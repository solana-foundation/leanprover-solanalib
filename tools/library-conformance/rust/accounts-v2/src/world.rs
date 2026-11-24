//! The world for a case: one loader input region, the `AccountView`s of its
//! instruction accounts, the guards the driver holds and the ghost owner
//! epochs. `state()` is the record state (see the family
//! `Projection.lean` for what it denotes).

use conformance_accounts::{Entry, Input, Region, ACCOUNT_HEADER};
use conformance_recorder::{self as rec, Json};
use solana_account_view::{AccountView, Ref, RefMut, RuntimeAccount};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    Shared,
    Exclusive,
}

impl Mode {
    fn name(self) -> &'static str {
        match self {
            Mode::Shared => "shared",
            Mode::Exclusive => "exclusive",
        }
    }
}

/// A guard the driver holds, by ghost identity (its index in `World::guards`).
pub enum Held {
    /// Dropped: a tombstone.
    Dropped,
    SharedBytes(Ref<'static, [u8]>),
    SharedByte(Ref<'static, u8>),
    ExclusiveBytes(RefMut<'static, [u8]>),
    ExclusiveByte(RefMut<'static, u8>),
    /// Moved into a `try_map` whose closure unwound: the guard is gone but its
    /// lease is not released (`ManuallyDrop`). Cell, mode and target describe
    /// the guard before the call.
    Leaked { cell: usize, mode: Mode, offset: usize, length: usize },
    /// Taken out for a consuming call; never visible in a state.
    Moving,
}

pub struct Guard {
    pub held: Held,
    pub generation: u64,
}

/// Value address, referent length and state address of a guard, from its
/// derived `Debug` (`Ref { value: Pointer { addr, metadata }, state, .. }` for
/// slices, `Ref { value: 0x.., state: 0x.., .. }` for sized targets).
fn guard_fields(debug: &str, sized_len: Option<usize>) -> (usize, usize, usize) {
    fn hex_after(s: &str, key: &str) -> usize {
        let start = s.find(key).unwrap_or_else(|| panic!("no {key} in {s}")) + key.len();
        let rest = &s[start..];
        let rest = rest.strip_prefix("0x").unwrap_or_else(|| panic!("no address after {key} in {s}"));
        let end = rest.find(|c: char| !c.is_ascii_hexdigit()).unwrap_or(rest.len());
        usize::from_str_radix(&rest[..end], 16).unwrap()
    }
    fn dec_after(s: &str, key: &str) -> usize {
        let start = s.find(key).unwrap_or_else(|| panic!("no {key} in {s}")) + key.len();
        let rest = &s[start..];
        let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
        rest[..end].parse().unwrap()
    }
    let state = hex_after(debug, "state: ");
    match sized_len {
        Some(len) => (hex_after(debug, "value: "), len, state),
        None => (hex_after(debug, "addr: "), dec_after(debug, "metadata: "), state),
    }
}

pub struct World {
    pub input: Input,
    region: &'static mut Region,
    base: *mut u8,
    /// Entry index of each cell (non-duplicate entry).
    cells: Vec<usize>,
    /// Cell of each entry (duplicates: the cell of their first occurrence).
    entry_cell: Vec<usize>,
    /// Serialized data length of each cell.
    entry_len: Vec<usize>,
    pub guards: Vec<Guard>,
    /// Ghost: successful `close` calls per cell.
    pub epochs: Vec<u64>,
}

impl World {
    pub fn new(input: Input) -> World {
        let region: &'static mut Region = Box::leak(Box::new(input.serialize()));
        let base = region.as_mut_ptr();
        let mut cells = Vec::new();
        let mut entry_cell = Vec::new();
        let mut entry_len = Vec::new();
        for (i, entry) in input.entries.iter().enumerate() {
            match entry {
                Entry::Account(a) => {
                    entry_cell.push(cells.len());
                    cells.push(i);
                    entry_len.push(a.data.len());
                }
                Entry::Duplicate(j) => entry_cell.push(entry_cell[*j as usize]),
            }
        }
        let epochs = vec![0; cells.len()];
        World { input, region, base, cells, entry_cell, entry_len, guards: Vec::new(), epochs }
    }

    pub fn cell_of(&self, entry: usize) -> usize {
        self.entry_cell[entry]
    }

    fn cell_ptr(&self, cell: usize) -> *mut RuntimeAccount {
        unsafe { self.base.add(self.region.account_offset(self.cells[cell])) as *mut RuntimeAccount }
    }

    fn data_addr(&self, cell: usize) -> usize {
        self.cell_ptr(cell) as usize + ACCOUNT_HEADER
    }

    /// The `RuntimeAccount` referenced by an instruction-account view: its first
    /// occurrence, as the entrypoint maps duplicates.
    pub fn account_ptr(&self, entry: usize) -> *mut RuntimeAccount {
        self.cell_ptr(self.entry_cell[entry])
    }

    /// A fresh `AccountView` of instruction account `entry`, leaked so that
    /// guards borrowed from it live as long as the region.
    pub fn view(&self, entry: usize) -> &'static mut AccountView {
        let view = Box::leak(Box::new(unsafe { AccountView::new_unchecked(self.account_ptr(entry)) }));
        assert_eq!(view.account_ptr(), self.account_ptr(entry) as *const RuntimeAccount);
        view
    }

    /// The cell whose `RuntimeAccount` starts at `addr`.
    fn cell_at(&self, addr: usize) -> usize {
        (0..self.cells.len())
            .find(|&c| self.cell_ptr(c) as usize == addr)
            .unwrap_or_else(|| panic!("no account at {addr:#x}"))
    }

    /// `(cell, offset)` of an address inside the data area of a cell (serialized
    /// length plus the 10 KiB realloc reserve), or `None`.
    pub fn locate(&self, addr: usize) -> Option<(usize, usize)> {
        (0..self.cells.len()).find_map(|c| {
            let start = self.data_addr(c);
            let end = start + self.entry_len[c] + conformance_accounts::MAX_PERMITTED_DATA_INCREASE;
            (start <= addr && addr <= end).then(|| (c, addr - start))
        })
    }

    /// The cell whose address field `addr` addresses, or `None`.
    pub fn address_cell(&self, addr: usize) -> Option<usize> {
        (0..self.cells.len()).find(|&c| self.cell_ptr(c) as usize + 8 == addr)
    }

    /// `(cell, mode, offset, length)` of a held guard, read from the guard object.
    pub fn observe(&self, held: &Held) -> Option<(usize, Mode, usize, usize)> {
        let (fields, mode) = match held {
            Held::Dropped => return None,
            Held::Moving => panic!("a guard in a consuming call has no state"),
            Held::Leaked { cell, mode, offset, length } => return Some((*cell, *mode, *offset, *length)),
            Held::SharedBytes(r) => (guard_fields(&format!("{r:?}"), None), Mode::Shared),
            Held::SharedByte(r) => (guard_fields(&format!("{r:?}"), Some(1)), Mode::Shared),
            Held::ExclusiveBytes(r) => (guard_fields(&format!("{r:?}"), None), Mode::Exclusive),
            Held::ExclusiveByte(r) => (guard_fields(&format!("{r:?}"), Some(1)), Mode::Exclusive),
        };
        let (value, length, state) = fields;
        let cell = self.cell_at(state);
        let offset = value
            .checked_sub(self.data_addr(cell))
            .unwrap_or_else(|| panic!("guard target {value:#x} precedes its account's data"));
        Some((cell, mode, offset, length))
    }

    /// The bytes a held guard denotes, read through its `value` pointer.
    pub fn target_bytes(&self, k: usize) -> Vec<u8> {
        let (cell, _, offset, length) = self.observe(&self.guards[k].held).unwrap();
        let start = (self.data_addr(cell) + offset) as *const u8;
        unsafe { core::slice::from_raw_parts(start, length).to_vec() }
    }

    fn backing(&self, cell: usize) -> Vec<u8> {
        let start = self.data_addr(cell) as *const u8;
        unsafe { core::slice::from_raw_parts(start, self.entry_len[cell]).to_vec() }
    }

    pub fn push(&mut self, held: Held) -> usize {
        self.guards.push(Guard { held, generation: 0 });
        self.guards.len() - 1
    }

    pub fn take(&mut self, k: usize) -> Held {
        core::mem::replace(&mut self.guards[k].held, Held::Moving)
    }

    pub fn token(&self, k: usize) -> Json {
        Json::Arr(vec![Json::from(k), Json::from(self.guards[k].generation)])
    }

    /// The record state.
    pub fn state(&self) -> Json {
        let guards = Json::arr(self.guards.iter(), |g| match self.observe(&g.held) {
            None => Json::Null,
            Some((cell, mode, offset, length)) => Json::Arr(vec![
                Json::from(cell),
                Json::from(mode.name()),
                Json::from(g.generation),
                Json::from(offset),
                Json::from(length),
            ]),
        });
        Json::obj([
            ("input", self.region.read_back()),
            ("backing", Json::arr(0..self.cells.len(), |c| rec::bytes(&self.backing(c)))),
            ("guards", guards),
            ("owner_epochs", Json::arr(self.epochs.iter(), |e| Json::from(*e))),
        ])
    }
}
