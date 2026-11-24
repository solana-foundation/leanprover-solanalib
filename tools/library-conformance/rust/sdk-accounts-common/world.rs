//! Shared native AccountInfo observation world. Guard observation and Rc identity
//! follow the existing AccountsV1 fixture; the projection additionally records
//! owner storage, serialized lengths and every backing byte for mutations.

use crate::region::{self, Region};
use conformance_recorder::{self as rec, Json};
use crate::{AccountInfo, ProgramError, sparse, resize, MEMSETS};
use std::cell::{Ref, RefCell, RefMut};
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum Setup {
    BorrowData(usize),
    BorrowMutData(usize),
    BorrowLamports(usize),
    BorrowMutLamports(usize),
    Drop(usize),
    /// Keep an extra clone of the AccountInfo at a position (raises both strong counts).
    Clone(usize),
    Resize(usize, usize, bool),
}

#[derive(Clone, Debug)]
pub enum Call {
    Lamports(usize), DataLen(usize), Empty(usize), TryLen(usize),
    Borrow(usize, bool, bool), Clone(usize), AsRef(usize), Assign(usize),
    Resize(usize, usize, bool, bool),
}

/// The guard types as the getters return them: the shared ones borrow their
/// contents for the AccountInfo borrow `'b`, the exclusive ones for `'a`.
pub(super) enum Obj<'b, 'a> {
    DataShared(Ref<'b, &'b mut [u8]>),
    DataExclusive(RefMut<'b, &'a mut [u8]>),
    LamportsShared(Ref<'b, &'b mut u64>),
    LamportsExclusive(RefMut<'b, &'a mut u64>),
}

pub(super) struct World<'b, 'a> {
    pub(super) region: &'b Region,
    pub(super) infos: &'b [AccountInfo<'a>],
    pub(super) slots: Vec<Option<Obj<'b, 'a>>>,
    pub(super) kept: Vec<AccountInfo<'a>>,
}

/// The cells of the region: (account position of the first occurrence, lamports or data).
fn cell_count(region: &Region) -> usize {
    2 * region.cells.len()
}

impl<'b, 'a> World<'b, 'a> {
    /// The first non-duplicate position whose AccountInfo holds this `Rc`.
    fn lamports_cell(&self, rc: &Rc<RefCell<&'a mut u64>>) -> usize {
        let first = self.originals().position(|i| Rc::ptr_eq(&i.lamports, rc)).expect("lamports Rc of the region");
        2 * first
    }

    fn data_cell(&self, rc: &Rc<RefCell<&'a mut [u8]>>) -> usize {
        let first = self.originals().position(|i| Rc::ptr_eq(&i.data, rc)).expect("data Rc of the region");
        2 * first + 1
    }

    /// The AccountInfos of the non-duplicate accounts, in order: cell `2k` and `2k + 1`.
    fn originals(&self) -> impl Iterator<Item = &AccountInfo<'a>> {
        let mut seen: Vec<*const RefCell<&'a mut u64>> = Vec::new();
        self.infos.iter().filter(move |i| {
            let p = Rc::as_ptr(&i.lamports);
            if seen.contains(&p) {
                false
            } else {
                seen.push(p);
                true
            }
        })
    }

    pub(super) fn info_json(&self, info: &AccountInfo<'a>) -> Json {
        let owner = info.owner as *const _ as usize;
        let (owner_ref, field) = self.region.locate_header(owner).expect("owner reference into a header");
        assert_eq!(field, 40);
        #[allow(deprecated)]
        #[cfg(feature = "unused-field")]
        let unused = info._unused;
        #[cfg(not(feature = "unused-field"))]
        let unused = info.rent_epoch;
        Json::obj([
            ("key", rec::bytes(info.key.as_ref())),
            ("lamports", self.lamports_cell(&info.lamports).into()),
            ("data", self.data_cell(&info.data).into()),
            ("owner", rec::bytes(info.owner.as_ref())),
            ("unused", unused.into()),
            ("is_signer", info.is_signer.into()),
            ("is_writable", info.is_writable.into()),
            ("executable", info.executable.into()),
            ("owner_ref", owner_ref.into()),
        ])
    }

    pub(super) fn args(&self, position: usize) -> Json {
        Json::obj([
            ("info", self.info_json(&self.infos[position])),
            (
                "profile",
                Json::obj([("word_bits", (usize::BITS as usize).into()), ("aborts", cfg!(panic = "abort").into())]),
            ),
        ])
    }

    /// (cell, mode) of a guard object, from the address it refers to.
    fn object_target(&self, obj: &Obj) -> (usize, &'static str) {
        let data_cell = |address: usize| {
            let (cell, offset) = self.region.locate_data(address).expect("data guard into a data area");
            assert_eq!(offset, 0);
            2 * cell + 1
        };
        let lamports_cell = |address: usize| {
            let (cell, field) = self.region.locate_header(address).expect("lamports guard into a header");
            assert_eq!(field, 72);
            2 * cell
        };
        match obj {
            Obj::DataShared(r) => (data_cell(r.as_ptr() as usize), "shared"),
            Obj::DataExclusive(r) => (data_cell(r.as_ptr() as usize), "exclusive"),
            Obj::LamportsShared(r) => (lamports_cell(&***r as *const u64 as usize), "shared"),
            Obj::LamportsExclusive(r) => (lamports_cell(&***r as *const u64 as usize), "exclusive"),
        }
    }

    fn lease<T>(cell: &RefCell<T>) -> &'static str {
        if cell.try_borrow_mut().is_ok() {
            "free"
        } else if cell.try_borrow().is_err() {
            "exclusive"
        } else {
            "shared"
        }
    }

    fn held_exclusive(&self, cell: usize) -> Option<&Obj<'b, 'a>> {
        self.slots.iter().flatten().find(|o| self.object_target(o) == (cell, "exclusive"))
    }

    pub(super) fn state(&self, ghost: bool) -> Json {
        let mut cells = Vec::new();
        let mut data_lens = Vec::new();
        for (k, info) in self.originals().enumerate() {
            let lamports = match info.lamports.try_borrow() {
                Ok(r) => **r,
                Err(_) => match self.held_exclusive(2 * k) {
                    Some(Obj::LamportsExclusive(r)) => ***r,
                    _ => panic!("lamports cell {} exclusively borrowed by no driver guard", 2 * k),
                },
            };
            let data = match info.data.try_borrow() {
                Ok(r) => r.to_vec(),
                Err(_) => match self.held_exclusive(2 * k + 1) {
                    Some(Obj::DataExclusive(r)) => r.to_vec(),
                    _ => panic!("data cell {} exclusively borrowed by no driver guard", 2 * k + 1),
                },
            };
            data_lens.push(data.len());
            cells.push(Json::obj([("lamports", lamports.into()), ("lease", Self::lease(&info.lamports).into())]));
            cells.push(Json::obj([("data", rec::bytes(&data)), ("lease", Self::lease(&info.data).into())]));
        }
        assert_eq!(cells.len(), cell_count(self.region));
        let rc = Json::Arr(
            self.originals()
                .flat_map(|i| [Rc::strong_count(&i.lamports), Rc::strong_count(&i.data)])
                .map(Json::from)
                .collect(),
        );
        let mut guards = Vec::new();
        for (id, slot) in self.slots.iter().enumerate() {
            if let Some(obj) = slot {
                let (cell, mode) = self.object_target(obj);
                guards.push(Json::obj([
                    ("id", id.into()),
                    ("cell", cell.into()),
                    ("mode", mode.into()),
                    ("view", "whole".into()),
                ]));
            }
        }
        // Frame bytes exclude every modeled mutable field and the complete
        // data backing, including hidden spare bytes. All other bytes stay fixed.
        let projected: Vec<(usize, usize)> = self
            .region
            .cells
            .iter()
            .zip(&data_lens)
            .flat_map(|(c, _)| [(c.header + 40, 32), (c.header + 72, 8), (c.header + 80, 8),
                (c.header + region::HEADER, c.entry_len + region::MAX_PERMITTED_DATA_INCREASE)])
            .collect();
        let frame = rec::bytes(&self.region.frame(&projected));
        let mut fields = vec![
            ("frame".to_string(), frame),
            ("cells".to_string(), Json::Arr(cells)),
            ("rc".to_string(), rc),
            ("guards".to_string(), Json::Arr(guards)),
        ];
        fields.push(("owners".to_owned(), Json::arr(self.originals(), |i| rec::bytes(i.owner.as_ref()))));
        fields.push(("infos".to_owned(), Json::arr(self.infos.iter(), |i| self.info_json(i))));
        fields.push(("buffers".to_owned(), Json::arr(self.region.cells.iter().zip(&data_lens), |(c, len)| {
            let original = u32::from_le_bytes(self.region.read(c.header + 4, 4).try_into().unwrap());
            let serialized = u64::from_le_bytes(self.region.read(c.header + 80, 8).try_into().unwrap());
            let spare = self.region.read(c.header + region::HEADER + len, c.entry_len + region::MAX_PERMITTED_DATA_INCREASE - len);
            Json::obj([("original_len", original.into()), ("serialized_len", serialized.into()), ("spare", sparse(&spare))])
        })));
        fields.push(("memsets".to_owned(), Json::arr(MEMSETS.lock().unwrap().iter(), |&(address, byte, n)| {
            let (cell, offset) = self.region.locate_data(address).expect("memset destination in data allocation");
            Json::obj([("cell", (2 * cell + 1).into()), ("offset", offset.into()), ("byte", byte.into()), ("length", n.into())])
        })));
        if ghost {
            fields.push((
                "ghost".to_string(),
                Json::obj([
                    ("slots", self.slots.len().into()),
                    ("generations", Json::arr(self.slots.iter(), |_| Json::from(0u64))),
                ]),
            ));
        }
        Json::Obj(fields)
    }

    pub(super) fn apply(&mut self, step: &Setup) {
        let infos = self.infos;
        let obj = match step {
            Setup::BorrowData(p) => Obj::DataShared(infos[*p].try_borrow_data().expect("setup borrow")),
            Setup::BorrowMutData(p) => Obj::DataExclusive(infos[*p].try_borrow_mut_data().expect("setup borrow")),
            Setup::BorrowLamports(p) => Obj::LamportsShared(infos[*p].try_borrow_lamports().expect("setup borrow")),
            Setup::BorrowMutLamports(p) => {
                Obj::LamportsExclusive(infos[*p].try_borrow_mut_lamports().expect("setup borrow"))
            }
            Setup::Drop(id) => {
                self.slots[*id].take().expect("setup drop of a live guard");
                return;
            }
            Setup::Clone(p) => {
                self.kept.push(infos[*p].clone());
                return;
            }
            Setup::Resize(p, len, zero) => {
                resize(&infos[*p], *len, *zero, false).expect("setup resize");
                return;
            }
        };
        self.slots.push(Some(obj));
    }
}

pub(super) fn program_error(e: &ProgramError) -> Json {
    format!("{e:?}").into()
}
