//! solana-account-info 3.1.1: `lamports`, `data_len`, `try_borrow_data`,
//! `try_borrow_mut_data` and derived `Clone`, over input regions deserialized
//! by `deserialize` in solana-program-entrypoint 3.1.1 (`AccountInfo::new` per
//! account, `AccountInfo::clone` per duplicate).
//!
//! The state is the native projection documented in the suite README
//! ("AccountInfo 3.1.1"):
//!
//! - `cells`: the `RefCell`s, two per non-duplicate account (lamports, then
//!   data), identified by their `Rc` (duplicates share them). A cell gives its
//!   contents, read through a temporary borrow or through the live guard the
//!   driver holds, and its lease (free, shared, exclusive), probed with
//!   `RefCell::try_borrow_mut` and `try_borrow`, whose temporary guards restore
//!   the cell exactly;
//! - `rc`: the strong count of each cell `Rc`;
//! - `frame`: the region outside the lamports fields and the current data;
//! - `guards`: the live guard objects the driver holds, by identity (creation
//!   order), with the cell they denote, read from the pointer stored in the object;
//! - `ghost` (state before only): the guard-table length and generations.

use crate::region::{self, Entry, Region};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use solana_account_info::AccountInfo;
use std::cell::{Ref, RefCell, RefMut};
use std::rc::Rc;

pub const F_CLONE: &str = "<solana_account_info::AccountInfo<'a> as core::clone::Clone>::clone";
pub const F_DATA_LEN: &str = "solana_account_info::AccountInfo::<'a>::data_len";
pub const F_LAMPORTS: &str = "solana_account_info::AccountInfo::<'a>::lamports";
pub const F_TRY_BORROW_DATA: &str = "solana_account_info::AccountInfo::<'a>::try_borrow_data";
pub const F_TRY_BORROW_MUT_DATA: &str = "solana_account_info::AccountInfo::<'a>::try_borrow_mut_data";

#[derive(Clone, Debug)]
pub enum Setup {
    BorrowData(usize),
    BorrowMutData(usize),
    BorrowLamports(usize),
    BorrowMutLamports(usize),
    Drop(usize),
    /// Keep an extra clone of the AccountInfo at a position (raises both strong counts).
    Clone(usize),
}

#[derive(Clone, Debug)]
pub enum Call {
    Lamports(usize),
    DataLen(usize),
    TryBorrowData(usize),
    TryBorrowMutData(usize),
    Clone(usize),
}

/// The guard types as the getters return them: the shared ones borrow their
/// contents for the AccountInfo borrow `'b`, the exclusive ones for `'a`.
enum Obj<'b, 'a> {
    DataShared(Ref<'b, &'b mut [u8]>),
    DataExclusive(RefMut<'b, &'a mut [u8]>),
    LamportsShared(Ref<'b, &'b mut u64>),
    LamportsExclusive(RefMut<'b, &'a mut u64>),
}

struct World<'b, 'a> {
    region: &'b Region,
    infos: &'b [AccountInfo<'a>],
    slots: Vec<Option<Obj<'b, 'a>>>,
    kept: Vec<AccountInfo<'a>>,
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

    fn info_json(&self, info: &AccountInfo<'a>) -> Json {
        let owner = info.owner as *const _ as usize;
        let (owner_ref, field) = self.region.locate_header(owner).expect("owner reference into a header");
        assert_eq!(field, 40);
        #[allow(deprecated)]
        let unused = info._unused;
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

    fn args(&self, position: usize) -> Json {
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

    fn state(&self, ghost: bool) -> Json {
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
        // Everything outside the lamports fields and the current data: the
        // rest of the region, which these calls must leave unchanged.
        let projected: Vec<(usize, usize)> = self
            .region
            .cells
            .iter()
            .zip(&data_lens)
            .flat_map(|(c, len)| [(c.header + 72, 8), (c.header + region::HEADER, *len)])
            .collect();
        let frame = rec::bytes(&self.region.frame(&projected));
        let mut fields = vec![
            ("frame".to_string(), frame),
            ("cells".to_string(), Json::Arr(cells)),
            ("rc".to_string(), rc),
            ("guards".to_string(), Json::Arr(guards)),
        ];
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

    fn apply(&mut self, step: &Setup) {
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
        };
        self.slots.push(Some(obj));
    }
}

fn program_error(e: &solana_program_error::ProgramError) -> Json {
    format!("{e:?}").into()
}

pub fn record_case(c: &mut Corpus, id: &str, name: &str, entries: &[Entry], setup: &[Setup], call: &Call) {
    let region = Region::new(&region::input(entries.to_vec()));
    // SAFETY: the region is laid out as the loader serializes it and outlives the infos.
    let (_, infos, _) = unsafe { solana_program_entrypoint::deserialize(region.base()) };
    let infos: Vec<AccountInfo<'_>> = infos;
    let mut world = World { region: &region, infos: &infos, slots: Vec::new(), kept: Vec::new() };
    for step in setup {
        world.apply(step);
    }
    let before = world.state(true);
    let (function, args, outcome) = match call {
        Call::Lamports(p) | Call::DataLen(p) => {
            let lamports = matches!(call, Call::Lamports(_));
            let args = world.args(*p);
            let result = rec::catch(|| if lamports { infos[*p].lamports() as usize } else { infos[*p].data_len() });
            let outcome = match result {
                Ok(v) => rec::returned(v.into(), world.state(false)),
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            (if lamports { F_LAMPORTS } else { F_DATA_LEN }, args, outcome)
        }
        Call::TryBorrowData(p) | Call::TryBorrowMutData(p) => {
            let shared = matches!(call, Call::TryBorrowData(_));
            let args = world.args(*p);
            let result = rec::catch(|| {
                if shared {
                    infos[*p].try_borrow_data().map(Obj::DataShared)
                } else {
                    infos[*p].try_borrow_mut_data().map(Obj::DataExclusive)
                }
            });
            let outcome = match result {
                Ok(Ok(obj)) => {
                    world.slots.push(Some(obj));
                    let id = world.slots.len() - 1;
                    rec::returned(rec::ok(Json::obj([("guard", id.into())])), world.state(false))
                }
                Ok(Err(e)) => rec::returned(rec::err(program_error(&e)), world.state(false)),
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            (if shared { F_TRY_BORROW_DATA } else { F_TRY_BORROW_MUT_DATA }, args, outcome)
        }
        Call::Clone(p) => {
            let args = world.args(*p);
            let result = rec::catch(|| infos[*p].clone());
            let outcome = match result {
                Ok(clone) => {
                    // The clone is alive while the state after is read.
                    let state = world.state(false);
                    let value = world.info_json(&clone);
                    drop(clone);
                    rec::returned(value, state)
                }
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            (F_CLONE, args, outcome)
        }
    };
    c.push(Record {
        id: format!("{name}/{id}"),
        function,
        generics: vec![],
        layout: None,
        state: before,
        args,
        outcome,
        observed: None,
    });
    drop(world);
}

fn acct(seed: u8, lamports: u64, len: usize, signer: bool, writable: bool, executable: bool) -> region::Account {
    let mut a = region::account(seed, lamports, len);
    a.is_signer = signer;
    a.is_writable = writable;
    a.executable = executable;
    a
}

/// Case selection (the README rule): per member, every outcome class (value,
/// borrow panic, guard, borrow error) once or twice, on distinct accounts,
/// aliases and the independent other cell, at most about ten.
pub fn record(c: &mut Corpus) {
    use Entry::{Account as A, Duplicate as Dup};
    let one = vec![A(acct(1, 1_000, 16, false, true, false))];
    let empty = vec![A(acct(2, 0, 0, true, false, true))];
    let dups = vec![
        A(acct(3, 5_000, 8, true, true, false)),
        A(acct(4, u64::MAX, 3, false, false, false)),
        Dup(0),
        A(acct(5, 1, 5, true, false, true)),
        Dup(1),
    ];
    use Setup::*;
    let scenarios: Vec<(&str, &Vec<Entry>, Vec<Setup>)> = vec![
        ("one/free", &one, vec![]),
        ("one/data-shared", &one, vec![BorrowData(0)]),
        ("one/data-shared2", &one, vec![BorrowData(0), BorrowData(0)]),
        ("one/data-exclusive", &one, vec![BorrowMutData(0)]),
        ("one/lamports-shared", &one, vec![BorrowLamports(0)]),
        ("one/lamports-exclusive", &one, vec![BorrowMutLamports(0)]),
        ("one/both-exclusive", &one, vec![BorrowMutLamports(0), BorrowMutData(0)]),
        ("one/released", &one, vec![BorrowMutData(0), Drop(0)]),
        ("one/released-shared", &one, vec![BorrowData(0), BorrowData(0), Drop(1)]),
        ("one/cloned", &one, vec![Clone(0)]),
        ("empty/free", &empty, vec![]),
        ("dups/free", &dups, vec![]),
        ("dups/alias-data-exclusive", &dups, vec![BorrowMutData(2)]),
        ("dups/alias-data-shared", &dups, vec![BorrowData(4), BorrowData(1)]),
        ("dups/alias-lamports-exclusive", &dups, vec![BorrowMutLamports(0)]),
        ("dups/other-exclusive", &dups, vec![BorrowMutData(3), BorrowMutLamports(1)]),
    ];
    let mut case = |name: &str, p: usize, tag: &str, call: Call| {
        let (_, entries, setup) = scenarios.iter().find(|(n, _, _)| *n == name).unwrap();
        record_case(c, &format!("{tag}/p{p}"), name, entries, setup, &call);
    };
    for (name, p) in [
        ("one/free", 0),
        ("dups/free", 1),
        ("dups/free", 2),
        ("one/lamports-shared", 0),
        ("one/data-exclusive", 0),
        ("one/lamports-exclusive", 0),
        ("one/both-exclusive", 0),
        ("dups/alias-lamports-exclusive", 2),
    ] {
        case(name, p, "lamports", Call::Lamports(p));
    }
    for (name, p) in [
        ("one/free", 0),
        ("empty/free", 0),
        ("dups/free", 3),
        ("dups/free", 4),
        ("one/data-shared", 0),
        ("one/lamports-exclusive", 0),
        ("one/data-exclusive", 0),
        ("dups/alias-data-exclusive", 0),
    ] {
        case(name, p, "data_len", Call::DataLen(p));
    }
    for (name, p) in [
        ("one/free", 0),
        ("one/data-shared2", 0),
        ("one/released", 0),
        ("one/released-shared", 0),
        ("one/lamports-exclusive", 0),
        ("empty/free", 0),
        ("dups/alias-data-shared", 1),
        ("one/data-exclusive", 0),
        ("one/both-exclusive", 0),
        ("dups/alias-data-exclusive", 0),
    ] {
        case(name, p, "try_borrow_data", Call::TryBorrowData(p));
    }
    for (name, p) in [
        ("one/free", 0),
        ("one/released", 0),
        ("one/lamports-exclusive", 0),
        ("empty/free", 0),
        ("dups/other-exclusive", 0),
        ("one/data-shared", 0),
        ("one/released-shared", 0),
        ("one/data-exclusive", 0),
        ("dups/alias-data-shared", 4),
        ("dups/other-exclusive", 3),
    ] {
        case(name, p, "try_borrow_mut_data", Call::TryBorrowMutData(p));
    }
    for (name, p) in [
        ("one/free", 0),
        ("one/cloned", 0),
        ("empty/free", 0),
        ("dups/free", 0),
        ("dups/free", 2),
        ("dups/free", 4),
        ("one/both-exclusive", 0),
    ] {
        case(name, p, "clone", Call::Clone(p));
    }
}
