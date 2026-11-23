//! AccountInfo worlds: a loader input region (`conformance-accounts`)
//! deserialized by the entrypoint of the pinned Anchor release, as an Anchor program
//! entrypoint does. The `k`-th distinct account has lamports cell `2k`, data
//! cell `2k + 1` and owner reference `k`; identities of returned AccountInfos
//! are read from their `Rc` and owner addresses.

use std::rc::Rc;

use anchor_lang::prelude::{AccountInfo, Pubkey};
use conformance_accounts::{Account, Entry, Input, Region};
use conformance_recorder::{self as rec, Json};

pub fn pk(n: u8) -> [u8; 32] {
    [n; 32]
}

pub fn account(key: [u8; 32], owner: [u8; 32], lamports: u64, data: Vec<u8>, signer: bool, writable: bool) -> Entry {
    Entry::Account(Account { key, owner, lamports, data, is_signer: signer, is_writable: writable, executable: false, rent_epoch: u64::MAX })
}

pub fn input(entries: Vec<Entry>) -> Input {
    Input { entries, instruction_data: vec![], program_id: pk(0xaa) }
}

/// A borrow the case holds across the call (kept alive, never read).
#[allow(dead_code)]
pub enum Held<'a> {
    Shared(std::cell::Ref<'a, &'static mut [u8]>),
    Exclusive(std::cell::RefMut<'a, &'static mut [u8]>),
    SharedLamports(std::cell::Ref<'a, &'static mut u64>),
    ExclusiveLamports(std::cell::RefMut<'a, &'static mut u64>),
}

pub struct World {
    pub region: &'static mut Region,
    pub infos: &'static [AccountInfo<'static>],
    /// Index in `infos` of each distinct account.
    pub distinct: Vec<usize>,
}

impl World {
    /// Serialize and deserialize `input` (call inside the child process for the case).
    pub fn new(input: &Input) -> World {
        let region: &'static mut Region = Box::leak(Box::new(input.serialize()));
        let (_, infos, _) = unsafe { anchor_lang::solana_program::entrypoint::deserialize(region.as_mut_ptr()) };
        let infos: &'static [AccountInfo<'static>] = Box::leak(infos.into_boxed_slice());
        let mut distinct: Vec<usize> = vec![];
        for (i, info) in infos.iter().enumerate() {
            if !distinct.iter().any(|&d| same(&infos[d].lamports, &info.lamports)) {
                distinct.push(i);
            }
        }
        World { region, infos, distinct }
    }

    pub fn info(&self, i: usize) -> &'static AccountInfo<'static> {
        &self.infos[i]
    }

    /// The distinct-account number of an AccountInfo (by its lamports `Rc`).
    pub fn number(&self, info: &AccountInfo) -> usize {
        self.distinct.iter().position(|&d| same(&self.infos[d].lamports, &info.lamports)).expect("unknown AccountInfo")
    }

    pub fn cell_of_data(&self, info: &AccountInfo) -> usize {
        let k = self.distinct.iter().position(|&d| same(&self.infos[d].data, &info.data)).expect("unknown data cell");
        2 * k + 1
    }

    pub fn cell_of_lamports(&self, info: &AccountInfo) -> usize {
        2 * self.number(info)
    }

    /// The owner reference: the distinct account whose owner storage it points to.
    pub fn owner_ref(&self, owner: &Pubkey) -> usize {
        self.distinct.iter().position(|&d| std::ptr::eq(self.infos[d].owner as *const Pubkey, owner as *const Pubkey)).expect("unknown owner storage")
    }

    #[allow(deprecated)]
    pub fn info_json(&self, info: &AccountInfo) -> Json {
        Json::obj([
            ("key", rec::bytes(info.key.as_ref())),
            ("lamports", self.cell_of_lamports(info).into()),
            ("data", self.cell_of_data(info).into()),
            ("owner", rec::bytes(info.owner.as_ref())),
            ("rent_epoch", unused(info).into()),
            ("is_signer", info.is_signer.into()),
            ("is_writable", info.is_writable.into()),
            ("executable", info.executable.into()),
            ("owner_ref", self.owner_ref(info.owner).into()),
        ])
    }

    /// The lease of each cell, probed through its `RefCell`.
    pub fn leases(&self) -> Json {
        let mut out = vec![];
        for &d in &self.distinct {
            let info = &self.infos[d];
            out.push(lease(info.lamports.try_borrow_mut().is_ok(), info.lamports.try_borrow().is_ok()));
            out.push(lease(info.data.try_borrow_mut().is_ok(), info.data.try_borrow().is_ok()));
        }
        Json::Arr(out)
    }

    /// `{"input": region read back, "leases": [...], "syscalls": ...}` plus `extra`.
    pub fn state(&self, extra: Vec<(&str, Json)>) -> Json {
        let mut fields = vec![("input".to_string(), self.region.read_back()), ("leases".to_string(), self.leases())];
        if !extra.iter().any(|(k, _)| *k == "syscalls") {
            fields.push(("syscalls".to_string(), conformance_shim::state()));
        }
        fields.extend(extra.into_iter().map(|(k, v)| (k.to_string(), v)));
        Json::Obj(fields)
    }
}

/// Identity of an `Rc` (the address of its allocation).
fn same<A: ?Sized, B: ?Sized>(a: &Rc<A>, b: &Rc<B>) -> bool {
    Rc::as_ptr(a) as *const u8 == Rc::as_ptr(b) as *const u8
}

fn lease(free: bool, shared_ok: bool) -> Json {
    if free {
        "free".into()
    } else if shared_ok {
        "shared".into()
    } else {
        "exclusive".into()
    }
}

/// `{"input": ..., "borrows": [...]}` plus `extra`, before the call.
pub fn state_before(input: &Input, borrows: &[(usize, &str)], extra: Vec<(&str, Json)>) -> Json {
    let mut fields = vec![
        ("input".to_string(), input.to_json()),
        ("borrows".to_string(), Json::arr(borrows.iter(), |(c, m)| Json::obj([("cell", (*c).into()), ("mode", (*m).into())]))),
    ];
    fields.extend(extra.into_iter().map(|(k, v)| (k.to_string(), v)));
    Json::Obj(fields)
}

/// Acquire the borrows a case holds across the call (cell numbering as above).
pub fn hold<'a>(world: &'a World, borrows: &[(usize, &str)]) -> Vec<Held<'a>> {
    borrows
        .iter()
        .map(|(cell, mode)| {
            let info = &world.infos[world.distinct[cell / 2]];
            match (cell % 2, *mode) {
                (1, "shared") => Held::Shared(info.data.borrow()),
                (1, "exclusive") => Held::Exclusive(info.data.borrow_mut()),
                (0, "shared") => Held::SharedLamports(info.lamports.borrow()),
                (0, "exclusive") => Held::ExclusiveLamports(info.lamports.borrow_mut()),
                _ => unreachable!(),
            }
        })
        .collect()
}

#[allow(deprecated)]
fn unused(info: &AccountInfo) -> u64 {
    #[cfg(feature = "account-info-2")]
    { info.rent_epoch }
    #[cfg(not(feature = "account-info-2"))]
    { info._unused }
}
