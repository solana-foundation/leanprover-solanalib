//! anchor-lang account wrappers over loader-deserialized AccountInfos:
//! `Account`/`InterfaceAccount`/`AccountLoader::try_from` (scripted traits),
//! `load`/`load_mut`, the key and dereference projections and
//! `ToAccountInfo::to_account_info`.

use std::cell::RefCell;
use std::rc::Rc;

use anchor_lang::prelude::*;
use anchor_lang::solana_program::program_error::ProgramError;
use conformance_accounts::{Entry, Input};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim as shim;

use crate::enc;
use crate::script::{self, check_ok, decode_ok, owner_returns, CheckStep, DecodeStep, OwnerStep, Scripted, Zc, Zc16};
use crate::world::{self, account, input, pk, World};

pub const PROGRAM: [u8; 32] = [0x77; 32];
const OTHER: [u8; 32] = [0x55; 32];
const SYSTEM: [u8; 32] = [0; 32];

fn push(c: &mut Corpus, id: String, function: &'static str, generics: Vec<(&'static str, String)>, state: Json, args: Json, outcome: Json) {
    c.push(Record { id, function, generics, layout: None, state, args, outcome, observed: None });
}

fn no_syscalls() -> (&'static str, Json) {
    ("syscalls", shim::Script::new(vec![]).state_before())
}

fn result_json<T>(r: &anchor_lang::Result<T>, ok: impl Fn(&T) -> Json) -> Json {
    match r {
        Ok(v) => rec::ok(ok(v)),
        Err(e) => rec::err(enc::error_value(e)),
    }
}

/// Run `call` on a fresh world in the child process for the case; it returns the result JSON.
/// The state after is the region, the leases (while held borrows and returned
/// guards are still alive) and `extra`.
fn run_case(
    inp: &Input,
    borrows: &[(usize, &'static str)],
    call: impl FnOnce(&'static World) -> (std::result::Result<Json, String>, Vec<(&'static str, Json)>),
) -> Json {
    let inp = inp.clone();
    let borrows = borrows.to_vec();
    shim::case(&shim::Script::new(vec![]), move || {
        let w: &'static World = Box::leak(Box::new(World::new(&inp)));
        let held = world::hold(w, &borrows);
        let (r, extra) = call(w);
        let state = w.state(extra);
        drop(held);
        match r {
            Ok(result) => rec::returned(result, state),
            Err(reason) => rec::unwound(reason, state),
        }
    })
}

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

struct Ctor {
    label: &'static str,
    entries: Vec<Entry>,
    target: usize,
    borrows: Vec<(usize, &'static str)>,
    script: script::Script,
}

fn data(n: usize) -> Vec<u8> {
    (0..n).map(|i| (i * 7 + 3) as u8).collect()
}

fn loader_data(extra: usize) -> Vec<u8> {
    let mut d = script::DISCRIMINATOR.to_vec();
    d.extend((0..extra).map(|i| (0x40 + i) as u8));
    d
}

fn sc(owner: Vec<OwnerStep>, check: Vec<CheckStep>, decode: Vec<DecodeStep>) -> script::Script {
    script::Script { owner, check, decode }
}

fn acc(owner: [u8; 32], lamports: u64, d: Vec<u8>) -> Vec<Entry> {
    vec![account(pk(1), owner, lamports, d, false, true)]
}

fn account_cases() -> Vec<Ctor> {
    let ok = || sc(vec![owner_returns(PROGRAM)], vec![], vec![decode_ok(7)]);
    vec![
        Ctor { label: "ok", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![], script: ok() },
        Ctor { label: "empty_data", entries: acc(PROGRAM, 1000, vec![]), target: 0, borrows: vec![], script: ok() },
        Ctor { label: "system_zero_lamports", entries: acc(SYSTEM, 0, data(4)), target: 0, borrows: vec![], script: ok() },
        Ctor { label: "system_nonzero", entries: acc(SYSTEM, 5, data(4)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(SYSTEM)], vec![], vec![decode_ok(9)]) },
        Ctor { label: "system_lamports_borrowed", entries: acc(SYSTEM, 5, data(4)), target: 0, borrows: vec![(0, "exclusive")], script: ok() },
        Ctor { label: "system_lamports_shared", entries: acc(SYSTEM, 0, data(4)), target: 0, borrows: vec![(0, "shared")], script: ok() },
        Ctor { label: "other_owner_lamports_borrowed", entries: acc(PROGRAM, 5, data(4)), target: 0, borrows: vec![(0, "exclusive")], script: ok() },
        Ctor { label: "wrong_owner", entries: acc(OTHER, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(PROGRAM), owner_returns(pk(0x66))], vec![], vec![]) },
        Ctor { label: "owner_assigns_match", entries: acc(OTHER, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![OwnerStep { returns: PROGRAM, assign: Some(PROGRAM), panic: false }], vec![], vec![decode_ok(1)]) },
        Ctor { label: "second_owner_assigns", entries: acc(OTHER, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(PROGRAM), OwnerStep { returns: pk(0x67), assign: Some(pk(0x68)), panic: false }], vec![], vec![]) },
        Ctor { label: "first_owner_panics", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![OwnerStep { returns: PROGRAM, assign: None, panic: true }], vec![], vec![]) },
        Ctor { label: "second_owner_panics", entries: acc(OTHER, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(PROGRAM), OwnerStep { returns: PROGRAM, assign: Some(pk(0x69)), panic: true }], vec![], vec![]) },
        Ctor { label: "data_borrowed", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![(1, "exclusive")], script: ok() },
        Ctor { label: "data_shared", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![(1, "shared")], script: ok() },
        Ctor { label: "decode_error", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(PROGRAM)], vec![], vec![DecodeStep { result: Err(ProgramError::InvalidAccountData), assign: None, lamports: None, panic: false }]) },
        Ctor { label: "decode_panics", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(PROGRAM)], vec![], vec![DecodeStep { result: Ok(1), assign: None, lamports: None, panic: true }]) },
        Ctor { label: "decode_effects", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(PROGRAM)], vec![], vec![DecodeStep { result: Ok(3), assign: Some(OTHER), lamports: Some(77), panic: false }]) },
        Ctor { label: "decode_effects_error", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(PROGRAM)], vec![], vec![DecodeStep { result: Err(ProgramError::Custom(5)), assign: Some(OTHER), lamports: Some(0), panic: false }]) },
        Ctor { label: "duplicate", entries: vec![account(pk(1), PROGRAM, 1000, data(12), false, true), account(pk(2), OTHER, 1, vec![], true, false), Entry::Duplicate(0)],
            target: 2, borrows: vec![], script: ok() },
        Ctor { label: "exhausted", entries: acc(OTHER, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(PROGRAM)], vec![], vec![]) },
    ]
}

fn interface_cases() -> Vec<Ctor> {
    let ok = || sc(vec![], vec![check_ok()], vec![decode_ok(7)]);
    let check = |err: Option<ProgramError>, assign: Option<[u8; 32]>, panic: bool| CheckStep { err, assign, panic };
    vec![
        Ctor { label: "ok", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![], script: ok() },
        Ctor { label: "system_zero_lamports", entries: acc(SYSTEM, 0, data(4)), target: 0, borrows: vec![], script: ok() },
        Ctor { label: "system_nonzero", entries: acc(SYSTEM, 1, data(4)), target: 0, borrows: vec![], script: ok() },
        Ctor { label: "system_lamports_borrowed", entries: acc(SYSTEM, 5, data(4)), target: 0, borrows: vec![(0, "exclusive")], script: ok() },
        Ctor { label: "check_error", entries: acc(OTHER, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![], vec![check(Some(ProgramError::IllegalOwner), None, false)], vec![]) },
        Ctor { label: "check_panics", entries: acc(OTHER, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![], vec![check(None, Some(PROGRAM), true)], vec![]) },
        Ctor { label: "check_assigns", entries: acc(OTHER, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![], vec![check(None, Some(PROGRAM), false)], vec![decode_ok(2)]) },
        Ctor { label: "data_borrowed", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![(1, "exclusive")], script: ok() },
        Ctor { label: "data_shared", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![(1, "shared")], script: ok() },
        Ctor { label: "decode_error", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![], vec![check_ok()], vec![DecodeStep { result: Err(ProgramError::InvalidAccountData), assign: None, lamports: None, panic: false }]) },
        Ctor { label: "decode_panics", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![], vec![check_ok()], vec![DecodeStep { result: Ok(1), assign: Some(OTHER), lamports: None, panic: true }]) },
        Ctor { label: "decode_assigns", entries: acc(PROGRAM, 1000, data(12)), target: 0, borrows: vec![],
            script: sc(vec![], vec![check_ok()], vec![DecodeStep { result: Ok(4), assign: Some(OTHER), lamports: Some(9), panic: false }]) },
        Ctor { label: "duplicate", entries: vec![account(pk(1), PROGRAM, 1000, data(12), false, true), Entry::Duplicate(0)],
            target: 1, borrows: vec![], script: ok() },
    ]
}

fn loader_cases() -> Vec<Ctor> {
    let ok = || sc(vec![owner_returns(PROGRAM)], vec![], vec![]);
    vec![
        Ctor { label: "ok", entries: acc(PROGRAM, 1000, loader_data(16)), target: 0, borrows: vec![], script: ok() },
        Ctor { label: "short_payload", entries: acc(PROGRAM, 1000, loader_data(3)), target: 0, borrows: vec![], script: ok() },
        Ctor { label: "system_zero_lamports", entries: acc(SYSTEM, 0, loader_data(16)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(SYSTEM)], vec![], vec![]) },
        Ctor { label: "wrong_owner", entries: acc(OTHER, 1000, loader_data(16)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(PROGRAM), owner_returns(pk(0x61))], vec![], vec![]) },
        Ctor { label: "owner_assigns_match", entries: acc(OTHER, 1000, loader_data(16)), target: 0, borrows: vec![],
            script: sc(vec![OwnerStep { returns: PROGRAM, assign: Some(PROGRAM), panic: false }], vec![], vec![]) },
        Ctor { label: "second_owner_panics", entries: acc(OTHER, 1000, loader_data(16)), target: 0, borrows: vec![],
            script: sc(vec![owner_returns(PROGRAM), OwnerStep { returns: PROGRAM, assign: None, panic: true }], vec![], vec![]) },
        Ctor { label: "no_discriminator", entries: acc(PROGRAM, 1000, vec![1, 2, 3]), target: 0, borrows: vec![], script: ok() },
        Ctor { label: "empty_data", entries: acc(PROGRAM, 1000, vec![]), target: 0, borrows: vec![], script: ok() },
        Ctor { label: "wrong_discriminator", entries: acc(PROGRAM, 1000, vec![1, 2, 3, 4, 5, 6, 7, 9, 0, 0]), target: 0, borrows: vec![], script: ok() },
        Ctor { label: "data_borrowed", entries: acc(PROGRAM, 1000, loader_data(16)), target: 0, borrows: vec![(1, "exclusive")], script: ok() },
        Ctor { label: "data_shared", entries: acc(PROGRAM, 1000, loader_data(16)), target: 0, borrows: vec![(1, "shared")], script: ok() },
        Ctor { label: "lamports_borrowed", entries: acc(PROGRAM, 1000, loader_data(16)), target: 0, borrows: vec![(0, "exclusive")], script: ok() },
        Ctor { label: "first_owner_panics", entries: acc(PROGRAM, 1000, loader_data(16)), target: 0, borrows: vec![],
            script: sc(vec![OwnerStep { returns: PROGRAM, assign: None, panic: true }], vec![], vec![]) },
    ]
}

const ACCOUNT_TRY_FROM: &str = "anchor_lang::accounts::account::Account::<'a, T>::try_from";
const INTERFACE_TRY_FROM: &str = "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::try_from";
const LOADER_TRY_FROM: &str = "anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::try_from";
pub const SCRIPTED: &str = "conformance_anchor::script::Scripted";
pub const ZC: &str = "conformance_anchor::script::Zc";
pub const ZC16: &str = "conformance_anchor::script::Zc16";

fn args_ctor(case: &Ctor) -> Json {
    Json::obj([("account", case.target.into()), ("script", case.script.json())])
}

fn record_constructors(c: &mut Corpus) {
    for case in account_cases() {
        let inp = input(case.entries.clone());
        let state = world::state_before(&inp, &case.borrows, vec![("log", Json::Arr(vec![])), no_syscalls()]);
        let (target, sc_) = (case.target, case.script.clone());
        let outcome = run_case(&inp, &case.borrows, move |w| {
            script::install(sc_, w, w.info(target));
            let r = rec::catch(|| Account::<Scripted>::try_from(w.info(target)));
            let r = r.map(|res| result_json(&res, |a| Json::obj([("value", (**a).0.into()), ("info", w.info_json(a.as_ref()))])));
            (r, vec![("log", script::log())])
        });
        push(c, format!("account_try_from/{}", case.label), ACCOUNT_TRY_FROM, vec![("T", SCRIPTED.to_string())], state, args_ctor(&case), outcome);
    }
    for case in interface_cases() {
        let inp = input(case.entries.clone());
        let state = world::state_before(&inp, &case.borrows, vec![("log", Json::Arr(vec![])), no_syscalls()]);
        let (target, sc_) = (case.target, case.script.clone());
        let outcome = run_case(&inp, &case.borrows, move |w| {
            script::install(sc_, w, w.info(target));
            let r = rec::catch(|| InterfaceAccount::<Scripted>::try_from(w.info(target)));
            let r = r.map(|res| result_json(&res, |a| Json::obj([("value", (**a).0.into()), ("info", w.info_json(a.as_ref()))])));
            (r, vec![("log", script::log())])
        });
        push(c, format!("interface_try_from/{}", case.label), INTERFACE_TRY_FROM, vec![("T", SCRIPTED.to_string())], state, args_ctor(&case), outcome);
    }
    for case in loader_cases() {
        let inp = input(case.entries.clone());
        let state = world::state_before(&inp, &case.borrows, vec![("log", Json::Arr(vec![])), no_syscalls()]);
        let (target, sc_) = (case.target, case.script.clone());
        let outcome = run_case(&inp, &case.borrows, move |w| {
            script::install(sc_, w, w.info(target));
            let r = rec::catch(|| AccountLoader::<Zc>::try_from(w.info(target)));
            let r = r.map(|res| result_json(&res, |l| Json::obj([("info", w.info_json(l.as_ref()))])));
            (r, vec![("log", script::log())])
        });
        push(c, format!("loader_try_from/{}", case.label), LOADER_TRY_FROM, vec![("T", ZC.to_string())], state, args_ctor(&case), outcome);
    }
}

// ---------------------------------------------------------------------------
// load / load_mut
// ---------------------------------------------------------------------------

const LOAD: &str = "anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::load";
const LOAD_MUT: &str = "anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::load_mut";

/// The mapped view of a returned guard: offset from the data start, length, bytes.
fn mapped<T>(w: &World, info: &AccountInfo, r: &T) -> Json {
    let _ = w;
    let base = info.data.as_ptr();
    let start = unsafe { (*base).as_ptr() } as usize;
    let addr = r as *const T as usize;
    let len = std::mem::size_of::<T>();
    let bytes = unsafe { std::slice::from_raw_parts(addr as *const u8, len) };
    Json::obj([("offset", (addr - start).into()), ("length", len.into()), ("bytes", rec::bytes(bytes))])
}

fn record_loads(c: &mut Corpus) {
    struct L { label: &'static str, writable: bool, d: Vec<u8>, borrows: Vec<(usize, &'static str)>, aligned16: bool }
    let cases = vec![
        L { label: "ok", writable: true, d: loader_data(16), borrows: vec![], aligned16: false },
        L { label: "ok_longer", writable: true, d: loader_data(40), borrows: vec![], aligned16: false },
        L { label: "readonly", writable: false, d: loader_data(16), borrows: vec![], aligned16: false },
        L { label: "data_borrowed", writable: true, d: loader_data(16), borrows: vec![(1, "exclusive")], aligned16: false },
        L { label: "data_shared", writable: true, d: loader_data(16), borrows: vec![(1, "shared")], aligned16: false },
        L { label: "no_discriminator", writable: true, d: vec![1, 2], borrows: vec![], aligned16: false },
        L { label: "wrong_discriminator", writable: true, d: vec![9, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], borrows: vec![], aligned16: false },
        L { label: "short_payload", writable: true, d: loader_data(15), borrows: vec![], aligned16: false },
        L { label: "discriminator_only", writable: true, d: loader_data(0), borrows: vec![], aligned16: false },
        L { label: "misaligned", writable: true, d: loader_data(32), borrows: vec![], aligned16: true },
        L { label: "misaligned_short", writable: true, d: loader_data(8), borrows: vec![], aligned16: true },
    ];
    for case in cases {
        for (mutable, function) in [(false, LOAD), (true, LOAD_MUT)] {
            let inp = input(vec![account(pk(1), PROGRAM, 500, case.d.clone(), false, case.writable)]);
            let state = world::state_before(&inp, &case.borrows, vec![no_syscalls()]);
            let aligned16 = case.aligned16;
            // The data address modulo 16 (the region is 16-aligned): the model
            // `dataAddress`, used only for the alignment check.
            let address = {
                let mut region = inp.serialize();
                let off = region.account_offset(0) + 8 + 32 + 32 + 8 + 8;
                (region.as_mut_ptr() as usize + off) % 16
            };
            let outcome = run_case(&inp, &case.borrows, move |w| {
                let info = w.info(0);
                assert_eq!(unsafe { (*info.data.as_ptr()).as_ptr() } as usize % 16, address);
                // The loader itself is built before the call (`AccountLoader::new` is private).
                script::install(script::Script { owner: vec![owner_returns(PROGRAM); 1], check: vec![], decode: vec![] }, w, info);
                fn go<T: anchor_lang::ZeroCopy + Owner>(w: &'static World, info: &'static AccountInfo<'static>, mutable: bool) -> std::result::Result<Json, String> {
                    let l: &'static AccountLoader<T> = Box::leak(Box::new(unsafe { loader_unchecked::<T>(info) }));
                    // A returned guard stays alive until the state after the call is read.
                    if mutable {
                        rec::catch(|| { let g = l.load_mut(); let j = result_json(&g, |g| mapped(w, info, &**g)); std::mem::forget(g); j })
                    } else {
                        rec::catch(|| { let g = l.load(); let j = result_json(&g, |g| mapped(w, info, &**g)); std::mem::forget(g); j })
                    }
                }
                let r = if aligned16 { go::<Zc16>(w, info, mutable) } else { go::<Zc>(w, info, mutable) };
                (r, vec![])
            });
            let generics = vec![("T", if case.aligned16 { ZC16 } else { ZC }.to_string())];
            push(c, format!("{}/{}", if mutable { "load_mut" } else { "load" }, case.label), function, generics, state,
                Json::obj([("account", 0.into()), ("data_address", address.into())]), outcome);
        }
    }
}

/// An `AccountLoader` for `info` without its checks: `try_from_unchecked`
/// checks only the owner, which the installed script answers.
unsafe fn loader_unchecked<T: anchor_lang::ZeroCopy + Owner>(info: &'static AccountInfo<'static>) -> AccountLoader<'static, T> {
    AccountLoader::<T>::try_from_unchecked(&Pubkey::new_from_array(PROGRAM), info).ok().expect("loader")
}

// ---------------------------------------------------------------------------
// Key and dereference projections
// ---------------------------------------------------------------------------

const INFO_KEY: &str = "anchor_lang::accounts::account_info::<impl anchor_lang::Key for solana_account_info::AccountInfo<'_>>::key";
const LOADER_KEY: &str = "<anchor_lang::accounts::account_loader::AccountLoader<'_, T> as anchor_lang::Key>::key";
const SIGNER_KEY: &str = "<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Key>::key";
const ACCOUNT_DEREF: &str = "<anchor_lang::accounts::account::Account<'_, T> as core::ops::deref::Deref>::deref";
const INTERFACE_ACCOUNT_DEREF: &str = "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as core::ops::deref::Deref>::deref";
const INTERFACE_DEREF: &str = "<anchor_lang::accounts::interface::Interface<'info, T> as core::ops::deref::Deref>::deref";
pub const SCRIPTED_ID: &str = "conformance_anchor::accounts::AnyProgram";

/// An `Interface` tag accepting every program id.
pub struct AnyProgram;

impl anchor_lang::CheckId for AnyProgram {
    fn check_id(_: &Pubkey) -> anchor_lang::Result<()> {
        Ok(())
    }
}

fn projection_worlds() -> Vec<(&'static str, Vec<Entry>, usize, Vec<(usize, &'static str)>)> {
    let mut exec = account(pk(9), pk(0x0b), 1, vec![0xde, 0xad], false, false);
    if let Entry::Account(a) = &mut exec {
        a.executable = true;
        a.rent_epoch = 17;
    }
    vec![
        ("plain", vec![account(pk(1), PROGRAM, 1000, loader_data(16), true, true)], 0, vec![]),
        ("second", vec![account(pk(2), OTHER, 0, vec![], false, false), account(pk(3), PROGRAM, 7, loader_data(16), true, false)], 1, vec![]),
        ("duplicate", vec![account(pk(4), PROGRAM, 5, loader_data(16), true, true), Entry::Duplicate(0)], 1, vec![]),
        ("borrowed", vec![account(pk(5), PROGRAM, 5, loader_data(16), true, true)], 0, vec![(1, "exclusive"), (0, "shared")]),
        ("executable", vec![exec.clone()], 0, vec![]),
        ("executable_duplicate", vec![account(pk(8), PROGRAM, 3, vec![], true, true), exec.clone(), Entry::Duplicate(1)], 2, vec![]),
        ("executable_borrowed", vec![exec], 0, vec![(1, "exclusive"), (0, "exclusive")]),
    ]
}

/// `{"region": read back, "leases": [...]}`: the ambient projection state.
fn region_state(w: &World) -> Json {
    Json::obj([("region", w.region.read_back()), ("leases", w.leases()), ("syscalls", shim::state())])
}

fn record_projections(c: &mut Corpus) {
    for (label, entries, target, borrows) in projection_worlds() {
        let inp = input(entries);
        let projections: Vec<(&str, &'static str, Vec<(&'static str, String)>)> = vec![
            ("info_key", INFO_KEY, vec![]),
            ("loader_key", LOADER_KEY, vec![("T", ZC.to_string())]),
            ("signer_key", SIGNER_KEY, vec![]),
            ("account_deref", ACCOUNT_DEREF, vec![("T", SCRIPTED.to_string())]),
            ("interface_account_deref", INTERFACE_ACCOUNT_DEREF, vec![("T", SCRIPTED.to_string())]),
            ("interface_deref", INTERFACE_DEREF, vec![("T", SCRIPTED_ID.to_string())]),
        ];
        for (name, function, generics) in projections {
            let borrows_ = borrows.clone();
            let inp_ = inp.clone();
            // The wrapper is built before the call; the ambient state is read
            // just before and just after the projection.
            let out = shim::case(&shim::Script::new(vec![]), move || {
                let w: &'static World = Box::leak(Box::new(World::new(&inp_)));
                let info = w.info(target);
                script::install(script::Script { owner: vec![owner_returns(*info.owner.as_array())], check: vec![check_ok()], decode: vec![decode_ok(41)] }, w, info);
                let held = world::hold(w, &[]);
                let (args, call): (Json, Box<dyn FnOnce() -> Json>) = match name {
                    "info_key" => (Json::obj([("account", target.into())]), Box::new(move || enc::key(&info.key()))),
                    "loader_key" => {
                        let l = unsafe { loader_unchecked::<Zc>(info) };
                        (Json::obj([("account", target.into())]), Box::new(move || enc::key(&l.key())))
                    }
                    "signer_key" => match Signer::try_from(info) {
                        Ok(s) => (Json::obj([("account", target.into())]), Box::new(move || enc::key(&s.key()))),
                        Err(_) => (Json::Null, Box::new(|| Json::Null)),
                    },
                    "account_deref" => {
                        let a = Account::<Scripted>::try_from_unchecked(info).ok().expect("account");
                        (Json::obj([("account", target.into()), ("value", 41.into())]), Box::new(move || (*a).0.into()))
                    }
                    "interface_account_deref" => {
                        let owner = *info.owner;
                        let a = InterfaceAccount::<Scripted>::try_from_unchecked(info).ok().expect("account");
                        (Json::obj([("account", target.into()), ("value", 41.into()), ("owner", enc::key(&owner))]), Box::new(move || (*a).0.into()))
                    }
                    "interface_deref" => match Interface::<AnyProgram>::try_from(info) {
                        Ok(i) => (Json::obj([("account", target.into())]), Box::new(move || w.info_json(&i))),
                        Err(_) => (Json::Null, Box::new(|| Json::Null)),
                    },
                    _ => unreachable!(),
                };
                drop(held);
                let held = world::hold(w, &borrows_);
                let before = region_state(w);
                let result = call();
                let after = region_state(w);
                drop(held);
                Json::obj([("args", args), ("before", before), ("outcome", rec::returned(result, after))])
            });
            let out = parse_raw(&out);
            let args = field(&out, "args");
            if args == Json::Null {
                continue; // the wrapper does not accept this account (not a signer / not executable)
            }
            let state = Json::obj([("input", inp.to_json()), ("before", field(&out, "before")), no_syscalls()]);
            push(c, format!("{name}/{label}"), function, generics, state, args, field(&out, "outcome"));
        }
    }
}

// ---------------------------------------------------------------------------
// ToAccountInfo::to_account_info
// ---------------------------------------------------------------------------

const TO_ACCOUNT_INFO: &str = "<T as anchor_lang::ToAccountInfo<'info>>::to_account_info";
pub const HOLDER: &str = "conformance_anchor::accounts::Holder";

thread_local! {
    static AS_REF_LOG: RefCell<Vec<Json>> = const { RefCell::new(Vec::new()) };
}

/// A scripted `AsRef<AccountInfo>`: logs, then panics or returns its account.
pub struct Holder {
    info: &'static AccountInfo<'static>,
    panics: bool,
}

impl AsRef<AccountInfo<'static>> for Holder {
    fn as_ref(&self) -> &AccountInfo<'static> {
        AS_REF_LOG.with(|l| l.borrow_mut().push("as_ref".into()));
        if self.panics {
            panic!("script as_ref");
        }
        self.info
    }
}

/// Strong counts of all cell `Rc` values, in cell order.
pub fn rc_counts(w: &World) -> Json {
    let mut out = vec![];
    for &d in &w.distinct {
        out.push(Rc::strong_count(&w.infos[d].lamports).into());
        out.push(Rc::strong_count(&w.infos[d].data).into());
    }
    Json::Arr(out)
}

fn record_to_account_info(c: &mut Corpus) {
    for (label, entries, target, _) in projection_worlds() {
        for panics in [false, true] {
            let inp = input(entries.clone());
            let inp_ = inp.clone();
            let out = shim::case(&shim::Script::new(vec![]), move || {
                let w: &'static World = Box::leak(Box::new(World::new(&inp_)));
                let holder = Holder { info: w.info(target), panics };
                let before = Json::obj([("counts", rc_counts(w)), ("log", Json::Arr(vec![]))]);
                let r = rec::catch(|| holder.to_account_info());
                let log = AS_REF_LOG.with(|l| Json::Arr(l.borrow().clone()));
                let after = w.state(vec![("counts", rc_counts(w)), ("log", log)]);
                let outcome = match r {
                    Ok(info) => {
                        let j = w.info_json(&info);
                        let o = rec::returned(j, after);
                        std::mem::forget(info);
                        o
                    }
                    Err(reason) => rec::unwound(reason, after),
                };
                Json::obj([("before", before), ("outcome", outcome)])
            });
            let out = parse_raw(&out);
            let mut state = vec![("input".to_string(), inp.to_json()), ("borrows".to_string(), Json::Arr(vec![]))];
            if let Json::Obj(fields) = field(&out, "before") {
                state.extend(fields);
            }
            state.push(("syscalls".to_string(), shim::Script::new(vec![]).state_before()));
            let args = Json::obj([("account", target.into()), ("panics", panics.into())]);
            push(c, format!("to_account_info/{label}/{}", if panics { "as_ref_panics" } else { "ok" }), TO_ACCOUNT_INFO,
                vec![("T", HOLDER.to_string())], Json::Obj(state), args, field(&out, "outcome"));
        }
    }
}

// ---------------------------------------------------------------------------

/// The JSON text from the child process, parsed back (a small reader for the recorder output).
pub fn parse_raw(j: &Json) -> Json {
    match j {
        Json::Raw(text) => crate::json::parse(text),
        other => other.clone(),
    }
}

pub fn field(j: &Json, k: &str) -> Json {
    match j {
        Json::Obj(fields) => fields.iter().find(|(key, _)| key == k).map(|(_, v)| v.clone()).unwrap_or(Json::Null),
        _ => Json::Null,
    }
}

pub fn record_all(c: &mut Corpus) {
    record_constructors(c);
    record_loads(c);
    record_projections(c);
    record_to_account_info(c);
}
