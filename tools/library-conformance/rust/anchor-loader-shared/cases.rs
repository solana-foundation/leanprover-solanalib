//! Loader lifecycle calls on real deserialized accounts, including aliases,
//! held borrows and effectful Owner callbacks. SDK sources are unmodified.

use std::collections::BTreeSet;
use std::rc::Rc;
use anchor_lang::prelude::*;
use conformance_accounts::{Entry, Input};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim as shim;
use crate::{enc, script, world};
use script::{Step, Zc, Zc16, DISC, PROGRAM};
use world::{World, account, input, pk};

const OTHER: [u8; 32] = [0x55; 32];
const ZC: &str = "conformance_anchor_loader::script::Zc";
const ZC16: &str = "conformance_anchor_loader::script::Zc16";
const UNCHECKED: &str = "anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::try_from_unchecked";
const ACCOUNTS: &str = "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as anchor_lang::Accounts<'info, B>>::try_accounts";
const AS_REF: &str = "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref";
const CLONE: &str = "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as core::clone::Clone>::clone";
const INIT: &str = "anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::load_init";
const EXIT: &str = "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as anchor_lang::AccountsExit<'info>>::exit";
const CLOSE: &str = "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as anchor_lang::AccountsClose<'info>>::close";

#[derive(Clone)]
struct Case {
    label: &'static str,
    entries: Vec<Entry>,
    target: usize,
    borrows: Vec<(usize, &'static str)>,
    script: Vec<Step>,
    program: [u8; 32],
}

fn base(label: &'static str, data: Vec<u8>) -> Case {
    Case { label, entries: vec![account(pk(1), PROGRAM, 40, data, false, true)],
        target: 0, borrows: vec![], script: vec![script::returns(PROGRAM)], program: PROGRAM }
}

fn bytes(n: usize) -> Vec<u8> { (0..n).map(|i| (i % 200 + 31) as u8).collect() }
fn checked_bytes(n: usize) -> Vec<u8> { let mut d = DISC.to_vec(); d.extend(bytes(n)); d }
fn init_bytes(n: usize) -> Vec<u8> { let mut d = vec![0; 8]; d.extend(bytes(n)); d }
fn modify(case: &mut Case, f: impl FnOnce(&mut conformance_accounts::Account)) {
    let Entry::Account(account) = &mut case.entries[0] else { unreachable!() };
    f(account);
}
fn record_id(w: &World, info: &AccountInfo) -> Json {
    w.infos.iter().position(|candidate| std::ptr::eq(candidate as *const _ as *const u8, info as *const _ as *const u8)).expect("actual record reference").into()
}
fn counts(w: &World) -> Json {
    Json::arr(&w.distinct, |&i| Json::Arr(vec![Rc::strong_count(&w.info(i).lamports).into(),
        Rc::strong_count(&w.info(i).data).into()]))
}
fn loader<T: anchor_lang::ZeroCopy + Owner>(w: &'static World, target: usize) -> &'static AccountLoader<'static, T> {
    let info = w.info(target);
    script::install(vec![script::returns(info.owner.to_bytes())], Some(info));
    Box::leak(Box::new(AccountLoader::<T>::try_from_unchecked(&Pubkey::new_from_array(PROGRAM), info).expect("prepare loader")))
}
fn push(c: &mut Corpus, case: &Case, method: &str, function: &'static str, ty: &str, state: Json, args: Json, outcome: Json) {
    let mut generics = vec![("T", ty.to_string())];
    if function == ACCOUNTS { generics.push(("B", "u64".to_string())); }
    c.push(Record { id: format!("{method}/{}", case.label), function,
        generics, layout: None, state, args, outcome, observed: None });
}
fn before(inp: &Input, case: &Case, extras: Vec<(&str, Json)>) -> Json {
    let mut fields = vec![("log", Json::Arr(vec![])), ("syscalls", shim::Script::new(vec![]).state_before())];
    fields.extend(extras);
    world::state_before(inp, &case.borrows, fields)
}
fn args(case: &Case) -> Json {
    Json::obj([("account", case.target.into()), ("program_id", rec::bytes(&case.program)),
        ("script", script::json(&case.script))])
}
fn outcome(result: std::result::Result<Json, String>, state: Json) -> Json {
    match result { Ok(value) => rec::returned(value, state), Err(reason) => rec::unwound(reason, state) }
}

fn constructor_cases() -> Vec<Case> {
    let mut cases = vec![base("ok", checked_bytes(16)), base("short_payload", checked_bytes(1)),
        base("empty_data", vec![]), base("short_prefix", vec![1, 2, 3]),
        base("wrong_discriminator", vec![9; 24])];
    let mut wrong = base("wrong_owner", checked_bytes(16));
    modify(&mut wrong, |a| a.owner = OTHER);
    wrong.script = vec![script::returns(PROGRAM), script::returns(pk(0x66))]; cases.push(wrong);
    let mut assigned = base("owner_assigns_match", checked_bytes(16));
    modify(&mut assigned, |a| a.owner = OTHER);
    assigned.script = vec![Step { returns: PROGRAM, assign: Some(PROGRAM), panic: false }]; cases.push(assigned);
    let mut first = base("first_owner_panics", checked_bytes(16));
    first.script = vec![Step { returns: PROGRAM, assign: Some(OTHER), panic: true }]; cases.push(first);
    let mut second = base("second_owner_panics", checked_bytes(16));
    modify(&mut second, |a| a.owner = OTHER);
    second.script = vec![script::returns(PROGRAM), Step { returns: PROGRAM, assign: Some(pk(0x68)), panic: true }];
    cases.push(second);
    for (name, mode) in [("data_shared", "shared"), ("data_exclusive", "exclusive")] {
        let mut held = base(name, checked_bytes(16)); held.borrows = vec![(1, mode)]; cases.push(held);
    }
    let mut readonly = base("readonly_program_ignored", vec![]);
    readonly.program = pk(0x33); modify(&mut readonly, |a| a.is_writable = false); cases.push(readonly);
    let mut dup = base("duplicate_record", checked_bytes(16));
    dup.entries.push(Entry::Duplicate(0)); dup.target = 1; cases.push(dup);
    cases
}

fn record_constructors(c: &mut Corpus) {
    for case in constructor_cases() {
        let inp = input(case.entries.clone());
        let state = before(&inp, &case, vec![]);
        let actual = case.clone(); let source = inp.clone();
        let result = shim::case(&shim::Script::new(vec![]), move || {
            let w = Box::leak(Box::new(World::new(&source)));
            let _held = world::hold(w, &actual.borrows);
            script::install(actual.script, Some(w.info(actual.target)));
            let result = rec::catch(|| {
                let result = AccountLoader::<Zc>::try_from_unchecked(&Pubkey::new_from_array(actual.program), w.info(actual.target));
                enc::result(&result, |loader| Json::obj([("record", record_id(w, loader.as_ref()))]))
            });
            outcome(result, w.state(vec![("log", script::log())]))
        });
        push(c, &case, "try_from_unchecked", UNCHECKED, ZC, state, args(&case), result);
    }
    let mut all = constructor_cases();
    let mut empty = base("empty_accounts", vec![]); empty.entries.clear(); empty.script.clear(); all.push(empty);
    for case in all {
        // The actual mutable slice begins at the selected record. Its tail,
        // bumps and realloc set are read after every normal/error/unwind exit.
        let inp = input(case.entries.clone());
        let indices: Vec<usize> = (case.target..case.entries.len()).collect();
        let mut extras = vec![("remaining", Json::arr(indices.iter(), |i| (*i).into())),
            ("bumps", 17u64.into()), ("reallocs", Json::Arr(vec![rec::bytes(&pk(0x31))]))];
        let state = before(&inp, &case, std::mem::take(&mut extras));
        let actual = case.clone(); let source = inp.clone();
        let result = shim::case(&shim::Script::new(vec![]), move || {
            let w = Box::leak(Box::new(World::new(&source)));
            let _held = world::hold(w, &actual.borrows);
            script::install(actual.script, w.infos.get(actual.target));
            let mut remaining = &w.infos[actual.target..];
            let mut bumps = 17u64;
            let mut reallocs = BTreeSet::from([Pubkey::new_from_array(pk(0x31))]);
            let result = rec::catch(|| {
                let result = AccountLoader::<Zc>::try_accounts(&Pubkey::new_from_array(actual.program),
                    &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs);
                enc::result(&result, |loader| Json::obj([("record", record_id(w, loader.as_ref()))]))
            });
            outcome(result, w.state(vec![("log", script::log()),
                ("remaining", Json::arr(remaining, |info| record_id(w, info))),
                ("bumps", bumps.into()), ("reallocs", Json::arr(&reallocs, |key| rec::bytes(key.as_ref())))]))
        });
        let mut arguments = match args(&case) { Json::Obj(fields) => fields, _ => unreachable!() };
        arguments.push(("instruction_data".to_string(), rec::bytes(&[0xab, 0xcd])));
        push(c, &case, "try_accounts", ACCOUNTS, ZC, state, Json::Obj(arguments), result);
    }
}

fn record_identities(c: &mut Corpus, clone_enabled: bool) {
    for duplicate in [false, true] {
        let mut case = base(if duplicate { "duplicate" } else { "original" }, vec![]);
        if duplicate { case.entries.push(Entry::Duplicate(0)); case.target = 1; }
        for cloning in [false, true] {
            if cloning && !clone_enabled { continue; }
            case.script.clear();
            let inp = input(case.entries.clone());
            let rc: usize = if duplicate { 2 } else { 1 };
            let state = before(&inp, &case, vec![("ref_counts", Json::Arr(vec![Json::Arr(vec![rc.into(), rc.into()])]))]);
            let actual = case.clone(); let source = inp.clone();
            let result = shim::case(&shim::Script::new(vec![]), move || {
                let w = Box::leak(Box::new(World::new(&source)));
                let loader = loader::<Zc>(w, actual.target);
                script::install(vec![], Some(w.info(actual.target)));
                let result = rec::catch(|| {
                    let record = if cloning {
                        let copied: AccountLoader<'static, Zc> = Clone::clone(loader); record_id(w, copied.as_ref())
                    } else { record_id(w, loader.as_ref()) };
                    Json::obj([("record", record)])
                });
                outcome(result, w.state(vec![("log", script::log()), ("ref_counts", counts(w))]))
            });
            push(c, &case, if cloning { "clone" } else { "as_ref" }, if cloning { CLONE } else { AS_REF },
                ZC, state, args(&case), result);
        }
    }
}

fn record_init(c: &mut Corpus) {
    let mut cases = vec![base("zero_prefix", init_bytes(16)), base("trailing_capacity", init_bytes(40)),
        base("short_prefix", vec![0; 3]), base("empty_data", vec![]),
        base("short_payload", init_bytes(15)), base("discriminator_only", vec![0; 8]),
        base("nonzero_prefix", checked_bytes(16))];
    let mut readonly = base("readonly_before_borrow", init_bytes(16));
    modify(&mut readonly, |a| a.is_writable = false); readonly.borrows.push((1, "exclusive")); cases.push(readonly);
    for (name, mode) in [("shared_conflict", "shared"), ("exclusive_conflict", "exclusive")] {
        let mut held = base(name, init_bytes(16)); held.borrows.push((1, mode)); cases.push(held);
    }
    let mut owner = base("owner_not_rechecked", init_bytes(16)); modify(&mut owner, |a| a.owner = OTHER); cases.push(owner);
    for case in cases {
        for aligned16 in [false, true] {
            if aligned16 && !matches!(case.label, "zero_prefix" | "short_payload") { continue; }
            let inp = input(case.entries.clone());
            let state = before(&inp, &case, vec![]);
            let actual = case.clone(); let source = inp.clone();
            let address = { let mut region = inp.serialize();
                let offset = region.account_offset(case.target) + 88;
                (region.as_mut_ptr() as usize + offset) % 16 };
            let result = shim::case(&shim::Script::new(vec![]), move || {
                let w = Box::leak(Box::new(World::new(&source)));
                fn go<T: anchor_lang::ZeroCopy + Owner>(w: &'static World, case: &Case, address: usize) -> Json {
                    let loader = loader::<T>(w, case.target);
                    script::install(vec![], Some(w.info(case.target)));
                    let _held = world::hold(w, &case.borrows);
                    let start = unsafe { (*w.info(case.target).data.as_ptr()).as_ptr() } as usize;
                    assert_eq!(start % 16, address);
                    let result = rec::catch(|| {
                        let guard = loader.load_init();
                        let value = enc::result(&guard, |guard| {
                            let p = &**guard as *const T as *const u8;
                            let size = std::mem::size_of::<T>();
                            Json::obj([("offset", (p as usize - start).into()), ("length", size.into()),
                                ("bytes", rec::bytes(unsafe { std::slice::from_raw_parts(p, size) }))])
                        });
                        std::mem::forget(guard); value
                    });
                    outcome(result, w.state(vec![("log", script::log())]))
                }
                if aligned16 { go::<Zc16>(w, &actual, address) } else { go::<Zc>(w, &actual, address) }
            });
            let mut arguments = match args(&case) { Json::Obj(fields) => fields, _ => unreachable!() };
            arguments.push(("data_address".to_string(), address.into()));
            push(c, &case, if aligned16 { "load_init_16" } else { "load_init" }, INIT,
                if aligned16 { ZC16 } else { ZC }, state, Json::Obj(arguments), result);
        }
    }
}

fn record_exit(c: &mut Corpus) {
    let mut cases = vec![base("write_discriminator", init_bytes(16)), base("short_write", vec![0; 3]),
        base("empty_write", vec![])];
    let mut readonly = base("readonly_is_not_checked", init_bytes(16)); modify(&mut readonly, |a| a.is_writable = false); cases.push(readonly);
    let mut wrong = base("owner_type_mismatch", init_bytes(16)); wrong.program = OTHER; cases.push(wrong);
    let mut closed = base("closed_account", vec![]); modify(&mut closed, |a| a.owner = [0; 32]); cases.push(closed);
    for (label, owner, mode) in [("borrow_error", PROGRAM, "shared"), ("borrow_exclusive", PROGRAM, "exclusive"),
        ("closed_check_unwinds", [0; 32], "exclusive"), ("closed_check_shared_then_conflict", [0; 32], "shared")] {
        let mut held = base(label, init_bytes(16)); modify(&mut held, |a| a.owner = owner);
        held.borrows.push((1, mode)); cases.push(held);
    }
    let mut panics = base("owner_panics", init_bytes(16));
    panics.script = vec![Step { returns: PROGRAM, assign: Some(OTHER), panic: true }]; cases.push(panics);
    let mut assigned = base("owner_makes_closed", vec![]);
    assigned.script = vec![Step { returns: PROGRAM, assign: Some([0; 32]), panic: false }]; cases.push(assigned);
    for case in cases {
        let inp = input(case.entries.clone()); let state = before(&inp, &case, vec![]);
        let actual = case.clone(); let source = inp.clone();
        let result = shim::case(&shim::Script::new(vec![]), move || {
            let w = Box::leak(Box::new(World::new(&source)));
            let loader = loader::<Zc>(w, actual.target);
            script::install(actual.script, Some(w.info(actual.target)));
            let _held = world::hold(w, &actual.borrows);
            let result = rec::catch(|| enc::result(&loader.exit(&Pubkey::new_from_array(actual.program)), |_| Json::Null));
            outcome(result, w.state(vec![("log", script::log())]))
        });
        push(c, &case, "exit", EXIT, ZC, state, args(&case), result);
    }
}

fn record_close(c: &mut Corpus) {
    for (label, source_lamports, destination_lamports, alias, held) in [
        ("success", 40, 9, false, None), ("zero_source", 0, 9, false, None),
        ("overflow", 40, u64::MAX, false, None), ("alias", 40, 40, true, None),
        ("source_read_conflict", 40, 9, false, Some((0, "exclusive"))),
        ("destination_read_conflict", 40, 9, false, Some((2, "exclusive"))),
        ("destination_write_conflict", 40, 9, false, Some((2, "shared"))),
        ("source_write_conflict", 40, 9, false, Some((0, "shared"))),
        ("resize_conflict", 40, 9, false, Some((1, "shared"))),
    ] {
        let mut case = base(label, init_bytes(16));
        modify(&mut case, |a| a.lamports = source_lamports);
        case.entries.push(if alias { Entry::Duplicate(0) } else {
            account(pk(2), OTHER, destination_lamports, vec![9, 8], false, true)
        });
        case.borrows = held.into_iter().collect(); case.script.clear();
        let inp = input(case.entries.clone());
        // Argument evaluation precedes the selected close boundary. The moved
        // AccountInfo contributes one actual owner of each destination Rc.
        let before_counts = if alias {
            Json::Arr(vec![Json::Arr(vec![3usize.into(), 3usize.into()])])
        } else {
            Json::Arr(vec![Json::Arr(vec![1usize.into(), 1usize.into()]),
                Json::Arr(vec![2usize.into(), 2usize.into()])])
        };
        let state = before(&inp, &case, vec![("ref_counts", before_counts)]);
        let actual = case.clone(); let source = inp.clone();
        let result = shim::case(&shim::Script::new(vec![]), move || {
            let w = Box::leak(Box::new(World::new(&source)));
            let loader = loader::<Zc>(w, 0); script::install(vec![], Some(w.info(0)));
            let _held = world::hold(w, &actual.borrows);
            let destination = w.info(1).clone();
            assert_eq!(Rc::strong_count(&destination.lamports), if alias { 3 } else { 2 });
            assert_eq!(Rc::strong_count(&destination.data), if alias { 3 } else { 2 });
            let result = rec::catch(|| enc::result(&loader.close(destination), |_| Json::Null));
            outcome(result, w.state(vec![("log", script::log()), ("ref_counts", counts(w))]))
        });
        push(c, &case, "close", CLOSE, ZC, state,
            Json::obj([("account", 0usize.into()), ("destination", 1usize.into())]), result);
    }
}

pub fn record(corpus: &mut Corpus, clone_close: bool) {
    record_constructors(corpus);
    record_identities(corpus, clone_close);
    record_init(corpus);
    record_exit(corpus);
    if clone_close { record_close(corpus); }
}
