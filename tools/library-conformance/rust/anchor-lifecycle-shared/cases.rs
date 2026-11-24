//! Calls the lifecycle functions of the pinned release on serialized account input.
//! No invocation implementation is reached. Receiver preparation happens before
//! the measured boundary, and returned resources stay live during observation.

use std::{collections::BTreeSet, mem::ManuallyDrop, rc::Rc};
use anchor_lang::prelude::*;
use conformance_accounts::{Account as InputAccount, Entry, Input};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim as shim;
use crate::{script::{self, ExitPayload, Inner, Payload, ProgramTag, Script, Var, PROGRAM, DISC}, track, world::{self, World, account, input, pk}};

pub struct Api {
    pub object: &'static str,
    pub method: &'static str,
    pub function: &'static str,
}

#[derive(Clone)]
struct Case {
    label: &'static str,
    entries: Vec<Entry>,
    target: usize,
    borrows: Vec<(usize, &'static str)>,
    script: Script,
    program: [u8; 32],
    optional_some: bool,
}

fn base(label: &'static str) -> Case {
    let mut bytes = DISC.to_vec(); bytes.extend([11, 12, 13, 14, 15, 16, 17, 18]);
    let mut entry = account(PROGRAM, PROGRAM, 40, bytes, true, true);
    if let Entry::Account(account) = &mut entry { account.executable = true; }
    Case { label, entries: vec![entry], target: 0, borrows: vec![],
        script: Script::normal(), program: PROGRAM, optional_some: true }
}

fn change(case: &mut Case, f: impl FnOnce(&mut InputAccount)) {
    let Entry::Account(account) = &mut case.entries[0] else { unreachable!() };
    f(account);
}

fn constructor_cases(api: &Api) -> Vec<Case> {
    let mut cases = vec![base("ok")];
    let mut duplicate = base("duplicate_record"); duplicate.entries.push(Entry::Duplicate(0)); duplicate.target = 1; cases.push(duplicate);
    let mut readonly = base("readonly_is_allowed"); change(&mut readonly, |account| account.is_writable = false); cases.push(readonly);
    let mut other_program = base("caller_program_is_ignored"); other_program.program = pk(0x33); cases.push(other_program);
    if api.method == "try_accounts" { let mut empty = base("empty_accounts"); empty.entries.clear(); cases.push(empty); }
    match api.object {
        "signer" => {
            let mut failed = base("not_signer"); change(&mut failed, |account| account.is_signer = false); cases.push(failed);
        }
        "system_account" => {
            change(&mut cases[0], |account| account.owner = [0; 32]);
            let mut failed = base("not_system_owned"); failed.borrows.push((1, "exclusive")); cases.push(failed);
        }
        "program" | "interface" => {
            let mut failed = base("not_executable"); change(&mut failed, |account| account.executable = false); cases.push(failed);
            if api.object == "program" {
                let mut failed = base("wrong_id_before_executable"); change(&mut failed, |account| { account.key = pk(0x55); account.executable = false; });
                failed.script.id[1].key = pk(0x66); cases.push(failed);
                let mut panic = base("second_id_unwinds_after_error"); change(&mut panic, |account| account.key = pk(0x55));
                panic.script.id[1].panic = true; panic.script.id[1].assign = Some(pk(0x68)); cases.push(panic);
                let mut first = base("first_id_unwinds"); first.script.id[0].panic = true; cases.push(first);
            } else {
                let mut failed = base("check_id_error"); failed.script.check_id[0].error = 71; cases.push(failed);
                let mut panic = base("check_id_unwinds"); panic.script.check_id[0].panic = true; cases.push(panic);
            }
        }
        "sysvar" => {
            let mut failed = base("sysvar_error_is_replaced"); failed.script.sysvar[0].error = 71; cases.push(failed);
            let mut string = base("sysvar_borsh_error_is_dropped"); string.script.sysvar[0].error = 1; cases.push(string);
            let mut panic = base("sysvar_unwinds"); panic.script.sysvar[0].panic = true; cases.push(panic);
            let mut changed = base("sysvar_effects_survive_error"); changed.script.sysvar[0].error = 71;
            changed.script.sysvar[0].lamports = Some(99); cases.push(changed);
        }
        "account" | "interface_account" => {
            let mut closed = base("not_initialized"); change(&mut closed, |account| { account.owner = [0; 32]; account.lamports = 0; }); cases.push(closed);
            let mut init_borrow = base("initialization_read_unwinds"); change(&mut init_borrow, |account| account.owner = [0; 32]);
            init_borrow.borrows.push((0, "exclusive")); cases.push(init_borrow);
            let mut wrong = base("wrong_owner"); change(&mut wrong, |account| account.owner = pk(0x55));
            if api.object == "account" { wrong.script.owner[1].key = pk(0x66); }
            else { wrong.script.check_owner[0].error = 71; }
            cases.push(wrong);
            let mut diagnostic = base("owner_callback_unwinds");
            if api.object == "account" {
                change(&mut diagnostic, |account| account.owner = pk(0x55)); diagnostic.script.owner[1].panic = true;
                diagnostic.script.owner[1].assign = Some(pk(0x68));
            } else { diagnostic.script.check_owner[0].panic = true; diagnostic.script.check_owner[0].assign = Some(pk(0x68)); }
            cases.push(diagnostic);
            let mut changed = base("owner_callback_changes_owner"); change(&mut changed, |account| account.owner = pk(0x55));
            if api.object == "account" { changed.script.owner[0].assign = Some(PROGRAM); }
            else { changed.script.check_owner[0].assign = Some(PROGRAM); }
            cases.push(changed);
            for (label, mode) in [("shared_data_borrow", "shared"), ("exclusive_data_borrow", "exclusive")] {
                let mut held = base(label); held.borrows.push((1, mode)); cases.push(held);
            }
            let mut failed = base("decoder_error"); failed.script.decode[0].error = 73; cases.push(failed);
            let mut panic = base("decoder_unwinds_with_effects"); panic.script.decode[0].panic = true;
            panic.script.decode[0].lamports = Some(93); cases.push(panic);
            let mut mismatch = base("wrong_discriminator"); change(&mut mismatch, |account| account.data[0] = 255); cases.push(mismatch);
            let mut empty = base("empty_data"); change(&mut empty, |account| account.data.clear()); cases.push(empty);
            let mut mutated = base("decoder_changes_owner"); mutated.script.decode[0].assign = Some(pk(0x62)); cases.push(mutated);
        }
        _ => {}
    }
    cases
}

fn reload_cases() -> Vec<Case> {
    let mut cases = vec![base("replacement")];
    let mut owner = base("owner_changed_after_construction"); change(&mut owner, |account| account.owner = pk(0x55));
    owner.script.check_owner[0].error = 71; cases.push(owner);
    for (label, mode) in [("shared_data_borrow", "shared"), ("exclusive_data_borrow", "exclusive")] {
        let mut held = base(label); held.borrows.push((1, mode)); cases.push(held);
    }
    let mut failed = base("decoder_error_keeps_old_payload"); failed.script.decode[0].error = 73; cases.push(failed);
    let mut panic = base("decoder_unwinds_keeps_old_payload"); panic.script.decode[0].panic = true; cases.push(panic);
    let mut dropped = base("old_drop_unwinds_replacement_installed"); dropped.script.drop_payload[0].panic = true;
    dropped.script.drop_payload[0].lamports = Some(97); cases.push(dropped);
    cases
}

fn exit_cases() -> Vec<Case> {
    let mut cases = vec![base("write")];
    let mut empty = base("empty_destination_has_no_memcpy"); change(&mut empty, |account| account.data.clear()); cases.push(empty);
    let mut empty_input = base("empty_source_still_calls_memcpy"); empty_input.script.serialize[0].bytes.clear(); cases.push(empty_input);
    let mut mismatch = base("caller_not_saved_owner"); mismatch.program = pk(0x33); cases.push(mismatch);
    let mut closed = base("closed"); change(&mut closed, |account| { account.owner = [0; 32]; account.data.clear(); }); cases.push(closed);
    let mut replaced = base("owner_changed_saved_owner_retained"); change(&mut replaced, |account| account.owner = pk(0x55)); cases.push(replaced);
    let mut short = base("partial_write"); change(&mut short, |account| account.data.truncate(3)); cases.push(short);
    let mut partial_error = base("partial_write_then_error"); change(&mut partial_error, |account| account.data.truncate(3));
    partial_error.script.serialize[0].error = 79; cases.push(partial_error);
    let mut panic = base("write_then_unwind"); panic.script.serialize[0].panic = true; cases.push(panic);
    let mut owner_panic = base("owner_unwinds"); owner_panic.script.owner[0].panic = true; cases.push(owner_panic);
    let mut readonly = base("readonly_is_not_checked"); change(&mut readonly, |account| account.is_writable = false); cases.push(readonly);
    for (label, mode) in [("shared_conflict", "shared"), ("exclusive_conflict", "exclusive")] {
        let mut held = base(label); held.borrows.push((1, mode)); cases.push(held);
    }
    let mut closed_borrow = base("closed_check_unwinds"); change(&mut closed_borrow, |account| account.owner = [0; 32]);
    closed_borrow.borrows.push((1, "exclusive")); cases.push(closed_borrow);
    cases
}

fn close_cases() -> Vec<Case> {
    let mut cases = vec![];
    for (label, source, destination, alias, borrows) in [
        ("ok", 40, 10, false, vec![]),
        ("alias", 40, 40, true, vec![]),
        ("overflow", u64::MAX, 1, false, vec![]),
        ("destination_read_conflict", 40, 10, false, vec![(2, "exclusive")]),
        ("source_read_conflict", 40, 10, false, vec![(0, "exclusive")]),
        ("both_read_conflict", 40, 10, false, vec![(0, "exclusive"), (2, "exclusive")]),
        ("destination_write_conflict", 40, 10, false, vec![(2, "shared")]),
        ("source_write_conflict_after_credit", 40, 10, false, vec![(0, "shared")]),
        ("resize_conflict_after_transfers", 40, 10, false, vec![(1, "shared")]),
    ] {
        let mut case = base(label);
        change(&mut case, |account| account.lamports = source);
        case.entries.push(if alias { Entry::Duplicate(0) } else { account(pk(2), pk(3), destination, vec![9], false, true) });
        case.borrows = borrows; cases.push(case);
    }
    cases
}

fn collection_cases(api: &Api) -> Vec<Case> {
    let mut cases = vec![base("some_ok")];
    let mut failed = base("inner_error_with_effects"); failed.script.inner[0].error = 81;
    failed.script.inner[0].lamports = Some(101); cases.push(failed);
    let mut panic = base("inner_unwinds_with_effects"); panic.script.inner[0].panic = true;
    panic.script.inner[0].lamports = Some(103); cases.push(panic);
    if api.object == "option" {
        let mut none = base("none"); none.optional_some = false; cases.push(none);
        let mut other = base("other_key_calls_inner"); change(&mut other, |account| account.key = pk(0x19)); cases.push(other);
        if api.method == "try_accounts" {
            // A program-ID sentinel skips the inner constructor even when its
            // script would fail. Use another key to observe its failure effects.
            let mut failed = base("other_key_inner_error_with_effects");
            change(&mut failed, |account| account.key = pk(0x19));
            failed.script.inner[0].error = 81; failed.script.inner[0].lamports = Some(101); cases.push(failed);
            let mut panic = base("other_key_inner_unwinds_with_effects");
            change(&mut panic, |account| account.key = pk(0x19));
            panic.script.inner[0].panic = true; panic.script.inner[0].lamports = Some(103); cases.push(panic);
        }
    }
    if api.method == "try_accounts" {
        let mut empty = base("empty_accounts"); empty.entries.clear();
        empty.script.inner[0].lamports = None; cases.push(empty);
    }
    if api.method == "close" {
        for case in &mut cases { case.entries.push(account(pk(2), pk(3), 10, vec![9], false, true)); }
    }
    cases
}

fn counts(world: &World) -> Vec<Vec<usize>> {
    world.distinct.iter().map(|&index| {
        let info = world.info(index);
        vec![Rc::strong_count(&info.lamports), Rc::strong_count(&info.data)]
    }).collect()
}

fn counts_json(counts: &[Vec<usize>]) -> Json { Json::arr(counts, |pair| Json::arr(pair, |value| (*value).into())) }

fn expected_counts(api: &Api, case: &Case) -> Vec<Vec<usize>> {
    let mut result: Vec<Vec<usize>> = vec![];
    let mut ids: Vec<usize> = vec![];
    for entry in &case.entries {
        match entry {
            Entry::Account(_) => { ids.push(result.len()); result.push(vec![1, 1]); }
            Entry::Duplicate(index) => { let id = ids[*index as usize]; ids.push(id); result[id][0] += 1; result[id][1] += 1; }
        }
    }
    let mut add = |record: usize| { let id = ids[record]; result[id][0] += 1; result[id][1] += 1; };
    if cfg!(feature = "legacy-anchor") && matches!(api.object, "account" | "interface_account") && matches!(api.method, "reload" | "exit" | "close") { add(case.target); }
    if cfg!(feature = "legacy-anchor") && api.object == "unchecked_account" && api.method == "try_from" { add(case.target); }
    if api.method == "close" { add(1); }
    result
}

fn info_result<T: AsRef<AccountInfo<'static>>>(world: &World, value: &T, payload: Json) -> Json {
    Json::obj([("info", world.info_json(value.as_ref())), ("payload", payload)])
}

fn record_id(world: &World, info: &AccountInfo) -> Json {
    world.infos.iter().position(|candidate| std::ptr::eq(candidate as *const _ as *const u8,
        info as *const _ as *const u8)).expect("actual record reference").into()
}

fn prepare_account(world: &'static World, target: usize) -> Account<'static, Payload> {
    let info = world.info(target); let old_owner = *info.owner;
    info.assign(&Pubkey::new_from_array(PROGRAM));
    let mut script = Script::normal(); script.decode[0].value = 11;
    script::install(script, world, target, false);
    let receiver = Account::<Payload>::try_from_unchecked(info).expect("prepare account");
    info.assign(&old_owner); receiver
}

fn prepare_interface(world: &'static World, target: usize) -> InterfaceAccount<'static, Payload> {
    let info = world.info(target); let old_owner = *info.owner;
    info.assign(&Pubkey::new_from_array(PROGRAM));
    let mut script = Script::normal(); script.decode[0].value = 11;
    script::install(script, world, target, false);
    let receiver = InterfaceAccount::<Payload>::try_from_unchecked(info).expect("prepare interface");
    info.assign(&old_owner); receiver
}

fn execute(api: &'static Api, case: Case, source: Input) -> Json {
    let world = Box::leak(Box::new(World::new(&source)));
    let mut account_receiver = if api.object == "account" && matches!(api.method, "reload" | "close") {
        Some(ManuallyDrop::new(prepare_account(world, case.target)))
    } else { None };
    let mut interface_receiver = if api.object == "interface_account" && api.method == "reload" {
        Some(ManuallyDrop::new(prepare_interface(world, case.target)))
    } else { None };
    let mut exit_account: Option<ManuallyDrop<Account<'static, ExitPayload>>> = None;
    let mut exit_interface: Option<ManuallyDrop<InterfaceAccount<'static, ExitPayload>>> = None;
    if matches!(api.object, "account" | "interface_account") && api.method == "exit" {
        let info = world.info(case.target); let owner = *info.owner;
        info.assign(&Pubkey::new_from_array(PROGRAM));
        let mut script = Script::normal(); script.decode[0].value = 11;
        script::install(script, world, case.target, false);
        if api.object == "account" { exit_account = Some(ManuallyDrop::new(Account::<ExitPayload>::try_from_unchecked(info).expect("prepare exit account"))); }
        else { exit_interface = Some(ManuallyDrop::new(InterfaceAccount::<ExitPayload>::try_from_unchecked(info).expect("prepare exit interface"))); }
        info.assign(&owner);
    }
    let boxed = Box::new(Inner(11));
    let optional = if case.optional_some { Some(Inner(11)) } else { None };
    let destination = if api.method == "close" { Some(world.info(1).clone()) } else { None };
    #[cfg(feature = "legacy-anchor")]
    let unchecked_argument = if api.object == "unchecked_account" && api.method == "try_from" { Some(world.info(case.target).clone()) } else { None };
    let _held = world::hold(world, &case.borrows);
    script::install(case.script.clone(), world, case.target, api.method == "reload");
    assert_eq!(counts(world), expected_counts(api, &case), "caller-owned resources at the boundary");
    let mut remaining = &world.infos[case.target..];
    let mut bumps = script::initial_bumps();
    let mut reallocs = BTreeSet::from([Pubkey::new_from_array(pk(0x31))]);
    let program = Pubkey::new_from_array(case.program);
    let (result, heap) = track::tracked(|| {
        match (api.object, api.method) {
            ("account", "try_from") => script::keep(Account::<Payload>::try_from(world.info(case.target)), |value| info_result(world, value, value.0.into())),
            ("account", "try_from_unchecked") => script::keep(Account::<Payload>::try_from_unchecked(world.info(case.target)), |value| info_result(world, value, value.0.into())),
            ("interface_account", "try_from_unchecked") => script::keep(InterfaceAccount::<Payload>::try_from_unchecked(world.info(case.target)), |value| info_result(world, value, value.0.into())),
            ("program", "try_from") => script::keep(Program::<ProgramTag>::try_from(world.info(case.target)), |value| info_result(world, value, Json::Null)),
            ("signer", "try_from") => script::keep(Signer::try_from(world.info(case.target)), |value| info_result(world, value, Json::Null)),
            ("unchecked_account", "try_from") => {
                #[cfg(feature = "legacy-anchor")]
                let value = UncheckedAccount::try_from(unchecked_argument.expect("moved input"));
                #[cfg(not(feature = "legacy-anchor"))]
                let value = UncheckedAccount::try_from(world.info(case.target));
                let value = ManuallyDrop::new(value);
                track::untracked(|| info_result(world, &*value, Json::Null))
            }
            ("account", "try_accounts") => script::keep(Account::<Payload>::try_accounts(&program, &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs), |value| info_result(world, value, value.0.into())),
            ("interface_account", "try_accounts") => script::keep(InterfaceAccount::<Payload>::try_accounts(&program, &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs), |value| info_result(world, value, value.0.into())),
            ("program", "try_accounts") => script::keep(Program::<ProgramTag>::try_accounts(&program, &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs), |value| info_result(world, value, Json::Null)),
            ("interface", "try_accounts") => script::keep(Interface::<ProgramTag>::try_accounts(&program, &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs), |value| info_result(world, value, Json::Null)),
            ("signer", "try_accounts") => script::keep(Signer::try_accounts(&program, &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs), |value| info_result(world, value, Json::Null)),
            ("system_account", "try_accounts") => script::keep(SystemAccount::try_accounts(&program, &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs), |value| info_result(world, value, Json::Null)),
            ("unchecked_account", "try_accounts") => script::keep(UncheckedAccount::try_accounts(&program, &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs), |value| info_result(world, value, Json::Null)),
            ("account_info", "try_accounts") => script::keep(AccountInfo::try_accounts(&program, &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs), |value| Json::obj([("info", world.info_json(value)), ("payload", Json::Null)])),
            ("sysvar", "try_accounts") => script::keep(Sysvar::<Var>::try_accounts(&program, &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs), |value| info_result(world, value, value.0.into())),
            ("boxed", "try_accounts") => script::keep(Box::<Inner>::try_accounts(&program, &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs), |value| value.0.into()),
            ("option", "try_accounts") => script::keep(Option::<Inner>::try_accounts(&program, &mut remaining, &[0xab, 0xcd], &mut bumps, &mut reallocs), |value| value.as_ref().map_or(Json::Null, |value| value.0.into())),
            ("account", "reload") => script::keep(account_receiver.as_mut().unwrap().reload(), |_| Json::Null),
            ("interface_account", "reload") => script::keep(interface_receiver.as_mut().unwrap().reload(), |_| Json::Null),
            ("account", "exit") => script::keep(exit_account.as_ref().unwrap().exit(&program), |_| Json::Null),
            ("interface_account", "exit") => script::keep(exit_interface.as_ref().unwrap().exit(&program), |_| Json::Null),
            ("account", "close") => script::keep(account_receiver.as_ref().unwrap().close(destination.expect("destination")), |_| Json::Null),
            ("boxed", "exit") => script::keep(boxed.exit(&program), |_| Json::Null),
            ("boxed", "close") => script::keep(boxed.close(destination.expect("destination")), |_| Json::Null),
            ("option", "exit") => script::keep(optional.exit(&program), |_| Json::Null),
            ("default", "exit") => script::keep(script::DefaultExit.exit(&program), |_| Json::Null),
            _ => panic!("unhandled lifecycle API {}::{}", api.object, api.method),
        }
    });
    let mut fields = vec![("log", script::log()), ("ref_counts", counts_json(&counts(world))),
        ("fresh_live", heap.fresh_live.len().into()), ("program_string_dropped", script::program_string_dropped(&heap))];
    if api.method == "try_accounts" {
        fields.push(("remaining", Json::arr(remaining, |info| record_id(world, info))));
        fields.push(("bumps", script::bumps_json(&bumps)));
        fields.push(("reallocs", Json::arr(&reallocs, |key| rec::bytes(key.as_ref()))));
    }
    if api.method == "reload" {
        let value = if let Some(receiver) = account_receiver.as_ref() { receiver.0 }
            else { interface_receiver.as_ref().unwrap().0 };
        fields.push(("payload", value.into()));
    }
    let state = world.state(fields);
    match result { Ok(value) => rec::returned(value, state), Err(reason) => rec::unwound(reason, state) }
}

fn generics(api: &Api) -> Vec<(&'static str, String)> {
    let mut result = vec![];
    let payload = match api.object {
        "account" | "interface_account" => Some(if api.method == "exit" { "ExitPayload" } else { "Payload" }),
        "program" | "interface" => Some("ProgramTag"), "sysvar" => Some("Var"),
        "boxed" | "option" => Some("Inner"), "default" => Some("DefaultExit"), _ => None,
    };
    if let Some(name) = payload {
        result.push((if api.object == "default" { "Self" } else { "T" }, format!("conformance_anchor_lifecycle::script::{name}")));
    }
    if api.method == "try_accounts" && !cfg!(feature = "legacy-anchor") { result.push(("B", "u64".to_string())); }
    result
}

pub fn record(corpus: &mut Corpus, apis: &'static [Api]) {
    for api in apis {
        let cases = if matches!(api.object, "boxed" | "option") { collection_cases(api) }
            else if api.method == "reload" { reload_cases() }
            else if api.method == "close" { close_cases() }
            else if api.method == "exit" { exit_cases() }
            else { constructor_cases(api) };
        for case in cases {
            let inp = input(case.entries.clone());
            let mut fields = vec![("log", Json::Arr(vec![])), ("ref_counts", counts_json(&expected_counts(api, &case))),
                ("fresh_live", 0usize.into()), ("program_string_dropped", Json::Null),
                ("syscalls", shim::Script::new(vec![]).state_before())];
            if api.method == "try_accounts" {
                fields.push(("remaining", Json::arr(case.target..case.entries.len(), Json::from)));
                fields.push(("bumps", script::bumps_json(&script::initial_bumps())));
                fields.push(("reallocs", Json::Arr(vec![rec::bytes(&pk(0x31))])));
            }
            if api.method == "reload" { fields.push(("payload", 11u64.into())); }
            let state = world::state_before(&inp, &case.borrows, fields);
            let args = Json::obj([("account", case.target.into()), ("destination", 1usize.into()),
                ("program_id", rec::bytes(&case.program)), ("instruction_data", rec::bytes(&[0xab, 0xcd])),
                ("script", case.script.json()), ("saved_owner", rec::bytes(&PROGRAM)),
                ("optional_some", case.optional_some.into()), ("inner_value", 11u64.into())]);
            let label = case.label;
            let outcome = shim::case(&shim::Script::new(vec![]), move || execute(api, case, inp));
            corpus.push(Record { id: format!("{}/{}/{label}", api.object, api.method), function: api.function,
                generics: generics(api), layout: None, state, args, outcome, observed: None });
        }
    }
}
