//! Exact source-projected Anchor System wrappers, with only the complete
//! invoke_signed signature replaced. No invocation implementation is called.

use anchor_lang::context::CpiContext;
use anchor_lang::solana_program::{account_info::AccountInfo, instruction::Instruction,
    program_error::ProgramError, pubkey::Pubkey};
use anchor_lang::system_program::{Allocate, Assign, CreateAccount, Transfer};
use anchor_lang::{ToAccountInfos, ToAccountMetas};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Default)]
struct Script {
    mode: String,
    error: Option<ProgramError>,
    identities: Vec<usize>,
    calls: Vec<Json>,
    metas: usize,
    data: usize,
    error_string: Option<usize>,
}

thread_local! { static SCRIPT: RefCell<Script> = RefCell::new(Script::default()); }

fn counts(accounts: &[AccountInfo<'_>]) -> Json {
    Json::arr(accounts, |a| Json::arr(
        [Rc::strong_count(&a.lamports), Rc::strong_count(&a.data)], Json::from))
}

fn cells(accounts: &[AccountInfo<'_>]) -> Json {
    Json::arr(accounts, |a| Json::obj([
        ("lamports", (**a.lamports.borrow()).into()),
        ("data", rec::bytes(&a.data.borrow())),
    ]))
}

fn instruction(ix: &Instruction) -> Json {
    Json::obj([
        ("program", rec::bytes(ix.program_id.as_ref())),
        ("metas", Json::arr(&ix.accounts, |m| Json::obj([
            ("key", rec::bytes(m.pubkey.as_ref())),
            ("signer", m.is_signer.into()), ("writable", m.is_writable.into()),
        ]))),
        ("data", rec::bytes(&ix.data)),
    ])
}

/// Whole-signature provider. It records the actual request, mutates the actual
/// first account, then follows the chosen normal/error/unwind/terminal script.
pub fn invoke_signed(ix: &Instruction, infos: &[AccountInfo<'_>], seeds: &[&[&[u8]]])
    -> Result<(), ProgramError>
{
    let (mode, error, call) = crate::track::untracked(|| SCRIPT.with(|cell| {
        let mut script = cell.borrow_mut();
        let ids: Vec<_> = infos.iter().map(|info| {
            script.identities.iter().position(|p| *p == Rc::as_ptr(&info.data) as usize)
                .expect("request AccountInfo belongs to the prepared identity table")
        }).collect();
        let call = Json::obj([
            ("instruction", instruction(ix)),
            ("accounts", Json::arr(ids, Json::from)),
            ("signers", Json::arr(seeds, |group| Json::arr(*group, |seed| rec::bytes(seed)))),
            ("counts", counts(infos)),
        ]);
        script.metas = ix.accounts.as_ptr() as usize;
        script.data = ix.data.as_ptr() as usize;
        script.calls.push(call.clone());
        (script.mode.clone(), script.error.take(), call)
    }));
    **infos[0].lamports.borrow_mut() += 101;
    infos[0].data.borrow_mut()[0] += 7;
    match mode.as_str() {
        "ok" => Ok(()),
        "error" => Err(error.expect("scripted error")),
        "unwind" => std::panic::panic_any("opaque invoke unwind"),
        "terminal" => {
            // Exiting this separately launched child is genuinely nonreturning:
            // no source cleanup or imaginary after-state is recorded.
            println!("{}", call.to_text());
            std::process::exit(77)
        }
        _ => panic!("unknown provider mode"),
    }
}

fn account(number: u8) -> AccountInfo<'static> {
    let mut key = [0u8; 32];
    key[0] = number;
    let key = Box::leak(Box::new(Pubkey::new_from_array(key)));
    let owner = Box::leak(Box::new(Pubkey::new_from_array([55; 32])));
    let lamports = Box::leak(Box::new(100 + u64::from(number)));
    let data = Box::leak(Box::new([number, 9, 8]));
    #[cfg(feature = "modern-context")]
    { AccountInfo::new(key, false, false, lamports, data, owner, false) }
    #[cfg(not(feature = "modern-context"))]
    { AccountInfo::new(key, false, false, lamports, data, owner, false, 0) }
}

fn context<'a, 'b, 'c, T: ToAccountMetas + ToAccountInfos<'static>>(
    accounts: T, base: &[AccountInfo<'static>], remaining: Vec<AccountInfo<'static>>,
    seeds: &'a [&'b [&'c [u8]]],
) -> CpiContext<'a, 'b, 'c, 'static, T> {
    #[cfg(feature = "modern-context")]
    { CpiContext::new_with_signer(*base[3].key, accounts, seeds).with_remaining_accounts(remaining) }
    #[cfg(not(feature = "modern-context"))]
    { CpiContext::new_with_signer(base[3].clone(), accounts, seeds).with_remaining_accounts(remaining) }
}

fn error_json(error: &anchor_lang::error::Error) -> Json {
    match error {
        anchor_lang::error::Error::ProgramError(payload) => {
            let value = match &payload.program_error {
                ProgramError::Custom(code) => Json::obj([("custom", (*code).into())]),
                #[cfg(not(feature = "modern-context"))]
                ProgramError::BorshIoError(message) => Json::obj([("borsh", message.clone().into())]),
                other => panic!("unexpected provider error: {other:?}"),
            };
            assert!(payload.error_origin.is_none());
            assert!(payload.compared_values.is_none());
            Json::obj([("program_error", value), ("origin", Json::Null),
                ("compared", Json::Null), ("boxed", (!cfg!(feature = "inline-error")).into())])
        }
        other => panic!("wrong Anchor error branch: {other:?}"),
    }
}

fn run_case(operation: &str, mode: &str, alias: bool, amount: u64, borsh: bool) -> Record {
    let base = vec![account(1), account(2), account(3), account(9)];
    let remaining = vec![base[2].clone(), base[0].clone(), base[2].clone()];
    let remaining_ptr = remaining.as_ptr() as usize;
    let seeds0: &[&[u8]] = &[&[1, 2], &[], &[1, 2]];
    let seeds1: &[&[u8]] = &[&[255]];
    let seeds: &[&[&[u8]]] = &[seeds0, seeds1];
    let mut owner = [0; 32];
    owner[0] = 23;
    let owner = Pubkey::new_from_array(owner);
    let error = if mode == "error" {
        #[cfg(not(feature = "modern-context"))]
        { Some(if borsh { ProgramError::BorshIoError("owned provider error".to_string()) }
            else { ProgramError::Custom(77) }) }
        #[cfg(feature = "modern-context")]
        { assert!(!borsh); Some(ProgramError::Custom(77)) }
    } else { None };
    #[cfg(not(feature = "modern-context"))]
    let error_string = match &error {
        Some(ProgramError::BorshIoError(text)) => Some(text.as_ptr() as usize), _ => None,
    };
    #[cfg(feature = "modern-context")]
    let error_string = None;
    SCRIPT.with(|cell| *cell.borrow_mut() = Script {
        mode: mode.into(), error, error_string,
        identities: base.iter().map(|a| Rc::as_ptr(&a.data) as usize).collect(),
        ..Script::default()
    });
    let second = if alias { 0 } else { 1 };
    let before;
    let result;
    let log;
    // The context is fully prepared before recording the entry counts. Only
    // the exact projected wrapper is within the allocation tracking interval.
    match operation {
        "allocate" => {
            let ctx = context(Allocate { account_to_allocate: base[0].clone() }, &base, remaining, seeds);
            before = Json::obj([("cells", cells(&base)), ("counts", counts(&base))]);
            (result, log) = crate::track::tracked(|| crate::projected::allocate(ctx, amount));
        }
        "assign" => {
            let ctx = context(Assign { account_to_assign: base[0].clone() }, &base, remaining, seeds);
            before = Json::obj([("cells", cells(&base)), ("counts", counts(&base))]);
            (result, log) = crate::track::tracked(|| crate::projected::assign(ctx, &owner));
        }
        "create_account" => {
            let ctx = context(CreateAccount { from: base[0].clone(), to: base[second].clone() }, &base, remaining, seeds);
            before = Json::obj([("cells", cells(&base)), ("counts", counts(&base))]);
            (result, log) = crate::track::tracked(|| crate::projected::create_account(ctx, amount, 4097, &owner));
        }
        "transfer" => {
            let ctx = context(Transfer { from: base[0].clone(), to: base[second].clone() }, &base, remaining, seeds);
            before = Json::obj([("cells", cells(&base)), ("counts", counts(&base))]);
            (result, log) = crate::track::tracked(|| crate::projected::transfer(ctx, amount));
        }
        _ => panic!("unknown wrapper"),
    }
    let (calls, metas_ptr, data_ptr) = SCRIPT.with(|cell| {
        let script = cell.borrow();
        (script.calls.clone(), script.metas, script.data)
    });
    assert_eq!(calls.len(), 1);
    let free_order: Vec<&str> = log.frees.iter().filter_map(|p| {
        if *p == metas_ptr { Some("metas") } else if *p == data_ptr { Some("data") }
        else if *p == remaining_ptr { Some("remaining") } else { None }
    }).collect();
    assert_eq!(free_order, ["metas", "data", "remaining"]);
    let mut fresh_boxes = 0usize;
    let mut same_string = Json::Null;
    if let Ok(Err(anchor_lang::error::Error::ProgramError(payload))) = &result {
        #[cfg(not(feature = "inline-error"))]
        {
            let pointer = &**payload as *const _ as usize;
            assert!(log.allocs.contains(&pointer));
            assert!(log.fresh_live.contains(&pointer));
            fresh_boxes = 1;
        }
        #[cfg(not(feature = "modern-context"))]
        if let ProgramError::BorshIoError(text) = &payload.program_error {
            let original = SCRIPT.with(|cell| cell.borrow().error_string);
            assert_eq!(original, Some(text.as_ptr() as usize));
            same_string = true.into();
        }
        #[cfg(feature = "modern-context")]
        assert!(SCRIPT.with(|cell| cell.borrow().error_string).is_none());
    }
    if result.is_ok() {
        assert_eq!(log.fresh_live.len(), fresh_boxes, "no unmodeled surviving allocation");
    }
    let after = Json::obj([
        ("cells", cells(&base)), ("counts", counts(&base)), ("calls", Json::Arr(calls)),
        ("freed", Json::arr(free_order, Json::from)),
        ("fresh_boxes", fresh_boxes.into()), ("same_string", same_string),
    ]);
    let outcome = match result {
        Ok(value) => rec::returned(match value {
            Ok(()) => rec::ok(Json::Null), Err(error) => rec::err(error_json(&error)),
        }, after),
        Err(reason) => rec::unwound(reason, after),
    };
    Record {
        id: format!("{operation}/{mode}/alias{alias}/amount{amount}/borsh{borsh}"),
        function: match operation {
            "allocate" => "anchor_lang::system_program::allocate",
            "assign" => "anchor_lang::system_program::assign",
            "create_account" => "anchor_lang::system_program::create_account",
            "transfer" => "anchor_lang::system_program::transfer",
            _ => unreachable!(),
        }, generics: vec![], layout: None, state: before,
        args: Json::obj([("operation", operation.into()), ("mode", mode.into()),
            ("alias", alias.into()), ("amount", amount.into()), ("borsh", borsh.into())]),
        outcome, observed: None,
    }
}

pub fn main() {
    let argv: Vec<String> = std::env::args().collect();
    if argv.get(1).map(String::as_str) == Some("--build-config") {
        println!("{{\"scope\":\"projected-wrapper\",\"panic\":\"{}\",\"debug_assertions\":{},\"solana_cfg\":{},\"pointer_width\":{},\"little_endian\":{},\"signature_check_enabled\":{}}}",
            if cfg!(panic = "unwind") { "unwind" } else { "abort" },
            cfg!(debug_assertions), cfg!(target_os = "solana"), usize::BITS,
            cfg!(target_endian = "little"), option_env!("CARGO_FEATURE_SIGNATURE_CHECK").is_some());
        return;
    }
    rec::init();
    if argv.get(1).map(String::as_str) == Some("--terminal") {
        run_case(argv.get(2).expect("terminal operation"), "terminal", false, 37, false);
        unreachable!("opaque terminal must not return");
    }
    let mut corpus = Corpus::new(crate::CORPUS, &[("anchor-lang", crate::VERSION)]);
    for operation in ["allocate", "assign", "create_account", "transfer"] {
        for amount in [0, 37, u64::MAX] {
            corpus.push(run_case(operation, "ok", false, amount, false));
        }
        corpus.push(run_case(operation, "error", false, 37, false));
        corpus.push(run_case(operation, "unwind", false, 37, false));
        #[cfg(not(feature = "modern-context"))]
        corpus.push(run_case(operation, "error", false, 37, true));
        if operation == "create_account" || operation == "transfer" {
            corpus.push(run_case(operation, "ok", true, 37, false));
        }
        let child = std::process::Command::new(std::env::current_exe().expect("executable"))
            .args(["--terminal", operation]).output().expect("terminal child");
        assert_eq!(child.status.code(), Some(77));
        assert!(child.stderr.is_empty());
        let request = String::from_utf8(child.stdout).expect("terminal request UTF8");
        let mut record = run_case(operation, "ok", false, 37, false);
        record.id = format!("{operation}/terminal");
        record.args = Json::obj([("operation", operation.into()), ("mode", "terminal".into()),
            ("alias", false.into()), ("amount", 37u64.into()), ("borsh", false.into())]);
        record.outcome = Json::obj([("exit", "terminated".into()),
            ("reason", "opaque invoke terminal".into()), ("request", Json::Raw(request))]);
        corpus.push(record);
    }
    #[cfg(feature = "system-id")]
    {
        use anchor_lang::Id;
        corpus.push(Record { id: "System/id".into(),
            function: "<anchor_lang::system_program::System as anchor_lang::Id>::id",
            generics: vec![], layout: None, state: Json::Null, args: Json::Null,
            outcome: rec::returned(rec::bytes(anchor_lang::system_program::System::id().as_ref()), Json::Null),
            observed: None });
    }
    corpus.write(&rec::out_dir()).expect("write projected-wrapper corpus");
}
