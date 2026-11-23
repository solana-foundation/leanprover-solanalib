//! Exact Anchor SPL token wrapper projections. The complete invoke,
//! invoke_signed and get_return_data signatures are scripted here. No SDK
//! invocation body or token processor is called by this driver.

use crate::anchor_lang::context::CpiContext;
use crate::anchor_lang::solana_program::{account_info::AccountInfo,
    instruction::Instruction, program_error::ProgramError, pubkey::Pubkey};
use crate::anchor_lang::{ToAccountInfos, ToAccountMetas};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use std::cell::RefCell;
use std::rc::{Rc, Weak};

#[derive(Clone)]
pub struct Case {
    pub operation: &'static str,
    pub mode: &'static str,
    pub getter: &'static str,
    pub alias: bool,
    pub amount: u64,
    pub decimals: u8,
    pub authority_type: u8,
    pub option1: Option<Pubkey>,
    pub option2: Option<Pubkey>,
    pub extensions: bool,
    pub context_program: &'static str,
    pub extension_program: &'static str,
    pub empty_seeds: bool,
    pub borsh: bool,
}

impl Case {
    fn normal(operation: &'static str) -> Self {
        Self { operation, mode: "ok", getter: "good", alias: false, amount: 42,
            decimals: 9, authority_type: 3, option1: Some(key(85)), option2: Some(key(86)),
            extensions: false, context_program: "token2022", extension_program: "token2022",
            empty_seeds: false, borsh: false }
    }
}

type Lamports = Weak<RefCell<&'static mut u64>>;
type Data = Weak<RefCell<&'static mut [u8]>>;

#[derive(Default)]
struct Script {
    mode: String,
    getter: String,
    error: Option<ProgramError>,
    identities: Vec<usize>,
    lamports: Vec<Lamports>,
    data_cells: Vec<Data>,
    seed_pointer: usize,
    calls: Vec<Json>,
    getters: Vec<Json>,
    metas: usize,
    data: usize,
    returned: Option<usize>,
    expected_program: Option<Pubkey>,
    error_string: Option<usize>,
}

thread_local! { static SCRIPT: RefCell<Script> = RefCell::new(Script::default()); }

pub fn key(number: u8) -> Pubkey {
    let mut bytes = [0; 32]; bytes[0] = number;
    Pubkey::new_from_array(bytes)
}

fn program(which: &str) -> Pubkey {
    match which {
        "token2022" => "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb".parse().unwrap(),
        "legacy" => "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA".parse().unwrap(),
        "wrong" => key(99),
        _ => panic!("unknown selected program"),
    }
}

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

fn input_infos(accounts: &[AccountInfo<'_>]) -> Json {
    Json::arr(accounts, |a| Json::obj([
        ("key", rec::bytes(a.key.as_ref())), ("owner", rec::bytes(a.owner.as_ref())),
        ("signer", a.is_signer.into()), ("writable", a.is_writable.into()),
        ("executable", a.executable.into()),
    ]))
}

fn instruction(ix: &Instruction) -> Json {
    Json::obj([
        ("program", rec::bytes(ix.program_id.as_ref())),
        ("metas", Json::arr(&ix.accounts, |m| Json::obj([
            ("key", rec::bytes(m.pubkey.as_ref())),
            ("signer", m.is_signer.into()), ("writable", m.is_writable.into()),
        ]))), ("data", rec::bytes(&ix.data)),
    ])
}

fn terminal(reason: &str) -> ! {
    let detail = SCRIPT.with(|cell| {
        let script = cell.borrow();
        Json::obj([("calls", Json::Arr(script.calls.clone())),
            ("getters", Json::Arr(script.getters.clone()))])
    });
    println!("{}", Json::obj([("exit", "terminated".into()), ("reason", reason.into()),
        ("detail", detail), ("syscalls", Json::Arr(vec![]))]).to_text());
    std::process::exit(77)
}

fn provider(ix: &Instruction, infos: &[AccountInfo<'_>], seeds: &[&[&[u8]]], signed: bool)
    -> Result<(), ProgramError>
{
    let (mode, error) = crate::track::untracked(|| SCRIPT.with(|cell| {
        let mut script = cell.borrow_mut();
        let ids: Vec<_> = infos.iter().map(|info| script.identities.iter()
            .position(|p| *p == Rc::as_ptr(&info.data) as usize)
            .expect("the invocation uses an actual input AccountInfo identity")).collect();
        if signed { assert_eq!(seeds.as_ptr() as usize, script.seed_pointer); }
        let call = Json::obj([
            ("instruction", instruction(ix)), ("accounts", Json::arr(ids, Json::from)),
            ("signers", Json::arr(seeds, |group| Json::arr(*group, |seed| rec::bytes(seed)))),
            ("seed_reference", if signed { 0usize.into() } else { Json::Null }),
            ("counts", counts(infos)),
        ]);
        script.metas = ix.accounts.as_ptr() as usize;
        script.data = ix.data.as_ptr() as usize;
        script.calls.push(call);
        let mode = match script.mode.as_str() {
            "ok" => "ok", "error" => "error", "unwind" => "unwind", "terminal" => "terminal",
            _ => panic!("unknown provider mode"),
        };
        (mode, script.error.take())
    }));
    // The provider changes actual caller storage. All cases initialize enough
    // headroom and a nonempty data slice; these are scripted effects, not an
    // assumption that an opaque CPI succeeds or has a token processor effect.
    **infos[0].lamports.borrow_mut() += 101;
    infos[0].data.borrow_mut()[0] += 7;
    match mode {
        "ok" => Ok(()),
        "error" => Err(error.expect("scripted error")),
        "unwind" => std::panic::panic_any("opaque invoke unwind"),
        "terminal" => terminal("opaque invoke terminal"),
        _ => panic!("unknown provider mode"),
    }
}

/// These are the entire assumed invocation signatures, not syscall shims
/// beneath a real SDK invoke wrapper.
pub fn invoke_signed(ix: &Instruction, infos: &[AccountInfo<'_>], seeds: &[&[&[u8]]])
    -> Result<(), ProgramError> { provider(ix, infos, seeds, true) }
pub fn invoke(ix: &Instruction, infos: &[AccountInfo<'_>]) -> Result<(), ProgramError> {
    provider(ix, infos, &[], false)
}

/// The statement-temporary AccountInfo array must already be released here.
/// Weak references observe counts without adding an owner of either Rc.
pub fn get_return_data() -> Option<(Pubkey, Vec<u8>)> {
    let (kind, expected) = crate::track::untracked(|| SCRIPT.with(|cell| {
        let mut script = cell.borrow_mut();
        let observed = Json::obj([
            ("counts", Json::arr(script.lamports.iter().zip(&script.data_cells), |(l, d)|
                Json::arr([l.strong_count(), d.strong_count()], Json::from))),
            ("metas_live", crate::track::fresh_live_now(script.metas).into()),
            ("data_live", crate::track::fresh_live_now(script.data).into()),
        ]);
        script.getters.push(observed);
        let kind = match script.getter.as_str() {
            "good" => "good", "short" => "short", "long" => "long", "wrong" => "wrong",
            "none" => "none", "unwind" => "unwind", "terminal" => "terminal",
            _ => panic!("unknown getter mode"),
        };
        (kind, script.expected_program.unwrap())
    }));
    let (program, bytes) = match kind {
        "good" => (expected, 165u64.to_le_bytes().to_vec()),
        "short" => (expected, vec![1; 7]),
        "long" => (expected, vec![1; 9]),
        "wrong" => (key(99), vec![1]),
        "none" => return None,
        "unwind" => std::panic::panic_any("opaque getter unwind"),
        "terminal" => terminal("opaque getter terminal"),
        _ => panic!("unknown getter mode"),
    };
    SCRIPT.with(|cell| cell.borrow_mut().returned = Some(bytes.as_ptr() as usize));
    Some((program, bytes))
}

fn account(number: u8, address: Pubkey) -> AccountInfo<'static> {
    let key = Box::leak(Box::new(address));
    let owner = Box::leak(Box::new(Pubkey::new_from_array([55; 32])));
    let lamports = Box::leak(Box::new(100 + u64::from(number)));
    let data = Box::leak(Box::new([number, 9, 8]));
    #[cfg(feature = "modern-context")]
    { AccountInfo::new(key, false, false, lamports, data, owner, false) }
    #[cfg(not(feature = "modern-context"))]
    { AccountInfo::new(key, false, false, lamports, data, owner, false, 0) }
}

pub fn context<'a, 'b, 'c, T: ToAccountMetas + ToAccountInfos<'static>>(
    accounts: T, base: &[AccountInfo<'static>], remaining: Vec<AccountInfo<'static>>,
    seeds: &'a [&'b [&'c [u8]]],
) -> CpiContext<'a, 'b, 'c, 'static, T> {
    #[cfg(feature = "modern-context")]
    { CpiContext::new_with_signer(*base[4].key, accounts, seeds).with_remaining_accounts(remaining) }
    #[cfg(not(feature = "modern-context"))]
    { CpiContext::new_with_signer(base[4].clone(), accounts, seeds).with_remaining_accounts(remaining) }
}

pub type Run = (Json, Result<Result<Option<u64>, crate::anchor_lang::error::Error>, String>, crate::track::Log);

pub fn execute<T, F>(ctx: T, base: &[AccountInfo<'static>], call: F) -> Run
where F: FnOnce(T) -> Result<Option<u64>, crate::anchor_lang::error::Error> {
    let before = Json::obj([("cells", cells(base)), ("counts", counts(base)),
        ("infos", input_infos(base))]);
    let (result, log) = crate::track::tracked(|| call(ctx));
    (before, result, log)
}

fn error_json(error: &crate::anchor_lang::error::Error) -> Json {
    match error {
        crate::anchor_lang::error::Error::ProgramError(payload) => {
            let value = match &payload.program_error {
                ProgramError::Custom(code) => Json::obj([("custom", (*code).into())]),
                ProgramError::IncorrectProgramId => "incorrect_program_id".into(),
                ProgramError::InvalidArgument => "invalid_argument".into(),
                ProgramError::InvalidInstructionData => "invalid_instruction_data".into(),
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

fn is_extension(operation: &str) -> bool { operation.ends_with("_initialize") }

fn args_json(case: &Case, ids: &[usize], seeds: &[&[&[u8]]]) -> Json {
    Json::obj([
        ("operation", case.operation.into()), ("mode", case.mode.into()), ("getter", case.getter.into()),
        ("account_ids", Json::arr(ids, |id| (*id).into())), ("remaining", Json::arr([1, 0, 1], Json::from)),
        ("program_index", 4usize.into()), ("amount", case.amount.into()), ("decimals", case.decimals.into()),
        ("authority_type", case.authority_type.into()), ("mint_authority", rec::bytes(key(81).as_ref())),
        ("option1", case.option1.map(|p| rec::bytes(p.as_ref())).unwrap_or(Json::Null)),
        ("option2", case.option2.map(|p| rec::bytes(p.as_ref())).unwrap_or(Json::Null)),
        ("extensions", if case.extensions { Json::arr([0, 27, 27], Json::from) }
            else { Json::arr([7, 12], Json::from) }),
        ("seeds", Json::arr(seeds, |group| Json::arr(*group, |seed| rec::bytes(seed)))),
        ("borsh", case.borsh.into()), ("enum_size", crate::cases::enum_size(case.operation).into()),
    ])
}

fn run_case(case: &Case) -> Record {
    let base: Vec<_> = (0..5).map(|id| account(id + 1,
        if id == 4 { program(case.context_program) }
        else if id == 0 && is_extension(case.operation) { program(case.extension_program) }
        else { key(id + 1) })).collect();
    let remaining = vec![base[1].clone(), base[0].clone(), base[1].clone()];
    let remaining_ptr = remaining.as_ptr() as usize;
    let seed0: &[&[u8]] = &[&[1, 2], &[], &[1, 2]];
    let seed1: &[&[u8]] = &[];
    let seed2: &[&[u8]] = &[&[255]];
    let seeds: &[&[&[u8]]] = if case.empty_seeds { &[] } else { &[seed0, seed1, seed2] };
    let ids: Vec<_> = (0..crate::cases::field_count(case.operation)).map(|i|
        if case.alias && i == 1 { 0 } else { i }).collect();
    let error = if case.mode == "error" {
        #[cfg(not(feature = "modern-context"))]
        { Some(if case.borsh { ProgramError::BorshIoError("owned dependency error".to_string()) }
            else { ProgramError::Custom(77) }) }
        #[cfg(feature = "modern-context")]
        { assert!(!case.borsh); Some(ProgramError::Custom(77)) }
    } else { None };
    #[cfg(not(feature = "modern-context"))]
    let error_string = match &error {
        Some(ProgramError::BorshIoError(text)) => Some(text.as_ptr() as usize), _ => None,
    };
    #[cfg(feature = "modern-context")]
    let error_string = None;
    SCRIPT.with(|cell| *cell.borrow_mut() = Script {
        mode: case.mode.into(), getter: case.getter.into(), error, error_string,
        identities: base.iter().map(|a| Rc::as_ptr(&a.data) as usize).collect(),
        lamports: base.iter().map(|a| Rc::downgrade(&a.lamports)).collect(),
        data_cells: base.iter().map(|a| Rc::downgrade(&a.data)).collect(),
        seed_pointer: seeds.as_ptr() as usize, expected_program: Some(*base[4].key),
        ..Script::default()
    });
    let (before, result, log) = crate::cases::run(case, &base, &ids, remaining, seeds);
    let (calls, getters, metas, data, returned) = SCRIPT.with(|cell| {
        let s = cell.borrow(); (s.calls.clone(), s.getters.clone(), s.metas, s.data, s.returned)
    });
    let free_order: Vec<_> = log.events.iter().filter_map(|(p, allocated)| {
        if *allocated { None } else if *p == metas && metas != 0 { Some("metas") }
        else if *p == data && data != 0 { Some("data") }
        else if *p == remaining_ptr { Some("remaining") }
        else { None }
    }).collect();
    let mut fresh_boxes = 0usize;
    let mut same_string = Json::Null;
    let mut conversion_after_return_free = Json::Null;
    if let Ok(Err(crate::anchor_lang::error::Error::ProgramError(payload))) = &result {
        #[cfg(not(feature = "inline-error"))]
        {
            let pointer = &**payload as *const _ as usize;
            assert!(log.fresh_live.contains(&pointer));
            fresh_boxes = 1;
            if let Some(returned) = returned {
                let released = log.events.iter().rposition(|e| *e == (returned, false)).unwrap();
                let converted = log.events.iter().rposition(|e| *e == (pointer, true)).unwrap();
                conversion_after_return_free = (released < converted).into();
            }
        }
        #[cfg(not(feature = "modern-context"))]
        if let ProgramError::BorshIoError(text) = &payload.program_error {
            let original = SCRIPT.with(|cell| cell.borrow().error_string);
            assert_eq!(original, Some(text.as_ptr() as usize));
            same_string = true.into();
        }
    }
    let heap = if result.is_ok() {
        assert_eq!(log.fresh_live.len(), fresh_boxes, "all temporary allocations are gone");
        Json::obj([("allocations", log.allocs.len().into()), ("frees", log.frees.len().into()),
            ("live", log.fresh_live.len().into())])
    } else { Json::Null };
    let after = Json::obj([
        ("cells", cells(&base)), ("counts", counts(&base)), ("calls", Json::Arr(calls)),
        ("getters", Json::Arr(getters)), ("freed", Json::arr(free_order, Json::from)),
        ("fresh_boxes", fresh_boxes.into()), ("same_string", same_string), ("heap", heap),
        ("returned_freed", returned.map(|p| log.frees.contains(&p).into()).unwrap_or(Json::Null)),
        ("conversion_after_return_free", conversion_after_return_free),
    ]);
    let outcome = match result {
        Ok(value) => rec::returned(match value {
            Ok(value) => rec::ok(value.map(Json::from).unwrap_or(Json::Null)),
            Err(error) => rec::err(error_json(&error)),
        }, after),
        Err(reason) => rec::unwound(reason, after),
    };
    let function = crate::cases::FUNCTIONS.iter().find(|(name, _)| *name == case.operation).unwrap().1;
    Record { id: String::new(), function, generics: vec![], layout: None,
        state: before, args: args_json(case, &ids, seeds), outcome, observed: None }
}

fn selected_cases(operation: &'static str) -> Vec<Case> {
    let baseline = Case::normal(operation);
    let mut cases = vec![baseline.clone()];
    for mode in ["error", "unwind"] {
        cases.push(Case { mode, ..baseline.clone() });
    }
    cases.push(Case { empty_seeds: true, ..baseline.clone() });
    if crate::cases::field_count(operation) > 1 {
        cases.push(Case { alias: true, ..baseline.clone() });
    }
    for amount in [0, u64::MAX] {
        if ["transfer", "burn", "mint_to", "transfer_checked", "burn_checked", "mint_to_checked"].contains(&operation) {
            cases.push(Case { amount, decimals: if amount == 0 { 0 } else { 255 }, ..baseline.clone() });
        }
    }
    #[cfg(not(feature = "modern-context"))]
    cases.push(Case { mode: "error", borsh: true, ..baseline.clone() });
    cases.push(Case { context_program: "wrong", ..baseline.clone() });
    if is_extension(operation) {
        cases.push(Case { extension_program: "wrong", ..baseline.clone() });
    } else if operation != "transfer" && !cfg!(feature = "v0270") {
        cases.push(Case { context_program: "legacy", ..baseline.clone() });
    }
    if ["set_authority", "initialize_mint2", "mint_close_authority_initialize", "permanent_delegate_initialize"].contains(&operation)
        || is_extension(operation) && operation.contains("pointer") || operation == "transfer_hook_initialize" {
        cases.push(Case { option1: None, option2: None, authority_type: 0, ..baseline.clone() });
        cases.push(Case { option1: Some(Pubkey::default()), authority_type: 16, ..baseline.clone() });
        cases.push(Case { option2: Some(Pubkey::default()), ..baseline.clone() });
    }
    if operation == "get_account_data_size" {
        for getter in ["none", "wrong", "short", "long", "unwind"] {
            cases.push(Case { getter, ..baseline.clone() });
        }
        cases.push(Case { extensions: true, ..baseline.clone() });
    }
    cases
}

fn terminal_case(operation: &'static str, getter_terminal: bool) -> Record {
    let ordinary = Case::normal(operation);
    let mut record = run_case(&ordinary);
    let child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--terminal", operation, if getter_terminal { "getter" } else { "invoke" }])
        .output().expect("launch terminal signature provider");
    assert_eq!(child.status.code(), Some(77), "{}", String::from_utf8_lossy(&child.stderr));
    let output = String::from_utf8(child.stdout).expect("terminal observation UTF8");
    let chosen = Case { mode: if getter_terminal { "ok" } else { "terminal" },
        getter: if getter_terminal { "terminal" } else { "good" }, ..ordinary };
    // Inputs are byte-identical to the child. Only its genuinely nonreturning
    // observation supplies the terminal result; no cleanup state is attached.
    if let Json::Obj(ref mut args) = record.args {
        for (name, value) in args {
            if name == "mode" { *value = chosen.mode.into(); }
            if name == "getter" { *value = chosen.getter.into(); }
        }
    }
    record.outcome = Json::Raw(output);
    record
}

pub fn main() {
    rec::init();
    let argv: Vec<_> = std::env::args().collect();
    if argv.get(1).map(String::as_str) == Some("--terminal") {
        let operation = crate::cases::FUNCTIONS.iter().find(|(name, _)| Some(*name) == argv.get(2).map(String::as_str)).unwrap().0;
        let getter = argv.get(3).map(String::as_str) == Some("getter");
        run_case(&Case { mode: if getter { "ok" } else { "terminal" },
            getter: if getter { "terminal" } else { "good" }, ..Case::normal(operation) });
        unreachable!("terminal invocation/getter must not return");
    }
    let mut corpus = Corpus::new(crate::CORPUS, &[("anchor-spl", crate::VERSION)]);
    for (operation, _) in crate::cases::FUNCTIONS {
        for (index, case) in selected_cases(operation).iter().enumerate() {
            let mut record = run_case(case);
            record.id = format!("{operation}/{index:02}/{}", case.mode);
            corpus.push(record);
        }
        let mut terminal = terminal_case(operation, false);
        terminal.id = format!("{operation}/terminal/invoke");
        corpus.push(terminal);
        if *operation == "get_account_data_size" {
            let mut terminal = terminal_case(operation, true);
            terminal.id = format!("{operation}/terminal/getter");
            corpus.push(terminal);
        }
    }
    corpus.write(&rec::out_dir()).expect("write projected token wrapper corpus");
}
