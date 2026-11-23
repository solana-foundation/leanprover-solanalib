//! Exact source calls shared by six independently locked drivers.

use crate::{
    allocator, AccountMeta, Instruction, Pubkey, INSTRUCTION_CLONE, META_CLONE, META_NEW,
    META_READONLY, SYSTEM_FUNCTION,
};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use std::os::unix::process::ExitStatusExt;

pub fn key(start: u8) -> Pubkey {
    let mut bytes = [0; 32];
    bytes[0] = start;
    bytes[31] = start.wrapping_add(1);
    Pubkey::new_from_array(bytes)
}

fn address(key: &Pubkey) -> Json {
    rec::bytes(key.as_ref())
}
fn meta(value: &AccountMeta) -> Json {
    Json::obj([
        ("pubkey", address(&value.pubkey)),
        ("is_signer", value.is_signer.into()),
        ("is_writable", value.is_writable.into()),
    ])
}
fn instruction(value: &Instruction) -> Json {
    Json::obj([
        ("program_id", address(&value.program_id)),
        ("accounts", Json::arr(&value.accounts, meta)),
        ("data", rec::bytes(&value.data)),
    ])
}

fn push(
    corpus: &mut Corpus,
    id: String,
    function: &'static str,
    state: Json,
    args: Json,
    outcome: Json,
    observed: Json,
) {
    corpus.push(Record {
        id,
        function,
        generics: vec![],
        layout: None,
        state,
        args,
        outcome,
        observed: Some(observed),
    });
}

fn allocations(count: usize) -> Json {
    Json::obj([("allocation_calls", count.into())])
}

fn clone_input() -> Instruction {
    Instruction {
        program_id: key(9),
        accounts: vec![
            AccountMeta::new(key(1), true),
            AccountMeta::new_readonly(key(1), false),
        ],
        data: vec![0, 9, 255],
    }
}

fn abort_outcome(operation: &str, ordinal: usize) -> (Json, Json) {
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--allocation-child", operation, &ordinal.to_string()])
        .output()
        .unwrap();
    assert_eq!(
        output.status.signal(),
        Some(6),
        "allocation failure must SIGABRT: {output:?}"
    );
    assert!(output
        .stderr
        .windows(b"instruction-extensions-allocation-failure".len())
        .any(|x| x == b"instruction-extensions-allocation-failure"));
    (
        Json::obj([
            ("exit", "terminated".into()),
            ("reason", "allocation".into()),
        ]),
        Json::obj([
            ("signal", 6u64.into()),
            ("failed_allocation", ordinal.into()),
        ]),
    )
}

pub fn child() -> bool {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(String::as_str) != Some("--allocation-child") {
        return false;
    }
    let ordinal: usize = args[3].parse().unwrap();
    match args[2].as_str() {
        "clone" => {
            let input = clone_input();
            let _ = allocator::measure(ordinal, || input.clone());
        }
        "system" => {
            let args = system_sample();
            let _ = allocator::measure(ordinal, || call_system(&args));
        }
        _ => panic!("unknown allocation operation"),
    }
    panic!("requested allocation was not reached");
}

pub fn record_metadata(corpus: &mut Corpus) {
    for (label, address_value) in [
        ("zero", Pubkey::new_from_array([0; 32])),
        ("pattern", key(0x80)),
        ("ff", Pubkey::new_from_array([255; 32])),
    ] {
        for signer in [false, true] {
            for writable in [false, true] {
                let (value, count) = allocator::measure(0, || {
                    if writable {
                        AccountMeta::new(address_value, signer)
                    } else {
                        AccountMeta::new_readonly(address_value, signer)
                    }
                });
                assert_eq!(count, 0);
                push(
                    corpus,
                    format!("meta/{label}/{signer}/{writable}"),
                    if writable { META_NEW } else { META_READONLY },
                    Json::Null,
                    Json::obj([
                        ("pubkey", address(&address_value)),
                        ("is_signer", signer.into()),
                    ]),
                    rec::returned(meta(&value), Json::Null),
                    allocations(count),
                );
                let before = meta(&value);
                let (copied, count) = allocator::measure(0, || value.clone());
                assert_eq!(count, 0);
                assert_eq!(before, meta(&value));
                push(
                    corpus,
                    format!("meta-clone/{label}/{signer}/{writable}"),
                    META_CLONE,
                    before,
                    Json::empty(),
                    rec::returned(meta(&copied), meta(&value)),
                    allocations(count),
                );
            }
        }
    }
}

pub fn record_clone(corpus: &mut Corpus) {
    for (label, source) in [
        (
            "empty",
            Instruction {
                program_id: key(8),
                accounts: vec![],
                data: vec![],
            },
        ),
        (
            "data-only",
            Instruction {
                program_id: key(0),
                accounts: vec![],
                data: vec![255],
            },
        ),
        (
            "metas-only",
            Instruction {
                program_id: key(255),
                accounts: vec![AccountMeta::new(key(2), false)],
                data: vec![],
            },
        ),
        ("duplicates", clone_input()),
    ] {
        let before = instruction(&source);
        let (mut copied, count) = allocator::measure(0, || source.clone());
        let expected =
            usize::from(!source.accounts.is_empty()) + usize::from(!source.data.is_empty());
        assert_eq!(count, expected);
        assert_eq!(before, instruction(&source));
        assert_eq!(before, instruction(&copied));
        if !copied.accounts.is_empty() {
            assert_ne!(source.accounts.as_ptr(), copied.accounts.as_ptr());
        }
        if !copied.data.is_empty() {
            assert_ne!(source.data.as_ptr(), copied.data.as_ptr());
        }
        let result = instruction(&copied);
        if let Some(first) = copied.accounts.first_mut() {
            first.is_signer = !first.is_signer;
        }
        if let Some(first) = copied.data.first_mut() {
            *first ^= 255;
        }
        assert_eq!(before, instruction(&source));
        push(
            corpus,
            format!("clone/{label}"),
            INSTRUCTION_CLONE,
            before,
            Json::obj([("fail_at", Json::Null)]),
            rec::returned(result, instruction(&source)),
            allocations(count),
        );
    }
    for ordinal in 1..=2 {
        let (outcome, observed) = abort_outcome("clone", ordinal);
        push(
            corpus,
            format!("clone/oom/{ordinal}"),
            INSTRUCTION_CLONE,
            instruction(&clone_input()),
            Json::obj([("fail_at", ordinal.into())]),
            outcome,
            observed,
        );
    }
}

#[cfg(feature = "seeded")]
pub struct SystemArgs {
    from: Pubkey,
    to: Pubkey,
    base: Pubkey,
    seed: String,
    lamports: u64,
    space: u64,
    owner: Pubkey,
}
#[cfg(feature = "prefund")]
pub struct SystemArgs {
    new_account: Pubkey,
    payer: Option<(Pubkey, u64)>,
    space: u64,
    owner: Pubkey,
}

#[cfg(feature = "seeded")]
pub fn system_sample() -> SystemArgs {
    SystemArgs {
        from: key(1),
        to: key(1),
        base: key(1),
        seed: "a\0é".to_string(),
        lamports: 0x0102_0304_0506_0708,
        space: 32,
        owner: key(9),
    }
}
#[cfg(feature = "prefund")]
pub fn system_sample() -> SystemArgs {
    SystemArgs {
        new_account: key(1),
        payer: Some((key(1), 0)),
        space: 32,
        owner: key(9),
    }
}

#[cfg(feature = "seeded")]
pub fn call_system(args: &SystemArgs) -> Instruction {
    crate::create_account_with_seed(
        &args.from,
        &args.to,
        &args.base,
        &args.seed,
        args.lamports,
        args.space,
        &args.owner,
    )
}
#[cfg(feature = "prefund")]
pub fn call_system(args: &SystemArgs) -> Instruction {
    crate::create_account_allow_prefund(
        &args.new_account,
        args.payer.as_ref().map(|(key, lamports)| (key, *lamports)),
        args.space,
        &args.owner,
    )
}

#[cfg(feature = "seeded")]
fn system_args(args: &SystemArgs, fail_at: Json) -> Json {
    Json::obj([
        ("from", address(&args.from)),
        ("to", address(&args.to)),
        ("base", address(&args.base)),
        ("seed", rec::bytes(args.seed.as_bytes())),
        ("lamports", args.lamports.into()),
        ("space", args.space.into()),
        ("owner", address(&args.owner)),
        ("fail_at", fail_at),
    ])
}
#[cfg(feature = "prefund")]
fn system_args(args: &SystemArgs, fail_at: Json) -> Json {
    Json::obj([
        ("new_account", address(&args.new_account)),
        (
            "payer",
            rec::option(&args.payer, |(key, lamports)| {
                Json::obj([("pubkey", address(key)), ("lamports", (*lamports).into())])
            }),
        ),
        ("space", args.space.into()),
        ("owner", address(&args.owner)),
        ("fail_at", fail_at),
    ])
}

fn record_system_case(corpus: &mut Corpus, id: String, args: SystemArgs, expected: usize) {
    let (value, count) = allocator::measure(0, || call_system(&args));
    assert_eq!(count, expected, "allocation order changed for {id}");
    push(
        corpus,
        id,
        SYSTEM_FUNCTION,
        Json::Null,
        system_args(&args, Json::Null),
        rec::returned(instruction(&value), Json::Null),
        allocations(count),
    );
}

#[cfg(feature = "seeded")]
pub fn record_system(corpus: &mut Corpus) {
    for (label, seed) in [
        ("empty", String::new()),
        ("nul-utf8", "a\0é".to_string()),
        ("33", "x".repeat(33)),
        ("255", "z".repeat(255)),
    ] {
        for (amount_label, lamports) in [
            ("zero", 0),
            ("pattern", 0x0102_0304_0506_0708),
            ("max", u64::MAX),
        ] {
            let mut args = system_sample();
            args.seed = seed.clone();
            args.lamports = lamports;
            args.space = if lamports == u64::MAX { u64::MAX } else { 32 };
            let allocations = 2 + usize::from(!args.seed.is_empty());
            record_system_case(
                corpus,
                format!("seed/{label}/{amount_label}/alias"),
                args,
                allocations,
            );
        }
    }
    let mut args = system_sample();
    args.to = key(2);
    args.base = key(3);
    args.owner = Pubkey::new_from_array([0; 32]);
    record_system_case(corpus, "seed/distinct".into(), args, 3);
    record_system_aborts(corpus);
}

#[cfg(feature = "prefund")]
pub fn record_system(corpus: &mut Corpus) {
    for (label, payer) in [
        ("none", None),
        ("alias-zero", Some((key(1), 0))),
        ("distinct-one", Some((key(2), 1))),
        ("pattern", Some((key(2), 0x0102_0304_0506_0708))),
        ("max", Some((key(1), u64::MAX))),
    ] {
        for (space_label, space) in [("zero", 0), ("max", u64::MAX)] {
            let args = SystemArgs {
                new_account: key(1),
                payer,
                space,
                owner: key(9),
            };
            record_system_case(
                corpus,
                format!("prefund/{label}/{space_label}"),
                args,
                2 + usize::from(payer.is_some()),
            );
        }
    }
    record_system_aborts(corpus);
}

fn record_system_aborts(corpus: &mut Corpus) {
    for ordinal in 1..=3 {
        let (outcome, observed) = abort_outcome("system", ordinal);
        push(
            corpus,
            format!("system/oom/{ordinal}"),
            SYSTEM_FUNCTION,
            Json::Null,
            system_args(&system_sample(), ordinal.into()),
            outcome,
            observed,
        );
    }
}
