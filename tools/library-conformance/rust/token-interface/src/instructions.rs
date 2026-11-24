//! Program identities, the program-ID check and the instruction constructors
//! of spl-token-interface 2.0.0 and spl-token-2022-interface 3.1.1.
//!
//! Each constructor call records its arguments, its `Result<Instruction,
//! ProgramError>` and, as the state after the call, the fresh allocations and
//! deallocations it performed (see `common::counted`). Program identities
//! cover both Token programs and near misses that differ in one byte.

use crate::common::{counted, heap, k, key, result, Selection};
use conformance_recorder::{bytes, catch, returned, unwound, Corpus, Json, Record};
use solana_address::Address;
use solana_instruction::Instruction;
use solana_pubkey::Pubkey;

const LEGACY: [u8; 32] = spl_token_interface::ID.to_bytes();
const TOKEN_2022: [u8; 32] = spl_token_2022_interface::ID.to_bytes();

fn flip(mut b: [u8; 32], i: usize) -> [u8; 32] {
    b[i] ^= 1;
    b
}

/// Program identities: both Token programs, the System program (all zero),
/// one-byte near misses of each Token program and all-0xff.
fn programs() -> Vec<(&'static str, [u8; 32])> {
    vec![
        ("legacy", LEGACY),
        ("token2022", TOKEN_2022),
        ("zero", [0; 32]),
        ("legacy_last_flipped", flip(LEGACY, 31)),
        ("token2022_first_flipped", flip(TOKEN_2022, 0)),
        ("ones", [0xff; 32]),
    ]
}

/// Signer lists: none, one, a repeated key, three, and twelve (one more than
/// the multisig maximum; the constructors impose no limit).
fn signer_sets() -> Vec<(&'static str, Vec<[u8; 32]>)> {
    vec![
        ("none", vec![]),
        ("one", vec![k(40)]),
        ("repeated", vec![k(40), k(40)]),
        ("three", vec![k(41), k(42), k(41)]),
        ("twelve", (50..62).map(k).collect()),
    ]
}

const AMOUNTS: [u64; 5] = [0, 1, 513, 1 << 32, u64::MAX];
const DECIMALS: [u8; 4] = [0, 6, 9, 255];

fn instruction(ix: &Instruction) -> Json {
    Json::obj([
        ("program_id", key(ix.program_id.as_ref())),
        (
            "accounts",
            Json::arr(ix.accounts.iter(), |m| {
                Json::obj([
                    ("pubkey", key(m.pubkey.as_ref())),
                    ("is_signer", m.is_signer.into()),
                    ("is_writable", m.is_writable.into()),
                ])
            }),
        ),
        ("data", bytes(&ix.data)),
    ])
}

fn keys(ks: &[[u8; 32]]) -> Json {
    Json::arr(ks.iter(), |b| key(b))
}

/// A constructor call: counts its allocations; a panic would be recorded as
/// an unwind (the models admit none).
fn constructor(
    f: impl FnOnce() -> Result<Instruction, solana_program_error::ProgramError>,
) -> (bool, Json) {
    let (r, allocations, deallocations) = counted(|| catch(f));
    match r {
        Ok(r) => (r.is_ok(), returned(result(&r, instruction), heap(allocations, deallocations))),
        Err(reason) => (false, unwound(reason, heap(allocations, deallocations))),
    }
}

/// Selection class of a constructor case: accepted cases of the crate
/// program by argument shape, of the other accepted program as one class;
/// rejected cases by whether the program is a Token program.
fn class(ok: bool, pname: &str, shape: &str, own: &str) -> String {
    if ok && pname == own {
        format!("ok/{pname}/{shape}")
    } else if ok {
        format!("ok/{pname}")
    } else if pname == "legacy" || pname == "token2022" {
        format!("rejected/{pname}")
    } else {
        "rejected/other".into()
    }
}

fn offer(sel: &mut Selection, class: String, id: String, function: &'static str, args: Json, outcome: Json) {
    sel.offer(class, Record {
        id,
        function,
        generics: vec![],
        layout: None,
        state: Json::Null,
        args,
        outcome,
        observed: None,
    });
}

fn record(c: &mut Corpus, id: String, function: &'static str, args: Json, outcome: Json) {
    c.push(Record {
        id,
        function,
        generics: vec![],
        layout: None,
        state: Json::Null,
        args,
        outcome,
        observed: None,
    });
}

pub fn legacy(c: &mut Corpus) {
    let id = spl_token_interface::id();
    record(c, "id".into(), "spl_token_interface::id", Json::Null, returned(key(id.as_ref()), Json::Null));

    let pk = |b: &[u8; 32]| Pubkey::new_from_array(*b);
    let mut init = Selection::new();
    let mut transfer = Selection::new();
    for (pname, program) in programs() {
        for (shape, account, mint, owner) in
            [("distinct", k(1), k(2), k(3)), ("aliased", program, program, program)]
        {
            let args = Json::obj([
                ("program_id", key(&program)),
                ("account", key(&account)),
                ("mint", key(&mint)),
                ("owner", key(&owner)),
            ]);
            let (ok, outcome) = constructor(|| {
                spl_token_interface::instruction::initialize_account3(
                    &pk(&program),
                    &pk(&account),
                    &pk(&mint),
                    &pk(&owner),
                )
            });
            offer(
                &mut init,
                class(ok, pname, shape, "legacy"),
                format!("initialize_account3/{pname}/{shape}"),
                "spl_token_interface::instruction::initialize_account3",
                args,
                outcome,
            );
        }
        for (i, (sname, signers)) in signer_sets().into_iter().enumerate() {
            let amounts: Vec<u64> =
                if pname == "legacy" { AMOUNTS.to_vec() } else { vec![AMOUNTS[i % AMOUNTS.len()]] };
            for amount in amounts {
                let args = Json::obj([
                    ("program_id", key(&program)),
                    ("source", key(&k(1))),
                    ("destination", key(&k(2))),
                    ("authority", key(&k(3))),
                    ("signers", keys(&signers)),
                    ("amount", amount.into()),
                ]);
                let signer_keys: Vec<Pubkey> = signers.iter().map(pk).collect();
                let signer_refs: Vec<&Pubkey> = signer_keys.iter().collect();
                let (ok, outcome) = constructor(|| {
                    spl_token_interface::instruction::transfer(
                        &pk(&program),
                        &pk(&k(1)),
                        &pk(&k(2)),
                        &pk(&k(3)),
                        &signer_refs,
                        amount,
                    )
                });
                offer(
                    &mut transfer,
                    class(ok, pname, sname, "legacy"),
                    format!("transfer/{pname}/{sname}/{amount}"),
                    "spl_token_interface::instruction::transfer",
                    args,
                    outcome,
                );
            }
        }
    }
    init.into_corpus(c);
    transfer.into_corpus(c);
}

pub fn token_2022(c: &mut Corpus) {
    let id = spl_token_2022_interface::id();
    record(c, "id".into(), "spl_token_2022_interface::id", Json::Null, returned(key(id.as_ref()), Json::Null));

    let ad = |b: &[u8; 32]| Address::new_from_array(*b);
    let mut check = Selection::new();
    let mut init = Selection::new();
    let mut close = Selection::new();
    let mut withdraw = Selection::new();
    let mut checked = Selection::new();
    for (pname, program) in programs() {
        let r = catch(|| spl_token_2022_interface::check_spl_token_program_account(&ad(&program)));
        let (ok, outcome) = match r {
            Ok(r) => (r.is_ok(), returned(result(&r, |_| Json::Null), Json::Null)),
            Err(reason) => (false, unwound(reason, Json::Null)),
        };
        // The check has no further shape: keep each accepted program and both
        // ends of the rejected ones.
        offer(
            &mut check,
            class(ok, pname, "-", "token2022"),
            format!("check_spl_token_program_account/{pname}"),
            "spl_token_2022_interface::check_spl_token_program_account",
            Json::obj([("program_id", key(&program))]),
            outcome,
        );

        for (shape, account, mint, owner) in
            [("distinct", k(1), k(2), k(3)), ("aliased", program, program, program)]
        {
            let args = Json::obj([
                ("program_id", key(&program)),
                ("account", key(&account)),
                ("mint", key(&mint)),
                ("owner", key(&owner)),
            ]);
            let (ok, outcome) = constructor(|| {
                spl_token_2022_interface::instruction::initialize_account3(
                    &ad(&program),
                    &ad(&account),
                    &ad(&mint),
                    &ad(&owner),
                )
            });
            offer(
                &mut init,
                class(ok, pname, shape, "token2022"),
                format!("initialize_account3/{pname}/{shape}"),
                "spl_token_2022_interface::instruction::initialize_account3",
                args,
                outcome,
            );
        }

        for (sname, signers) in signer_sets() {
            let signer_keys: Vec<Address> = signers.iter().map(ad).collect();
            let signer_refs: Vec<&Address> = signer_keys.iter().collect();
            let authority_args = Json::obj([
                ("program_id", key(&program)),
                ("source", key(&k(1))),
                ("destination", key(&k(2))),
                ("authority", key(&k(3))),
                ("signers", keys(&signers)),
            ]);
            let (ok, outcome) = constructor(|| {
                spl_token_2022_interface::instruction::close_account(
                    &ad(&program),
                    &ad(&k(1)),
                    &ad(&k(2)),
                    &ad(&k(3)),
                    &signer_refs,
                )
            });
            offer(
                &mut close,
                class(ok, pname, sname, "token2022"),
                format!("close_account/{pname}/{sname}"),
                "spl_token_2022_interface::instruction::close_account",
                authority_args.clone(),
                outcome,
            );
            let (ok, outcome) = constructor(|| {
                spl_token_2022_interface::instruction::withdraw_excess_lamports(
                    &ad(&program),
                    &ad(&k(1)),
                    &ad(&k(2)),
                    &ad(&k(3)),
                    &signer_refs,
                )
            });
            offer(
                &mut withdraw,
                class(ok, pname, sname, "token2022"),
                format!("withdraw_excess_lamports/{pname}/{sname}"),
                "spl_token_2022_interface::instruction::withdraw_excess_lamports",
                authority_args,
                outcome,
            );
        }

        for (i, (sname, signers)) in signer_sets().into_iter().enumerate() {
            let signer_keys: Vec<Address> = signers.iter().map(ad).collect();
            let signer_refs: Vec<&Address> = signer_keys.iter().collect();
            let pairs: Vec<(u64, u8)> = if pname == "token2022" {
                // Boundary amounts; the last case carries the maximum decimals byte.
                vec![(0, 0), (1, 6), (513, 9), (1 << 32, 6), (u64::MAX, 255)]
            } else {
                vec![(AMOUNTS[i % AMOUNTS.len()], DECIMALS[i % DECIMALS.len()])]
            };
            for (amount, decimals) in pairs {
                let args = Json::obj([
                    ("program_id", key(&program)),
                    ("source", key(&k(1))),
                    ("mint", key(&k(4))),
                    ("destination", key(&k(2))),
                    ("authority", key(&k(3))),
                    ("signers", keys(&signers)),
                    ("amount", amount.into()),
                    ("decimals", decimals.into()),
                ]);
                let (ok, outcome) = constructor(|| {
                    spl_token_2022_interface::instruction::transfer_checked(
                        &ad(&program),
                        &ad(&k(1)),
                        &ad(&k(4)),
                        &ad(&k(2)),
                        &ad(&k(3)),
                        &signer_refs,
                        amount,
                        decimals,
                    )
                });
                offer(
                    &mut checked,
                    class(ok, pname, sname, "token2022"),
                    format!("transfer_checked/{pname}/{sname}/{amount}/{decimals}"),
                    "spl_token_2022_interface::instruction::transfer_checked",
                    args,
                    outcome,
                );
            }
        }
    }
    check.into_corpus(c);
    init.into_corpus(c);
    close.into_corpus(c);
    withdraw.into_corpus(c);
    checked.into_corpus(c);
}
