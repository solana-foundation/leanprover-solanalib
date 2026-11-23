//! anchor-spl 1.0.2: `token::Mint` and `token_interface::Mint` dereference,
//! `token::accessor::amount` and `token::transfer`.

use anchor_lang::prelude::*;
use anchor_spl::token::Transfer;
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim as shim;

use crate::accounts::{parse_raw, PROGRAM};
use crate::enc;
use crate::misc::seeds_json;
use crate::world::{self, account, input, pk, World};

fn push(c: &mut Corpus, id: String, function: &'static str, generics: Vec<(&'static str, String)>, state: Json, args: Json, outcome: Json) {
    c.push(Record { id, function, generics, layout: None, state, args, outcome, observed: None });
}

fn no_syscalls() -> (&'static str, Json) {
    ("syscalls", shim::Script::new(vec![]).state_before())
}

// ---------------------------------------------------------------------------
// Mint dereference
// ---------------------------------------------------------------------------

struct MintFields {
    authority: Option<[u8; 32]>,
    supply: u64,
    decimals: u8,
    initialized: bool,
    freeze: Option<[u8; 32]>,
}

fn coption(k: &Option<[u8; 32]>) -> Vec<u8> {
    match k {
        Some(k) => [vec![1, 0, 0, 0], k.to_vec()].concat(),
        None => vec![0; 36],
    }
}

/// The 82-byte base mint encoding (spl-token `Mint::pack`).
fn mint_bytes(m: &MintFields) -> Vec<u8> {
    [coption(&m.authority), m.supply.to_le_bytes().to_vec(), vec![m.decimals, m.initialized as u8], coption(&m.freeze)].concat()
}

fn opt_key(k: &Option<[u8; 32]>) -> Json {
    match k {
        Some(k) => rec::bytes(k),
        None => Json::Null,
    }
}

fn mint_json(m: &MintFields) -> Json {
    Json::obj([("mint_authority", opt_key(&m.authority)), ("supply", m.supply.into()), ("decimals", m.decimals.into()),
        ("is_initialized", m.initialized.into()), ("freeze_authority", opt_key(&m.freeze))])
}

fn coption_json(k: &anchor_lang::solana_program::program_option::COption<Pubkey>) -> Json {
    match k {
        anchor_lang::solana_program::program_option::COption::Some(k) => enc::key(k),
        anchor_lang::solana_program::program_option::COption::None => Json::Null,
    }
}

const TOKEN_MINT_DEREF: &str = "<anchor_spl::token::Mint as core::ops::deref::Deref>::deref";
const INTERFACE_MINT_DEREF: &str = "<anchor_spl::token_interface::Mint as core::ops::deref::Deref>::deref";

fn record_mint_deref(c: &mut Corpus) {
    let mints = vec![
        ("both_authorities", MintFields { authority: Some(pk(1)), supply: 1_000_000, decimals: 6, initialized: true, freeze: Some(pk(2)) }),
        ("no_authorities", MintFields { authority: None, supply: 0, decimals: 0, initialized: true, freeze: None }),
        ("max_supply", MintFields { authority: Some(pk(3)), supply: u64::MAX, decimals: 255, initialized: true, freeze: None }),
    ];
    for (label, m) in mints {
        let bytes = mint_bytes(&m);
        for (function, interface) in [(TOKEN_MINT_DEREF, false), (INTERFACE_MINT_DEREF, true)] {
            let bytes_ = bytes.clone();
            let out = shim::case(&shim::Script::new(vec![]), move || {
                let r = if interface {
                    let w = anchor_spl::token_interface::Mint::try_deserialize_unchecked(&mut &bytes_[..]).ok().expect("mint");
                    rec::catch(move || { let m = &*w; Json::obj([("mint_authority", coption_json(&m.mint_authority)), ("supply", m.supply.into()),
                        ("decimals", m.decimals.into()), ("is_initialized", m.is_initialized.into()), ("freeze_authority", coption_json(&m.freeze_authority))]) })
                } else {
                    let w = anchor_spl::token::Mint::try_deserialize_unchecked(&mut &bytes_[..]).ok().expect("mint");
                    rec::catch(move || { let m = &*w; Json::obj([("mint_authority", coption_json(&m.mint_authority)), ("supply", m.supply.into()),
                        ("decimals", m.decimals.into()), ("is_initialized", m.is_initialized.into()), ("freeze_authority", coption_json(&m.freeze_authority))]) })
                };
                match r {
                    Ok(v) => rec::returned(v, Json::obj([("syscalls", shim::state())])),
                    Err(reason) => rec::unwound(reason, Json::obj([("syscalls", shim::state())])),
                }
            });
            let state = Json::obj([("mint_data", rec::bytes(&bytes)), no_syscalls()]);
            let args = Json::obj([("mint", mint_json(&m))]);
            push(c, format!("{}/{label}", if interface { "interface_mint_deref" } else { "mint_deref" }), function, vec![], state, args, parse_raw(&out));
        }
    }
}

// ---------------------------------------------------------------------------
// accessor::amount
// ---------------------------------------------------------------------------

const AMOUNT: &str = "anchor_spl::token::accessor::amount";

fn token_account(amount: u64, len: usize) -> Vec<u8> {
    let mut d: Vec<u8> = (0..len.max(72)).map(|i| (i % 251) as u8).collect();
    d[64..72].copy_from_slice(&amount.to_le_bytes());
    d.truncate(len);
    d
}

fn record_amount(c: &mut Corpus) {
    let cases: Vec<(&str, Vec<u8>, Vec<(usize, &'static str)>)> = vec![
        ("token_account", token_account(123_456_789, 165), vec![]),
        ("max", token_account(u64::MAX, 165), vec![]),
        ("exact_72", token_account(5, 72), vec![]),
        ("short_71", token_account(5, 71), vec![]),
        ("short_64", token_account(5, 64), vec![]),
        ("empty", vec![], vec![]),
        ("data_borrowed", token_account(9, 165), vec![(1, "exclusive")]),
        ("data_shared", token_account(9, 165), vec![(1, "shared")]),
        ("lamports_borrowed", token_account(9, 165), vec![(0, "exclusive")]),
    ];
    for (label, d, borrows) in cases {
        let inp = input(vec![account(pk(1), PROGRAM, 100, d, false, true)]);
        let state = world::state_before(&inp, &borrows, vec![no_syscalls()]);
        let inp_ = inp.clone();
        let borrows_ = borrows.clone();
        let out = shim::case(&shim::Script::new(vec![]), move || {
            let w: &'static World = Box::leak(Box::new(World::new(&inp_)));
            let held = world::hold(w, &borrows_);
            let r = rec::catch(|| anchor_spl::token::accessor::amount(w.info(0)));
            let after = w.state(vec![]);
            drop(held);
            match r {
                Ok(res) => rec::returned(match &res { Ok(v) => rec::ok((*v).into()), Err(e) => rec::err(enc::error_value(e)) }, after),
                Err(reason) => rec::unwound(reason, after),
            }
        });
        push(c, format!("amount/{label}"), AMOUNT, vec![], state, Json::obj([("account", 0.into())]), parse_raw(&out));
    }
}

// ---------------------------------------------------------------------------
// token::transfer
// ---------------------------------------------------------------------------

const TRANSFER_FN: &str = "anchor_spl::token::transfer";

/// Decoder of `sol_invoke_signed_rust`: the stable instruction, the account
/// infos (the `AccountInfo` layout in this crate) and the signer seeds.
fn decode_invoke(ix: *const u8, infos: *const u8, infos_len: u64, seeds: *const u8, seeds_len: u64) -> Json {
    #[repr(C)]
    struct StableVec<T> { addr: u64, cap: u64, len: u64, _t: std::marker::PhantomData<T> }
    #[repr(C)]
    struct StableInstruction { accounts: StableVec<anchor_lang::solana_program::instruction::AccountMeta>, data: StableVec<u8>, program_id: Pubkey }
    unsafe {
        let ix = &*(ix as *const StableInstruction);
        let metas = std::slice::from_raw_parts(ix.accounts.addr as *const anchor_lang::solana_program::instruction::AccountMeta, ix.accounts.len as usize);
        let data = std::slice::from_raw_parts(ix.data.addr as *const u8, ix.data.len as usize);
        let infos = std::slice::from_raw_parts(infos as *const AccountInfo, infos_len as usize);
        let w = crate::spl::current_world();
        Json::obj([
            ("instruction", Json::obj([
                ("program_id", enc::key(&ix.program_id)),
                ("accounts", Json::arr(metas.iter(), |m| Json::obj([("pubkey", enc::key(&m.pubkey)), ("is_signer", m.is_signer.into()), ("is_writable", m.is_writable.into())]))),
                ("data", rec::bytes(data)),
            ])),
            ("account_infos", Json::arr(infos.iter(), |i| w.info_json(i))),
            ("signers_seeds", shim::signer_seeds(seeds, seeds_len)),
        ])
    }
}

thread_local! {
    static WORLD: std::cell::Cell<Option<&'static World>> = const { std::cell::Cell::new(None) };
}

fn current_world() -> &'static World {
    WORLD.with(|w| w.get().expect("no world"))
}

/// One `transfer` case. `borrows` are held on the world accounts across the
/// call: `invoke_signed` from solana-invoke probes the `RefCell`s of every account
/// named by the instruction before the syscall.
fn transfer_case(c: &mut Corpus, id: String, seeds: &'static [&'static [&'static [u8]]], ret: u64, amount: u64,
                 borrows: &[(usize, &'static str)]) {
    let inp = input(vec![
        account(pk(1), pk(0x06), 1, vec![0; 165], false, true),
        account(pk(2), pk(0x06), 1, vec![0; 165], false, true),
        account(pk(3), pk(0), 1, vec![], true, false),
    ]);
    let script = shim::Script::new(vec![shim::Reply::new("sol_invoke_signed_rust", ret)]);
    let inp_ = inp.clone();
    let borrows_ = borrows.to_vec();
    let out = shim::case(&script, move || {
        let w: &'static World = Box::leak(Box::new(World::new(&inp_)));
        WORLD.with(|c| c.set(Some(w)));
        shim::set_invoke_rust_decoder(decode_invoke);
        let accounts = Transfer { from: w.info(0).clone(), to: w.info(1).clone(), authority: w.info(2).clone() };
        let ctx = CpiContext::new_with_signer(Pubkey::new_from_array(pk(0x0c)), accounts, seeds);
        let held = world::hold(w, &borrows_);
        let before = crate::accounts::rc_counts(w);
        let r = rec::catch(|| anchor_spl::token::transfer(ctx, amount));
        let after = w.state(vec![("syscalls", shim::state()), ("counts", crate::accounts::rc_counts(w)), ("counts_before", before)]);
        drop(held);
        match r {
            Ok(res) => rec::returned(match &res { Ok(()) => rec::ok(Json::Null), Err(e) => rec::err(enc::error_value(e)) }, after),
            Err(reason) => rec::unwound(reason, after),
        }
    });
    let out = parse_raw(&out);
    // `Rc` strong counts with the context built (it holds a clone of each account).
    let counts = crate::accounts::field(&crate::accounts::field(&out, "state"), "counts_before");
    let out = strip_counts_before(out);
    let state = world::state_before(&inp, borrows, vec![("syscalls", script.state_before()), ("counts", counts)]);
    let args = Json::obj([
        ("context", Json::obj([
            ("accounts", Json::obj([("from", 0.into()), ("to", 1.into()), ("authority", 2.into())])),
            ("program_id", rec::bytes(&pk(0x0c))),
            ("signer_seeds", seeds_json(seeds)),
        ])),
        ("amount", amount.into()),
    ]);
    push(c, id, TRANSFER_FN, vec![], state, args, out);
}

fn record_transfer(c: &mut Corpus) {
    let seed_sets: Vec<(&str, &'static [&'static [&'static [u8]]])> = vec![
        ("unsigned", &[]),
        ("signed", &[&[b"authority", &[254]]]),
    ];
    let returns: Vec<(&str, u64)> = vec![("ok", 0), ("custom", 1), ("insufficient_funds", 6 << 32), ("custom_zero", 1 << 32), ("unknown_high", 99 << 32)];
    for (sl, seeds) in &seed_sets {
        for (rl, ret) in &returns {
            for amount in [0u64, 1_000_000, u64::MAX] {
                if amount != 1_000_000 && (*rl != "ok" || *sl != "unsigned") {
                    continue;
                }
                transfer_case(c, format!("transfer/{sl}/{rl}/{amount}"), seeds, *ret, amount, &[]);
            }
        }
    }
    // Accounts borrowed across the call (cells: lamports 2k, data 2k + 1 of account k =
    // from 0, to 1, authority 2). Writable metas need both cells free; the readonly
    // authority needs no exclusive borrow.
    let borrowed: Vec<(&str, Vec<(usize, &'static str)>)> = vec![
        ("from_data_shared", vec![(1, "shared")]),
        ("from_data_exclusive", vec![(1, "exclusive")]),
        ("from_lamports_shared", vec![(0, "shared")]),
        ("to_lamports_exclusive", vec![(2, "exclusive")]),
        ("authority_data_shared", vec![(5, "shared")]),
        ("authority_lamports_shared", vec![(4, "shared")]),
        ("authority_data_exclusive", vec![(5, "exclusive")]),
        ("authority_lamports_exclusive", vec![(4, "exclusive")]),
    ];
    for (label, borrows) in borrowed {
        transfer_case(c, format!("transfer/borrowed/{label}"), &[], 0, 1_000_000, &borrows);
    }
}

/// Move the counts read before the call from the outcome state to the record state.
fn strip_counts_before(out: Json) -> Json {
    match out {
        Json::Obj(fields) => Json::Obj(fields.into_iter().map(|(k, v)| {
            if k == "state" {
                match v {
                    Json::Obj(sf) => (k, Json::Obj(sf.into_iter().filter(|(sk, _)| sk != "counts_before").collect())),
                    other => (k, other),
                }
            } else {
                (k, v)
            }
        }).collect()),
        other => other,
    }
}

pub fn record_all(c: &mut Corpus) {
    record_mint_deref(c);
    record_amount(c);
    record_transfer(c);
}
