//! pinocchio-token-2022 0.3.1 checked CPI wrappers: `TransferChecked::invoke`,
//! `TransferChecked::invoke_signed` and `CloseAccount::invoke_signed`. They
//! check the borrow state of each writable account, initialize the CPI accounts and
//! call `sol_invoke_signed_c`, which the shim logs and answers.

use crate::common::*;
use conformance_accounts::Account;
use conformance_recorder::{self as rec, Corpus, Json};
use conformance_shim::{self as shim, Script};
use pinocchio_token_2022::instructions::{CloseAccount, TransferChecked};
use solana_account_view::{AccountView, Ref, RefMut};
use solana_address::Address;
use solana_instruction_view::cpi::{Seed, Signer};

const INVOKE: &str = "pinocchio_token_2022::instructions::transfer_checked::TransferChecked::<'_, '_>::invoke";
const INVOKE_SIGNED: &str = "pinocchio_token_2022::instructions::transfer_checked::TransferChecked::<'_, '_>::invoke_signed";
const CLOSE: &str = "pinocchio_token_2022::instructions::close_account::CloseAccount::<'_, '_>::invoke_signed";

/// Accounts: 0 source, 1 mint, 2 destination, 3 authority, 4 spare.
fn world_accounts() -> Vec<Account> {
    let token = pinocchio_token_2022::ID.to_bytes();
    let mut v = vec![
        account(120, token, bytes(120, 4)),
        account(121, token, bytes(121, 2)),
        account(122, token, bytes(122, 3)),
        account(123, [0; 32], vec![]),
        account(124, key(7), bytes(124, 1)),
    ];
    v[1].is_writable = false;
    v[3].is_signer = true;
    v[3].is_writable = false;
    v[4].executable = true;
    v[4].is_signer = true;
    v
}

#[derive(Clone, Default)]
struct Held {
    shared: Vec<usize>,
    exclusive: Vec<usize>,
}

#[derive(Clone)]
enum Call {
    Transfer { from: usize, mint: usize, to: usize, authority: usize, amount: u64, decimals: u8, signed: bool },
    Close { account: usize, destination: usize, authority: usize },
}

fn transfer(signed: bool) -> Call {
    Call::Transfer { from: 0, mint: 1, to: 2, authority: 3, amount: 42_000_000, decimals: 9, signed }
}

fn close() -> Call {
    Call::Close { account: 0, destination: 2, authority: 3 }
}

fn case(c: &mut Corpus, id: &str, call: Call, program: [u8; 32], held: Held, signers: Vec<Vec<Vec<u8>>>,
        script: Script) {
    raw_case(c, id, call, program, held, signers, script, &[]);
}

/// A case whose accounts carry the given raw header bytes (noncanonical flag
/// bytes and a nonzero first padding byte).
#[allow(clippy::too_many_arguments)]
fn raw_case(c: &mut Corpus, id: &str, call: Call, program: [u8; 32], held: Held, signers: Vec<Vec<Vec<u8>>>,
            script: Script, headers: &[(usize, [u8; 4])]) {
    let mut used: Vec<usize> = match &call {
        Call::Transfer { from, mint, to, authority, .. } => vec![*from, *mint, *to, *authority],
        Call::Close { account, destination, authority } => vec![*account, *destination, *authority],
    };
    used.extend(&held.shared);
    used.extend(&held.exclusive);
    let last = used.into_iter().max().unwrap();
    let mut world = World::new(world_accounts().into_iter().take(last + 1).collect());
    for &(j, h) in headers {
        world.set_raw_header(j, h);
    }
    let world = world;
    let mut exclusive_views: Vec<AccountView> = held.exclusive.iter().map(|&j| world.views[j].clone()).collect();
    let _shared: Vec<Ref<[u8]>> = held.shared.iter().map(|&j| world.views[j].try_borrow().unwrap()).collect();
    let _exclusive: Vec<RefMut<[u8]>> = exclusive_views.iter_mut().map(|v| v.try_borrow_mut().unwrap()).collect();
    let before = state(&world, script.state_before(), vec![]);
    let seeds_json = Json::arr(signers.iter(), |s| Json::arr(s.iter(), |b| rec::bytes(b)));
    let program_id = Address::new_from_array(program);
    let (function, args) = match &call {
        Call::Transfer { from, mint, to, authority, amount, decimals, signed } => {
            let mut a = vec![("program_id", rec::bytes(&program)), ("from", (*from).into()), ("mint", (*mint).into()),
                             ("to", (*to).into()), ("authority", (*authority).into()), ("amount", (*amount).into()),
                             ("decimals", (*decimals).into())];
            if *signed {
                a.push(("signers", seeds_json));
            } else {
                assert!(signers.is_empty());
            }
            (if *signed { INVOKE_SIGNED } else { INVOKE }, a)
        }
        Call::Close { account, destination, authority } => (CLOSE, vec![
            ("program_id", rec::bytes(&program)), ("account", (*account).into()),
            ("destination", (*destination).into()), ("authority", (*authority).into()), ("signers", seeds_json)]),
    };
    let args = Json::Obj(args.into_iter().map(|(k, v)| (k.to_string(), v)).collect());
    let outcome = shim::case(&script, || {
        let v = &world.views;
        let seeds: Vec<Vec<Seed>> = signers.iter().map(|s| s.iter().map(|b| Seed::from(b.as_slice())).collect()).collect();
        let signer_values: Vec<Signer> = seeds.iter().map(|s| Signer::from(s.as_slice())).collect();
        let r = match &call {
            Call::Transfer { from, mint, to, authority, amount, decimals, signed } => {
                let t = TransferChecked { from: &v[*from], mint: &v[*mint], to: &v[*to], authority: &v[*authority],
                                          amount: *amount, decimals: *decimals, token_program: &program_id };
                if *signed { t.invoke_signed(&signer_values) } else { t.invoke() }
            }
            Call::Close { account, destination, authority } => {
                CloseAccount { account: &v[*account], destination: &v[*destination], authority: &v[*authority],
                               token_program: &program_id }
                    .invoke_signed(&signer_values)
            }
        };
        rec::returned(result_json(&r, |_| Json::Null), after(&world, vec![]))
    });
    c.push(record(format!("{id}"), function, vec![], before, args, outcome));
}

/// Case selection: per wrapper, a free call (supplied
/// program id), seeds with another program id, an ignored nonzero return code,
/// a callee failure, a borrowed first writable account (shared) and a borrowed
/// destination (exclusive), borrowed readonly accounts (not checked), and
/// aliased accounts with and without a borrow.
pub fn record_all(c: &mut Corpus) {
    let token = pinocchio_token_2022::ID.to_bytes();
    let none = Held::default();
    let shared = |j: usize| Held { shared: vec![j], exclusive: vec![] };
    let exclusive = |j: usize| Held { shared: vec![], exclusive: vec![j] };
    let seeds = vec![vec![b"escrow".to_vec(), key(9).to_vec(), vec![253]], vec![], vec![vec![]]];

    for (kind, call) in [("transfer_invoke", transfer(false)), ("transfer_invoke_signed", transfer(true)),
                         ("close_invoke_signed", close())] {
        let signed = !matches!(call, Call::Transfer { signed: false, .. });
        let sig = |s: Vec<Vec<Vec<u8>>>| if signed { s } else { vec![] };
        case(c, &format!("{kind}/free"), call.clone(), token, none.clone(), vec![], invoke_reply(0));
        case(c, &format!("{kind}/other_program_id"), call.clone(), key(77), none.clone(), sig(seeds.clone()),
             invoke_reply(0));
        if kind == "transfer_invoke" {
            case(c, &format!("{kind}/return_code_ignored"), call.clone(), token, none.clone(), vec![], invoke_reply(1));
        }
        if kind == "close_invoke_signed" {
            case(c, &format!("{kind}/callee_fails"), call.clone(), token, none.clone(), sig(seeds.clone()),
                 invoke_terminates());
        }
        case(c, &format!("{kind}/first_writable_shared"), call.clone(), token, shared(0), vec![], no_script());
        case(c, &format!("{kind}/destination_exclusive"), call.clone(), token, exclusive(2), vec![], no_script());
        case(c, &format!("{kind}/readonly_borrowed"), call.clone(), token,
             Held { shared: vec![1], exclusive: vec![3] }, vec![], invoke_reply(0));
    }
    case(c, "transfer_invoke/max_values_spare_accounts",
         Call::Transfer { from: 4, mint: 3, to: 1, authority: 0, amount: u64::MAX, decimals: 255, signed: false },
         token, none.clone(), vec![], invoke_reply(0));
    case(c, "transfer_invoke_signed/aliased",
         Call::Transfer { from: 2, mint: 1, to: 2, authority: 2, amount: 1, decimals: 0, signed: true }, token,
         none.clone(), vec![vec![b"a".to_vec()]], invoke_reply(0));
    case(c, "transfer_invoke_signed/aliased_borrowed",
         Call::Transfer { from: 2, mint: 2, to: 2, authority: 2, amount: 1, decimals: 0, signed: true }, token,
         shared(2), vec![], no_script());
    case(c, "close_invoke_signed/aliased", Call::Close { account: 4, destination: 4, authority: 4 }, token,
         none.clone(), seeds.clone(), invoke_reply(0));

    // Raw header bytes: the checked path copies them unchanged (noncanonical
    // flag bytes, the first padding byte) and never reads them as Booleans.
    let raw: [(usize, [u8; 4]); 4] = [(0, [2, 255, 9, 0x5a]), (1, [0, 0, 3, 1]), (2, [128, 1, 0, 0xff]), (3, [7, 0, 1, 0x10])];
    raw_case(c, "transfer_invoke/raw_header", transfer(false), token, none.clone(), vec![], invoke_reply(0), &raw);
    raw_case(c, "transfer_invoke_signed/raw_header", transfer(true), token, none.clone(), seeds.clone(),
             invoke_reply(0), &raw);
    raw_case(c, "close_invoke_signed/raw_header", close(), token, none.clone(), vec![vec![b"c".to_vec()]],
             invoke_reply(0), &raw);
    raw_case(c, "transfer_invoke_signed/raw_header_destination_borrowed", transfer(true), token, shared(2), vec![],
             no_script(), &raw);
}
