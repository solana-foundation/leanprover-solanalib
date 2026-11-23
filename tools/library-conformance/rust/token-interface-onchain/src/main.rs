//! Records spl-token-2022 11.0.0 `onchain::invoke_transfer_checked` natively
//! (host build of the Solana branches), with the final CPI answered by the
//! shim `sol_invoke_signed_rust`.
//!
//! Record shape (README of the family module `Families/TokenInterface/Onchain.lean`):
//! * state: `accounts` (each distinct `AccountInfo`: key, owner, lamports,
//!   data, flags; aliases are clones of one entry and share its two cells),
//!   `borrows` held by the caller during the call (`{account, cell, mode}`),
//!   `syscalls` (the scripted CPI reply) and `counts`;
//! * args: program id, the account index of each role, the additional
//!   accounts by index, amount, decimals and signer seeds;
//! * outcome: `Ok(())`/`Err(ProgramError)` or a caught panic, with the
//!   accounts read back, the borrows still held, the syscall log and
//!   `counts`. The decoder logs the instruction for each CPI, its account infos
//!   (identified by the index of the cell pair their `Rc`s point to), the
//!   signer seeds and `counts`.
//!
//! `counts` is the `Rc::strong_count` of every cell, in cell order (account
//! the lamports `Rc` for `i` at `2i`, its data `Rc` at `2i + 1`), read through a
//! `Weak` per cell, which leaves the strong counts unchanged: before the call
//! with its arguments built (the caller infos, the `additional` clones and
//! the four infos the call takes by value), at each CPI, and after the call
//! returned or unwound, while the caller still holds its infos and
//! `additional`.

use conformance_recorder::{bytes, catch, err, ok, returned, unwound, variant, Corpus, Json, Record};
use conformance_shim::{Reply, Script};
use solana_account_info::AccountInfo;
use solana_address::Address;
use solana_instruction::AccountMeta;
use solana_program_error::ProgramError;
use solana_stable_layout::stable_instruction::StableInstruction;
use std::cell::RefCell;
use std::rc::{Rc, Weak};

const TOKEN_2022: [u8; 32] = spl_token_2022::ID.to_bytes();
const LEGACY: [u8; 32] = spl_token_2022_interface_legacy();

const fn spl_token_2022_interface_legacy() -> [u8; 32] {
    // TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA
    [
        6, 221, 246, 225, 215, 101, 161, 147, 217, 203, 225, 70, 206, 235, 121, 172, 28, 180, 133, 237,
        95, 91, 55, 145, 58, 140, 245, 133, 126, 255, 0, 169,
    ]
}

fn k(seed: u8) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[0] = seed;
    b[31] = seed.wrapping_mul(31).wrapping_add(7);
    b
}

fn key(b: &[u8]) -> Json {
    assert_eq!(b.len(), 32);
    bytes(b)
}

fn program_error(e: &ProgramError) -> Json {
    match e {
        ProgramError::Custom(code) => variant("Custom", vec![Json::from(*code)]),
        other => {
            let name = format!("{other:?}");
            assert!(name.chars().all(|c| c.is_ascii_alphanumeric()), "variant with fields: {name}");
            variant(&name, vec![])
        }
    }
}

/// A `Weak` to the lamports and the data cell of one distinct account.
type Cells = (Weak<RefCell<&'static mut u64>>, Weak<RefCell<&'static mut [u8]>>);

thread_local! {
    /// The cells of each distinct account of the running case.
    static CELLS: RefCell<Vec<Cells>> = const { RefCell::new(Vec::new()) };
}

fn cell_index(lamports: usize, data: usize) -> Json {
    CELLS.with(|c| {
        let c = c.borrow();
        match c.iter().position(|(l, d)| Weak::as_ptr(l) as usize == lamports && Weak::as_ptr(d) as usize == data) {
            Some(i) => Json::from(i),
            None => Json::Null,
        }
    })
}

/// The strong count of every cell, in cell order.
fn rc_counts() -> Json {
    CELLS.with(|c| {
        Json::Arr(
            c.borrow()
                .iter()
                .flat_map(|(l, d)| [Weak::strong_count(l), Weak::strong_count(d)])
                .map(Json::from)
                .collect(),
        )
    })
}

/// Splits the child-process `{"counts_before":[..],"outcome":..}` (the recorder
/// rendering: no whitespace, fields in order) into the counts before the call
/// and the outcome. An outcome the case did not return (a terminal syscall, a
/// dead child) has no counts.
fn split_counts_before(out: Json) -> (Json, Json) {
    let Json::Raw(text) = &out else { return (Json::Null, out) };
    let Some(rest) = text.strip_prefix("{\"counts_before\":[") else { return (Json::Null, out) };
    let (counts, rest) = rest.split_once(']').expect("counts_before is a list of integers");
    let outcome = rest.strip_prefix(",\"outcome\":").and_then(|o| o.strip_suffix('}')).expect("outcome follows counts_before");
    let counts = counts.split(',').filter(|n| !n.is_empty()).map(|n| Json::from(n.parse::<usize>().expect("count")));
    (Json::Arr(counts.collect()), Json::Raw(outcome.to_string()))
}

/// `sol_invoke_signed_rust` arguments, at the layouts of solana-stable-layout
/// 3.0.0 and solana-account-info 3.1.1.
fn decode(instruction: *const u8, infos: *const u8, infos_len: u64, seeds: *const u8, seeds_len: u64) -> Json {
    let ix = unsafe { &*(instruction as *const StableInstruction) };
    let metas: &[AccountMeta] = &ix.accounts;
    let infos = unsafe { std::slice::from_raw_parts(infos as *const AccountInfo, infos_len as usize) };
    let seeds = unsafe { std::slice::from_raw_parts(seeds as *const &[&[u8]], seeds_len as usize) };
    Json::obj([
        (
            "instruction",
            Json::obj([
                ("program_id", key(ix.program_id.as_ref())),
                (
                    "accounts",
                    Json::arr(metas.iter(), |m| {
                        Json::obj([
                            ("pubkey", key(m.pubkey.as_ref())),
                            ("is_signer", m.is_signer.into()),
                            ("is_writable", m.is_writable.into()),
                        ])
                    }),
                ),
                ("data", bytes(&ix.data)),
            ]),
        ),
        (
            "account_infos",
            Json::arr(infos.iter(), |a| {
                Json::obj([
                    ("cells", cell_index(Rc::as_ptr(&a.lamports) as usize, Rc::as_ptr(&a.data) as usize)),
                    ("key", key(a.key.as_ref())),
                    ("owner", key(a.owner.as_ref())),
                    ("is_signer", a.is_signer.into()),
                    ("is_writable", a.is_writable.into()),
                    ("executable", a.executable.into()),
                ])
            }),
        ),
        ("signers_seeds", Json::arr(seeds.iter(), |s| Json::arr(s.iter(), |b| bytes(b)))),
        ("counts", rc_counts()),
    ])
}

#[derive(Clone)]
struct Account {
    key: [u8; 32],
    owner: [u8; 32],
    lamports: u64,
    data: Vec<u8>,
    is_signer: bool,
    is_writable: bool,
    executable: bool,
}

fn account_json(a: &Account) -> Json {
    Json::obj([
        ("key", key(&a.key)),
        ("owner", key(&a.owner)),
        ("lamports", a.lamports.into()),
        ("data", bytes(&a.data)),
        ("is_signer", a.is_signer.into()),
        ("is_writable", a.is_writable.into()),
        ("executable", a.executable.into()),
    ])
}

#[derive(Clone, Copy)]
enum Held {
    DataShared(usize),
    DataExclusive(usize),
    LamportsExclusive(usize),
}

fn held_json(h: &Held) -> Json {
    let (account, cell, mode) = match *h {
        Held::DataShared(i) => (i, "data", "shared"),
        Held::DataExclusive(i) => (i, "data", "exclusive"),
        Held::LamportsExclusive(i) => (i, "lamports", "exclusive"),
    };
    Json::obj([("account", account.into()), ("cell", cell.into()), ("mode", mode.into())])
}

struct Case {
    id: &'static str,
    program: [u8; 32],
    accounts: Vec<Account>,
    /// Account index of source, mint, destination and authority.
    roles: [usize; 4],
    additional: Vec<usize>,
    amount: u64,
    decimals: u8,
    seeds: Vec<Vec<Vec<u8>>>,
    held: Vec<Held>,
    /// The scripted CPI return value, if the case reaches it.
    reply: Option<u64>,
    /// The scripted reply from the validation-address search (address, bump), for
    /// transfer-hook mints.
    pda: Option<([u8; 32], u8)>,
}

fn run(case: &Case) -> Record {
    let mut replies = Vec::new();
    if let Some((address, bump)) = case.pda {
        replies.push(Reply::new("sol_try_find_program_address", 0).data(&address).bump(bump));
    }
    if let Some(r) = case.reply {
        replies.push(Reply::new("sol_invoke_signed_rust", r));
    }
    let script = Script::new(replies);
    let args = Json::obj([
        ("program_id", key(&case.program)),
        ("source", case.roles[0].into()),
        ("mint", case.roles[1].into()),
        ("destination", case.roles[2].into()),
        ("authority", case.roles[3].into()),
        ("additional", Json::arr(case.additional.iter(), |i| Json::from(*i))),
        ("amount", case.amount.into()),
        ("decimals", case.decimals.into()),
        ("seeds", Json::arr(case.seeds.iter(), |s| Json::arr(s.iter(), |b| bytes(b)))),
    ]);
    let outcome = conformance_shim::case(&script, || {
        conformance_shim::set_invoke_rust_decoder(decode);
        // Leaked, so that the infos are `AccountInfo<'static>` and `CELLS` can
        // hold `Weak`s to their cells; the child process for the case exits after it.
        let keys: &'static [Address] =
            case.accounts.iter().map(|a| Address::new_from_array(a.key)).collect::<Vec<_>>().leak();
        let owners: &'static [Address] =
            case.accounts.iter().map(|a| Address::new_from_array(a.owner)).collect::<Vec<_>>().leak();
        let lamports: &'static mut [u64] = case.accounts.iter().map(|a| a.lamports).collect::<Vec<_>>().leak();
        let datas: &'static mut [Vec<u8>] = case.accounts.iter().map(|a| a.data.clone()).collect::<Vec<_>>().leak();
        let infos: Vec<AccountInfo<'static>> = {
            let mut infos = Vec::new();
            for (((a, key), owner), (l, d)) in
                case.accounts.iter().zip(keys).zip(owners).zip(lamports.iter_mut().zip(datas.iter_mut()))
            {
                infos.push(AccountInfo::new(key, a.is_signer, a.is_writable, l, d, owner, a.executable));
            }
            infos
        };
        CELLS.with(|c| {
            *c.borrow_mut() = infos.iter().map(|a| (Rc::downgrade(&a.lamports), Rc::downgrade(&a.data))).collect()
        });
        let (result, counts_before, counts_after) = {
            // Borrows held by the caller across the call.
            let mut data_shared = Vec::new();
            let mut data_exclusive = Vec::new();
            let mut lamports_exclusive = Vec::new();
            for h in &case.held {
                match *h {
                    Held::DataShared(i) => data_shared.push(infos[i].data.borrow()),
                    Held::DataExclusive(i) => data_exclusive.push(infos[i].data.borrow_mut()),
                    Held::LamportsExclusive(i) => lamports_exclusive.push(infos[i].lamports.borrow_mut()),
                }
            }
            let additional: Vec<AccountInfo> = case.additional.iter().map(|&i| infos[i].clone()).collect();
            let seeds: Vec<Vec<&[u8]>> =
                case.seeds.iter().map(|s| s.iter().map(|b| b.as_slice()).collect()).collect();
            let seed_refs: Vec<&[&[u8]]> = seeds.iter().map(|s| s.as_slice()).collect();
            let [s, m, d, a] = case.roles;
            // The infos the call takes by value.
            let (source, mint, destination, authority) =
                (infos[s].clone(), infos[m].clone(), infos[d].clone(), infos[a].clone());
            let counts_before = rc_counts();
            let result = catch(|| {
                spl_token_2022::onchain::invoke_transfer_checked(
                    &Address::new_from_array(case.program),
                    source,
                    mint,
                    destination,
                    authority,
                    &additional,
                    case.amount,
                    case.decimals,
                    &seed_refs,
                )
            });
            (result, counts_before, rc_counts())
        };
        // No borrow outlives the call except borrows held by the caller (dropped above).
        for info in &infos {
            assert!(info.try_borrow_mut_data().is_ok() && info.try_borrow_mut_lamports().is_ok());
        }
        let after: Vec<Account> = case
            .accounts
            .iter()
            .zip(&infos)
            .map(|(a, info)| Account {
                lamports: **info.lamports.borrow(),
                data: info.data.borrow().to_vec(),
                ..a.clone()
            })
            .collect();
        drop(infos);
        let state = Json::obj([
            ("accounts", Json::arr(after.iter(), account_json)),
            ("borrows", Json::arr(case.held.iter(), held_json)),
            ("syscalls", conformance_shim::state()),
            ("counts", counts_after),
        ]);
        let outcome = match result {
            Ok(Ok(())) => returned(ok(Json::Null), state),
            Ok(Err(e)) => returned(err(program_error(&e)), state),
            Err(reason) => unwound(reason, state),
        };
        Json::obj([("counts_before", counts_before), ("outcome", outcome)])
    });
    let (counts, outcome) = split_counts_before(outcome);
    let state = Json::obj([
        ("accounts", Json::arr(case.accounts.iter(), account_json)),
        ("borrows", Json::arr(case.held.iter(), held_json)),
        ("syscalls", script.state_before()),
        ("counts", counts),
    ]);
    Record {
        id: case.id.to_string(),
        function: "spl_token_2022::onchain::invoke_transfer_checked",
        generics: vec![],
        layout: None,
        state,
        args,
        outcome,
        observed: None,
    }
}

fn mint_base(initialized: u8) -> Vec<u8> {
    let mut v = 1u32.to_le_bytes().to_vec();
    v.extend_from_slice(&k(90));
    v.extend_from_slice(&5_000_000u64.to_le_bytes());
    v.push(6);
    v.push(initialized);
    v.extend_from_slice(&0u32.to_le_bytes());
    v.extend_from_slice(&[0; 32]);
    v
}

fn extended_mint(tlv: &[u8]) -> Vec<u8> {
    let mut v = mint_base(1);
    v.resize(165, 0);
    v.push(1);
    v.extend_from_slice(tlv);
    v
}

fn tlv_entry(tag: u16, value: &[u8]) -> Vec<u8> {
    let mut v = tag.to_le_bytes().to_vec();
    v.extend_from_slice(&(value.len() as u16).to_le_bytes());
    v.extend_from_slice(value);
    v
}

/// PodMultisig: m, n, is_initialized, then eleven signer keys.
fn multisig(n: u8, signers: &[[u8; 32]]) -> Vec<u8> {
    let mut v = vec![1, n, 1];
    for i in 0..11 {
        v.extend_from_slice(signers.get(i).unwrap_or(&[0; 32]));
    }
    assert_eq!(v.len(), 355);
    v
}

fn acct(seed: u8, owner: [u8; 32], data: Vec<u8>, signer: bool, writable: bool) -> Account {
    Account { key: k(seed), owner, lamports: 1_000_000 + seed as u64, data, is_signer: signer, is_writable: writable, executable: false }
}

const INSUFFICIENT_FUNDS: u64 = 6 << 32;

const HOOK_PROGRAM: u8 = 70;
const VALIDATION: u8 = 71;

fn program() -> Account {
    Account { executable: true, ..acct(HOOK_PROGRAM, [2; 32], vec![], false, false) }
}

fn validation(data: Vec<u8>) -> Account {
    acct(VALIDATION, k(HOOK_PROGRAM), data, false, false)
}

/// An ExtraAccountMetaList TLV entry for Execute: discriminator, u32 length,
/// PodSlice (u32 count, 35-byte records).
fn execute_list(metas: &[[u8; 35]]) -> Vec<u8> {
    let mut v = vec![105, 37, 101, 197, 75, 251, 102, 26];
    v.extend_from_slice(&((4 + 35 * metas.len()) as u32).to_le_bytes());
    v.extend_from_slice(&(metas.len() as u32).to_le_bytes());
    for m in metas {
        v.extend_from_slice(m);
    }
    v
}

/// A fixed-address extra account meta (discriminator 0).
fn fixed_meta(address: [u8; 32], signer: bool, writable: bool) -> [u8; 35] {
    let mut m = [0u8; 35];
    m[1..33].copy_from_slice(&address);
    m[33] = signer as u8;
    m[34] = writable as u8;
    m
}

/// A mint whose transfer-hook extension names `HOOK_PROGRAM`; the validation
/// address search is answered by the shim with `VALIDATION` at bump 253.
fn hook_case(id: &'static str, extra: Vec<Account>, additional: Vec<usize>, reply: Option<u64>) -> Case {
    let mut value = vec![0u8; 64];
    value[32..].copy_from_slice(&k(HOOK_PROGRAM));
    let mut mint = mint_base(1);
    mint.resize(165, 0);
    mint.push(1);
    mint.extend_from_slice(&tlv_entry(14, &value));
    let mut accounts = vec![
        acct(1, [0; 32], vec![], false, true),
        acct(2, TOKEN_2022, mint, false, false),
        acct(3, [0; 32], vec![], false, true),
        acct(4, [0; 32], vec![], true, false),
    ];
    accounts.extend(extra);
    Case {
        id,
        program: TOKEN_2022,
        accounts,
        roles: [0, 1, 2, 3],
        additional,
        amount: 1 << 40,
        decimals: 9,
        seeds: vec![],
        held: vec![],
        reply,
        pda: Some((k(VALIDATION), 253)),
    }
}

fn cases() -> Vec<Case> {
    let base = |mint_data: Vec<u8>, authority: Account| -> Vec<Account> {
        vec![
            // The function never reads source or destination data or owners.
            acct(1, [0; 32], vec![], false, true),
            acct(2, TOKEN_2022, mint_data, false, false),
            acct(3, [0; 32], vec![], false, true),
            authority,
        ]
    };
    let wallet = || acct(4, [0; 32], vec![], true, false);
    let simple = |id: &'static str, program: [u8; 32], mint: Vec<u8>, reply: Option<u64>| Case {
        id,
        program,
        accounts: base(mint, wallet()),
        roles: [0, 1, 2, 3],
        additional: vec![],
        amount: 513,
        decimals: 6,
        seeds: vec![],
        held: vec![],
        reply,
        pda: None,
    };
    let hook = |program: [u8; 32]| {
        let mut value = vec![0u8; 64];
        value[0] = 7; // authority (unused here)
        value[32..].copy_from_slice(&program);
        tlv_entry(14, &value)
    };
    let signers = [k(40), k(41)];
    let ms_accounts = |n: u8, owner: [u8; 32]| {
        let mut accounts = base(mint_base(1), acct(4, owner, multisig(n, &signers), false, false));
        accounts.push(acct(41, [0; 32], vec![], true, false));
        accounts.push(acct(60, [0; 32], vec![], true, false));
        accounts.push(acct(40, [0; 32], vec![], true, false));
        accounts
    };
    let multisig_case = |id: &'static str, n: u8, owner: [u8; 32], held: Vec<Held>, reply: Option<u64>| Case {
        id,
        program: TOKEN_2022,
        accounts: ms_accounts(n, owner),
        roles: [0, 1, 2, 3],
        additional: vec![4, 5, 6, 6, 4],
        amount: u64::MAX,
        decimals: 255,
        seeds: vec![vec![b"vault".to_vec(), vec![254]]],
        held,
        reply,
        pda: None,
    };
    let fee_config = tlv_entry(1, &{
        let mut v = vec![0u8; 108];
        v[72] = 9;
        v
    });
    vec![
        simple("program_rejected", [0; 32], mint_base(1), None),
        simple("legacy_program_bare_mint", LEGACY, mint_base(1), Some(0)),
        simple("bare_mint_cpi_error", TOKEN_2022, mint_base(1), Some(INSUFFICIENT_FUNDS)),
        simple("extended_mint_no_hook", TOKEN_2022, extended_mint(&fee_config), Some(0)),
        simple("hook_zero_program", TOKEN_2022, extended_mint(&hook([0; 32])), Some(0)),
        simple("hook_extension_malformed", TOKEN_2022, extended_mint(&[14, 0, 64, 0, 1, 2]), Some(0)),
        simple("mint_uninitialized", TOKEN_2022, mint_base(0), None),
        simple("mint_short", TOKEN_2022, mint_base(1)[..81].to_vec(), None),
        simple("mint_bad_padding", TOKEN_2022, {
            let mut v = extended_mint(&fee_config);
            v[100] = 1;
            v
        }, None),
        Case { held: vec![Held::DataExclusive(1)], ..simple("mint_data_borrowed", TOKEN_2022, mint_base(1), None) },
        Case {
            held: vec![Held::DataShared(1), Held::LamportsExclusive(0)],
            // Shared mint data still admits the mint read; the CPI is reached
            // only through the shim, whose reply is scripted.
            ..simple("mint_shared_source_lamports_held", TOKEN_2022, mint_base(1), None)
        },
        Case {
            roles: [0, 1, 0, 3],
            seeds: vec![vec![], vec![b"a".to_vec(), vec![]]],
            ..simple("source_is_destination", TOKEN_2022, mint_base(1), Some(0))
        },
        Case { roles: [1, 1, 1, 1], ..simple("all_roles_aliased", TOKEN_2022, mint_base(1), Some(0)) },
        multisig_case("multisig_signers", 2, TOKEN_2022, vec![], Some(0)),
        multisig_case("multisig_legacy_owner", 1, LEGACY, vec![], Some(0)),
        multisig_case("multisig_other_owner", 2, [0; 32], vec![], Some(0)),
        multisig_case("multisig_zero_signers", 0, TOKEN_2022, vec![], Some(0)),
        multisig_case("multisig_n_out_of_range", 12, TOKEN_2022, vec![], None),
        multisig_case("multisig_data_borrowed", 2, TOKEN_2022, vec![Held::DataExclusive(3)], None),
        multisig_case("multisig_data_shared", 2, TOKEN_2022, vec![Held::DataShared(3)], Some(0)),
        hook_case("hook_program_missing", vec![], vec![], None),
        hook_case("hook_without_validation", vec![program()], vec![4], Some(0)),
        hook_case("hook_validation_no_extras", vec![program(), validation(execute_list(&[]))], vec![5, 4], Some(0)),
        hook_case(
            "hook_validation_fixed_extra",
            vec![program(), validation(execute_list(&[fixed_meta(k(72), false, true)])), acct(72, [0; 32], vec![], false, true)],
            vec![6, 5, 4],
            Some(0),
        ),
        hook_case(
            "hook_validation_extra_missing",
            vec![program(), validation(execute_list(&[fixed_meta(k(72), false, true)]))],
            vec![4, 5],
            None,
        ),
        hook_case("hook_validation_malformed", vec![program(), validation(vec![1, 2, 3, 4, 5])], vec![4, 5], None),
    ]
}

fn main() {
    conformance_recorder::init();
    let out = conformance_recorder::out_dir();
    let mut c = Corpus::new("spl_token_2022_11_0_0", &[("spl-token-2022", "11.0.0")]);
    for case in cases() {
        c.push(run(&case));
    }
    c.write(&out).unwrap();
}
