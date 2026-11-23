//! Exact native calls of transfer-hook-interface 0.9.0. The helper invokes
//! no CPI. Only PDA syscalls use the deterministic observation shim.
//! AccountInfo aliases keep their real Rc cells; counts are read via Weak.
use conformance_recorder::{bytes, catch, err, ok, returned, unwound, variant, Corpus, Json, Record};
use conformance_shim::{Reply, Script};
use solana_account_info::AccountInfo;
use solana_pubkey::Pubkey;
use solana_instruction::{AccountMeta, Instruction};
use solana_program_error::ProgramError;
use std::cell::RefCell;
use std::rc::{Rc, Weak};

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
    roles: [usize; 4],
    additional: Vec<usize>,
    amount: u64,
    held: Vec<Held>,
    caller_metas: Vec<AccountMeta>,
    caller_infos: Vec<usize>,
    replies: Vec<Reply>,
}

fn instruction_json(ix: &Instruction) -> Json {
    Json::obj([
        ("program_id", key(ix.program_id.as_ref())),
        ("accounts", Json::arr(ix.accounts.iter(), |m| Json::obj([
            ("pubkey", key(m.pubkey.as_ref())),
            ("is_signer", m.is_signer.into()),
            ("is_writable", m.is_writable.into()),
        ]))),
        ("data", bytes(&ix.data)),
    ])
}

fn infos_json(infos: &[AccountInfo]) -> Json {
    Json::arr(infos.iter(), |a| Json::obj([
        ("cells", cell_index(Rc::as_ptr(&a.lamports) as usize, Rc::as_ptr(&a.data) as usize)),
        ("key", key(a.key.as_ref())),
        ("owner", key(a.owner.as_ref())),
        ("is_signer", a.is_signer.into()),
        ("is_writable", a.is_writable.into()),
        ("executable", a.executable.into()),
    ]))
}

fn run(case: &Case) -> Record {
    let script = Script::new(case.replies.clone());
    let initial_instruction = || Instruction {
        program_id: Pubkey::new_from_array(k(99)),
        accounts: case.caller_metas.clone(),
        data: vec![42, 43, 255, 0],
    };
    let args = Json::obj([
        ("program_id", key(&case.program)),
        ("source", case.roles[0].into()),
        ("mint", case.roles[1].into()),
        ("destination", case.roles[2].into()),
        ("authority", case.roles[3].into()),
        ("additional", Json::arr(case.additional.iter(), |i| Json::from(*i))),
        ("amount", case.amount.into()),
        ("instruction", instruction_json(&initial_instruction())),
        ("caller_infos", Json::arr(case.caller_infos.iter(), |i| Json::from(*i))),
    ]);
    let outcome = conformance_shim::case(&script, || {
        let keys: &'static [Pubkey] = case.accounts.iter().map(|a| Pubkey::new_from_array(a.key)).collect::<Vec<_>>().leak();
        let owners: &'static [Pubkey] = case.accounts.iter().map(|a| Pubkey::new_from_array(a.owner)).collect::<Vec<_>>().leak();
        let lamports: &'static mut [u64] = case.accounts.iter().map(|a| a.lamports).collect::<Vec<_>>().leak();
        let datas: &'static mut [Vec<u8>] = case.accounts.iter().map(|a| a.data.clone()).collect::<Vec<_>>().leak();
        let infos: Vec<AccountInfo<'static>> = case.accounts.iter().zip(keys).zip(owners)
            .zip(lamports.iter_mut().zip(datas.iter_mut()))
            .map(|(((a, key), owner), (l, d))| AccountInfo::new(key, a.is_signer, a.is_writable, l, d, owner, a.executable, 0))
            .collect();
        CELLS.with(|c| *c.borrow_mut() = infos.iter().map(|a| (Rc::downgrade(&a.lamports), Rc::downgrade(&a.data))).collect());
        let mut instruction = initial_instruction();
        let mut caller_infos: Vec<AccountInfo> = case.caller_infos.iter().map(|&i| infos[i].clone()).collect();
        let additional: Vec<AccountInfo> = case.additional.iter().map(|&i| infos[i].clone()).collect();
        let (result, counts_before, counts_after) = {
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
            let [s, m, d, a] = case.roles;
            let (source, mint, destination, authority) = (infos[s].clone(), infos[m].clone(), infos[d].clone(), infos[a].clone());
            let counts_before = rc_counts();
            let result = catch(|| spl_transfer_hook_interface::onchain::add_extra_accounts_for_execute_cpi(
                &mut instruction, &mut caller_infos, &Pubkey::new_from_array(case.program),
                source, mint, destination, authority, case.amount, &additional,
            ));
            (result, counts_before, rc_counts())
        };
        // Every helper-created Ref must have been released, even after panic.
        for info in &infos {
            assert!(info.try_borrow_mut_data().is_ok() && info.try_borrow_mut_lamports().is_ok());
        }
        let after: Vec<Account> = case.accounts.iter().zip(&infos).map(|(a, info)| Account {
            lamports: **info.lamports.borrow(), data: info.data.borrow().to_vec(), ..a.clone()
        }).collect();
        let state = Json::obj([
            ("accounts", Json::arr(after.iter(), account_json)),
            ("borrows", Json::arr(case.held.iter(), held_json)),
            ("syscalls", conformance_shim::state()),
            ("counts", counts_after),
            ("instruction", instruction_json(&instruction)),
            ("caller_infos", infos_json(&caller_infos)),
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
    Record { id: case.id.to_string(), function: "spl_transfer_hook_interface::onchain::add_extra_accounts_for_execute_cpi",
        generics: vec![], layout: None, state, args, outcome, observed: None }
}

fn acct(seed: u8, data: Vec<u8>) -> Account {
    Account { key: k(seed), owner: k(80), lamports: 1000 + seed as u64, data,
        is_signer: true, is_writable: true, executable: false }
}
fn fixed(address: [u8; 32], signer: u8, writable: u8) -> [u8; 35] {
    let mut m = [0; 35]; m[1..33].copy_from_slice(&address); m[33] = signer; m[34] = writable; m
}
fn configured(discriminator: u8, config: &[u8]) -> [u8; 35] {
    let mut m = fixed([0; 32], 1, 1); m[0] = discriminator; m[1..1 + config.len()].copy_from_slice(config); m
}
fn tlv(payload: &[u8]) -> Vec<u8> {
    let mut v = vec![105, 37, 101, 197, 75, 251, 102, 26];
    v.extend_from_slice(&(payload.len() as u32).to_le_bytes()); v.extend_from_slice(payload); v
}
fn execute(metas: &[[u8; 35]]) -> Vec<u8> {
    let mut v = (metas.len() as u32).to_le_bytes().to_vec();
    for m in metas { v.extend_from_slice(m); } tlv(&v)
}
fn pda(address: [u8; 32]) -> Reply { Reply::new("sol_try_find_program_address", 0).data(&address).bump(253) }
fn base(id: &'static str, data: Option<Vec<u8>>) -> Case {
    let mut accounts = vec![acct(1, k(72).to_vec()), acct(2, vec![3; 36]), acct(3, vec![]), acct(4, vec![]), acct(70, vec![])];
    let mut additional = vec![4];
    if let Some(data) = data { accounts.push(acct(71, data)); additional.push(5); }
    Case { id, program: k(70), accounts, roles: [0, 1, 2, 3], additional, amount: (1 << 40) + 513,
        held: vec![], caller_metas: vec![AccountMeta::new(Pubkey::new_from_array(k(90)), true)],
        caller_infos: vec![0, 3], replies: vec![pda(k(71))] }
}
fn extra(id: &'static str, metas: &[[u8; 35]]) -> Case {
    let mut c = base(id, Some(execute(metas))); c.accounts.push(acct(72, k(73).to_vec())); c.additional.push(6); c
}
fn cases() -> Vec<Case> {
    let mut out = vec![
        base("no_validation", None),
        base("validation_empty", Some(execute(&[]))),
        extra("fresh_signer_preserved", &[fixed(k(72), 1, 1)]),
        extra("pod_bool_nonzero", &[fixed(k(72), 2, 255)]),
        base("missing_program", None),
        extra("fixed_extra_missing", &[fixed(k(75), 1, 1)]),
        extra("existing_role_privileges_reduced", &[fixed(k(1), 1, 1)]),
        extra("repeated_extra_privileges_reduced", &[fixed(k(72), 1, 0), fixed(k(72), 1, 1)]),
        extra("fixed_extra_unrelated_borrow_conflict", &[fixed(k(72), 1, 1)]),
        extra("shared_data_and_exclusive_lamports", &[fixed(k(72), 1, 1)]),
        base("validation_exclusive_borrow", Some(execute(&[]))),
        base("first_match_duplicate_cells", Some(execute(&[fixed(k(72), 1, 1)]))),
        base("program_is_validation", None),
        base("all_roles_same_account", Some(execute(&[]))),
        base("tlv_empty", Some(vec![])),
        base("tlv_short_nonzero", Some(vec![1, 2, 3])),
        base("tlv_short_zero", Some(vec![0; 7])),
        base("tlv_invalid_tail", Some({let mut v = execute(&[]); v.push(1); v})),
        base("tlv_zero_tail", Some({let mut v = execute(&[]); v.extend_from_slice(&[0; 7]); v})),
        base("tlv_missing_execute", Some({let mut v = execute(&[]); v[0] = 3; v})),
        base("pod_short_header", Some(tlv(&[0, 0, 0]))),
        base("pod_short_record", Some(tlv(&[0; 5]))),
        base("pod_long_record", Some(tlv(&[0; 40]))),
        base("pod_count_over_capacity_panics", Some({let mut v = execute(&[fixed(k(72), 1, 1)]); v[12] = 2; v})),
        base("pod_unused_capacity", Some({let mut v = execute(&[fixed(k(72), 1, 1)]); v[12] = 0; v})),
        extra("invalid_meta_discriminator", &[configured(3, &[])]),
        extra("account_data_pubkey", &[configured(2, &[2, 0, 0])]),
        extra("instruction_data_too_short", &[configured(2, &[1, 0])]),
        extra("pubkey_account_index_missing", &[configured(2, &[2, 99, 0])]),
        extra("pubkey_data_too_short", &[configured(2, &[2, 3, 1])]),
        extra("external_program_missing_before_bad_seed", &[configured(255, &[255])]),
        extra("invalid_seed_discriminator", &[configured(1, &[255])]),
        extra("literal_before_bad_seed", &[configured(1, &[1, 2, 8, 9, 255])]),
        extra("seed_instruction_data_too_short", &[configured(1, &[2, 15, 2])]),
        extra("seed_account_index_missing", &[configured(1, &[3, 99])]),
        extra("seed_account_data_index_missing", &[configured(1, &[4, 99, 0, 1])]),
        extra("seed_account_data_too_short", &[configured(1, &[4, 3, 0, 1])]),
        extra("error_after_first_extra", &[fixed(k(72), 1, 1), configured(3, &[])]),
        extra("empty_seed_pda", &[configured(1, &[])]),
        base("pda_nonzero_status_panics", None),
        base("pda_failure_before_program_lookup", None),
        base("pda_partial_output", Some(execute(&[]))),
        base("pda_terminal", None),
    ];
    for c in &mut out {
        match c.id {
            "missing_program" => c.additional.clear(),
            "existing_role_privileges_reduced" => c.additional.push(0),
            "fixed_extra_unrelated_borrow_conflict" => c.held = vec![Held::DataExclusive(2)],
            "shared_data_and_exclusive_lamports" => c.held = vec![Held::DataShared(0), Held::DataShared(5), Held::LamportsExclusive(1)],
            "validation_exclusive_borrow" => c.held = vec![Held::DataExclusive(5)],
            "first_match_duplicate_cells" => {
                c.accounts.push(acct(72, vec![6])); c.accounts.push(Account { owner: k(81), ..acct(72, vec![7]) });
                c.additional.extend_from_slice(&[7, 6, 7]);
            }
            "program_is_validation" => { c.accounts[4].data = execute(&[]); c.replies = vec![pda(k(70))]; }
            "all_roles_same_account" => c.roles = [0, 0, 0, 0],
            "empty_seed_pda" => c.replies.push(pda(k(72))),
            "pda_nonzero_status_panics" => c.replies = vec![Reply::new("sol_try_find_program_address", 1)],
            "pda_failure_before_program_lookup" => {
                c.additional.clear();
                c.replies = vec![Reply::new("sol_try_find_program_address", 1)];
            }
            "pda_partial_output" => {
                let mut validation = [0; 32];
                validation[..2].copy_from_slice(&[11, 12]);
                c.accounts[5].key = validation;
                c.replies = vec![Reply::new("sol_try_find_program_address", 0).data(&[11, 12])];
            }
            "pda_terminal" => c.replies = vec![Reply::new("sol_try_find_program_address", 0).terminate("scripted PDA stop")],
            _ => {}
        }
    }
    out
}
fn main() {
    conformance_recorder::init();
    let mut corpus = Corpus::new("spl_transfer_hook_interface_0_9_0", &[("spl-transfer-hook-interface", "0.9.0")]);
    for case in cases() { corpus.push(run(&case)); }
    corpus.write(&conformance_recorder::out_dir()).unwrap();
}
