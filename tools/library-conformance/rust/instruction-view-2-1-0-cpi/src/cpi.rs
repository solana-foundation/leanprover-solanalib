//! Checked CPI preparation over a loader input region and the shim `sol_invoke_signed_c`.
//!
//! Each case serializes an `Input` (distinct keys, duplicates, chosen flags), builds an
//! `AccountView` per entry (a duplicate entry views its target, as the entrypoint does), takes
//! the case borrows through `try_borrow`/`try_borrow_mut` and keeps them live during the call,
//! and calls the function under a shim script. The state before is the region read back after
//! the borrows and the script; after the call it is the region read back and the shim state.

use conformance_accounts::{Account, Entry, Input, Region};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, AccountWrite, Reply, Script};
use solana_account_view::{AccountView, RuntimeAccount};
use solana_address::Address;
use solana_instruction_view::cpi::{invoke_signed, Seed, Signer};
use solana_instruction_view::{InstructionAccount, InstructionView};

#[derive(Clone, Copy)]
pub enum Borrow {
    Shared,
    Mut,
}

/// `start`, 30 zero bytes and `start + 1`: distinct keys with a compact zero run.
pub fn key32(start: u8) -> [u8; 32] {
    let mut k = [0u8; 32];
    k[0] = start;
    k[31] = start.wrapping_add(1);
    k
}

pub fn account(key: u8, signer: bool, writable: bool, lamports: u64, data: &[u8]) -> Entry {
    Entry::Account(Account {
        key: key32(key),
        owner: [0; 32],
        lamports,
        data: data.to_vec(),
        is_signer: signer,
        is_writable: writable,
        executable: false,
        rent_epoch: 0,
    })
}

/// Region, views and live borrows; `call` runs while the borrows are held.
fn with_views<R>(input: &Input, borrows: &[(usize, Borrow)], call: impl FnOnce(&[AccountView], &Region) -> R) -> R {
    with_views_poked(input, &[], borrows, call)
}

/// A raw header byte written into the serialized region before the views are built:
/// (entry, byte offset in the account header, value). Offsets 1 to 3 are the flag bytes,
/// 4 the first padding byte (account-view `padding`), which the loader leaves zero.
pub type Poke = (usize, usize, u8);

fn with_views_poked<R>(input: &Input, pokes: &[Poke], borrows: &[(usize, Borrow)],
                       call: impl FnOnce(&[AccountView], &Region) -> R) -> R {
    let mut region = input.serialize();
    for (entry, offset, value) in pokes {
        assert!((1..8).contains(offset), "only header flag and padding bytes are poked");
        unsafe { *region.account_ptr(*entry).add(*offset) = *value };
    }
    let views: Vec<AccountView> = (0..input.entries.len())
        .map(|i| {
            let j = match input.entries[i] {
                Entry::Duplicate(j) => j as usize,
                Entry::Account(_) => i,
            };
            unsafe { AccountView::new_unchecked(region.account_ptr(j) as *mut RuntimeAccount) }
        })
        .collect();
    for (i, b) in borrows {
        // A separate view of the same account takes the borrow; it stays live (forgotten guard).
        let mut holder = unsafe { AccountView::new_unchecked(views[*i].account_ptr() as *mut RuntimeAccount) };
        match b {
            Borrow::Shared => core::mem::forget(holder.try_borrow().expect("shared borrow")),
            Borrow::Mut => core::mem::forget(holder.try_borrow_mut().expect("exclusive borrow")),
        }
    }
    call(&views, &region)
}

fn result_json(r: &Result<(), solana_program_error::ProgramError>) -> Json {
    match r {
        Ok(()) => rec::ok(Json::Null),
        Err(e) => rec::err(format!("{e:?}").into()),
    }
}

pub struct Case<'a> {
    pub id: String,
    pub input: Input,
    pub borrows: Vec<(usize, Borrow)>,
    pub script: Script,
    pub args: Json,
    pub call: &'a dyn Fn(&[AccountView]) -> Result<(), solana_program_error::ProgramError>,
}

pub fn run(c: &mut Corpus, function: &'static str, generics: Vec<(&'static str, String)>, case: Case) {
    run_raw(c, function, generics, case, &[], false)
}

/// `run`, with header bytes poked into the region and optionally the shim raw CPI header
/// logging (`"raw_header": true` is then part of the state).
pub fn run_raw(c: &mut Corpus, function: &'static str, generics: Vec<(&'static str, String)>, case: Case,
               pokes: &[Poke], raw_header: bool) {
    let state_of = |region: Json, syscalls: Json| {
        let mut fields = vec![("region".to_string(), region), ("syscalls".to_string(), syscalls)];
        if raw_header {
            fields.push(("raw_header".to_string(), Json::Bool(true)));
        }
        Json::Obj(fields)
    };
    let before_region = with_views_poked(&case.input, pokes, &case.borrows, |_, region| region.read_back());
    let state = state_of(before_region, case.script.state_before());
    shim::log_cpi_raw_header(raw_header);
    let outcome = shim::case(&case.script, || {
        with_views_poked(&case.input, pokes, &case.borrows, |views, region| {
            let r = (case.call)(views);
            rec::returned(result_json(&r), state_of(region.read_back(), shim::state()))
        })
    });
    shim::log_cpi_raw_header(false);
    c.push(Record { id: case.id, function, generics, layout: None, state, args: case.args, outcome, observed: None });
}

pub fn cpi_ok() -> Script {
    Script::new(vec![Reply::new("sol_invoke_signed_c", 0)])
}

/// The callee changes the lamports and owner of the first prepared account, and its data when the
/// account has `data` bytes (the shim writes at most the current data length).
pub fn cpi_writes(lamports: u64, data: Option<Vec<u8>>) -> Script {
    Script::new(vec![Reply::new("sol_invoke_signed_c", 0).write(AccountWrite {
        account: 0,
        lamports: Some(lamports),
        data,
        owner: Some(key32(0x55)),
    })])
}

pub fn cpi_terminates() -> Script {
    Script::new(vec![Reply::new("sol_invoke_signed_c", 0).terminate("callee failed")])
}

pub fn no_cpi() -> Script {
    Script::new(vec![])
}

pub fn signers_json(signers: &[&[&[u8]]]) -> Json {
    Json::arr(signers.iter(), |s| Json::arr(s.iter(), |b| rec::bytes(b)))
}

/// `[Signer]` over the given nested seeds, then `f`.
pub fn with_signers<R>(signers: &[&[&[u8]]], f: impl FnOnce(&[Signer]) -> R) -> R {
    let seeds: Vec<Vec<Seed>> = signers.iter().map(|s| s.iter().map(|b| Seed::from(*b)).collect()).collect();
    let signers: Vec<Signer> = seeds.iter().map(|s| Signer::from(&s[..])).collect();
    f(&signers)
}

/// The standard accounts: 0 writable signer, 1 writable, 2 duplicate of 0, 3 read-only,
/// 4 read-only signer with data, 5 writable with data.
/// The first `n` of the standard entries (a case serializes only the entries it uses).
pub fn standard_input(n: usize) -> Input {
    let mut input = Input {
        entries: vec![
            account(0x10, true, true, 1_000, &[]),
            account(0x30, false, true, 0, &[]),
            Entry::Duplicate(0),
            account(0x50, false, false, 7, &[]),
            account(0x70, true, false, 9, &[1, 2, 3]),
            account(0x90, false, true, 11, &[4, 5, 6, 7, 8]),
        ],
        instruction_data: vec![],
        program_id: key32(0xa0),
    };
    input.entries.truncate(n);
    input
}

/// Entries a case needs: one past the largest account index it uses.
fn needed(indices: impl IntoIterator<Item = usize>) -> usize {
    indices.into_iter().max().map_or(0, |i| i + 1)
}

// ---------------------------------------------------------------------------
// pinocchio-system 0.6.0
// ---------------------------------------------------------------------------

pub fn record_system(c: &mut Corpus) {
    use pinocchio_system::instructions::{Allocate, Assign, Transfer};
    const TRANSFER: &str = "pinocchio_system::instructions::transfer::Transfer::<'_>::invoke";
    const ALLOCATE: &str = "pinocchio_system::instructions::allocate::Allocate::<'_>::invoke_signed";
    const ASSIGN: &str = "pinocchio_system::instructions::assign::Assign::<'_, '_>::invoke_signed";

    let transfers: Vec<(&str, usize, usize, u64, Vec<(usize, Borrow)>, Script)> = vec![
        ("ok", 0, 1, 7, vec![], cpi_ok()),
        ("max_lamports", 0, 1, u64::MAX, vec![], cpi_ok()),
        ("alias_via_duplicate", 0, 2, 5, vec![], cpi_ok()),
        ("from_not_signer_or_writable", 3, 1, 1, vec![], cpi_ok()),
        ("from_with_data", 4, 5, 2, vec![], cpi_ok()),
        ("from_shared_borrow", 0, 1, 7, vec![(0, Borrow::Shared)], no_cpi()),
        ("to_exclusive_borrow", 0, 1, 7, vec![(1, Borrow::Mut)], no_cpi()),
        ("unrelated_borrow", 0, 1, 7, vec![(3, Borrow::Mut)], cpi_ok()),
        ("callee_writes", 0, 1, 7, vec![], cpi_writes(993, None)),
        ("callee_fails", 0, 1, 7, vec![], cpi_terminates()),
    ];
    {
        let call = |v: &[AccountView]| Transfer { from: &v[0], to: &v[1], lamports: 9 }.invoke();
        run_raw(c, TRANSFER, vec![], Case {
            id: "transfer/raw_header_padding".to_string(),
            input: standard_input(2),
            borrows: vec![],
            script: cpi_ok(),
            args: Json::obj([("from", 0usize.into()), ("to", 1usize.into()), ("lamports", 9u64.into())]),
            call: &call,
        }, &[(0, 4, 0x11), (1, 2, 3), (1, 4, 0xee)], true);
    }
    for (label, from, to, lamports, borrows, script) in transfers {
        let call = move |v: &[AccountView]| Transfer { from: &v[from], to: &v[to], lamports }.invoke();
        run(c, TRANSFER, vec![], Case {
            id: format!("transfer/{label}"),
            input: standard_input(needed([from, to].into_iter().chain(borrows.iter().map(|b| b.0)))),
            borrows,
            script,
            args: Json::obj([("from", from.into()), ("to", to.into()), ("lamports", lamports.into())]),
            call: &call,
        });
    }

    let seeds_a: &[&[&[u8]]] = &[];
    let seeds_b: &[&[&[u8]]] = &[&[b"vault", &[0xfe]]];
    let seeds_c: &[&[&[u8]]] = &[&[], &[b"", b"x"], &[b"vault"]];
    let allocations: Vec<(&str, usize, u64, &[&[&[u8]]], Vec<(usize, Borrow)>, Script)> = vec![
        ("ok_no_signers", 0, 0, seeds_a, vec![], cpi_ok()),
        ("ok_one_signer", 1, 10_240, seeds_b, vec![], cpi_ok()),
        ("ok_nested_signers", 5, u64::MAX, seeds_c, vec![], cpi_ok()),
        ("readonly_account", 3, 8, seeds_a, vec![], cpi_ok()),
        ("shared_borrow", 0, 8, seeds_b, vec![(0, Borrow::Shared)], no_cpi()),
        ("callee_fails", 0, 8, seeds_a, vec![], cpi_terminates()),
    ];
    for (label, account_index, space, signers, borrows, script) in allocations {
        let call = move |v: &[AccountView]| {
            with_signers(signers, |s| Allocate { account: &v[account_index], space }.invoke_signed(s))
        };
        run(c, ALLOCATE, vec![], Case {
            id: format!("allocate/{label}"),
            input: standard_input(needed([account_index].into_iter().chain(borrows.iter().map(|b| b.0)))),
            borrows,
            script,
            args: Json::obj([("account", account_index.into()), ("space", space.into()), ("signers", signers_json(signers))]),
            call: &call,
        });
    }

    let assigns: Vec<(&str, usize, [u8; 32], &[&[&[u8]]], Vec<(usize, Borrow)>, Script)> = vec![
        ("ok_no_signers", 0, key32(0x20), seeds_a, vec![], cpi_ok()),
        ("ok_owner_zero_nested", 4, [0; 32], seeds_c, vec![], cpi_ok()),
        ("exclusive_borrow", 5, key32(0x20), seeds_b, vec![(5, Borrow::Mut)], no_cpi()),
        ("callee_writes", 1, key32(0x21), seeds_b, vec![], cpi_writes(3, None)),
    ];
    for (label, account_index, owner, signers, borrows, script) in assigns {
        let call = move |v: &[AccountView]| {
            let owner = Address::new_from_array(owner);
            with_signers(signers, |s| Assign { account: &v[account_index], owner: &owner }.invoke_signed(s))
        };
        run(c, ASSIGN, vec![], Case {
            id: format!("assign/{label}"),
            input: standard_input(needed([account_index].into_iter().chain(borrows.iter().map(|b| b.0)))),
            borrows,
            script,
            args: Json::obj([("account", account_index.into()), ("owner", rec::bytes(&owner)),
                ("signers", signers_json(signers))]),
            call: &call,
        });
    }
}

// ---------------------------------------------------------------------------
// pinocchio-associated-token-account 0.4.0
// ---------------------------------------------------------------------------

pub fn record_ata(c: &mut Corpus) {
    use pinocchio_associated_token_account::instructions::CreateIdempotent;
    const FUNCTION: &str =
        "pinocchio_associated_token_account::instructions::create_idempotent::CreateIdempotent::<'_>::invoke";
    // (label, funding, account, wallet, mint, system, token, borrows, script)
    type Row = (&'static str, [usize; 6], Vec<(usize, Borrow)>, Script);
    let rows: Vec<Row> = vec![
        ("distinct", [0, 1, 3, 4, 5, 2], vec![], cpi_ok()),
        ("wallet_is_funding", [0, 1, 2, 4, 5, 3], vec![], cpi_ok()),
        ("all_same_account", [0, 2, 0, 2, 0, 2], vec![], cpi_ok()),
        ("readonly_mint_exclusive_borrow", [0, 1, 3, 4, 5, 3], vec![(4, Borrow::Mut)], cpi_ok()),
        ("associated_shared_borrow", [0, 1, 3, 4, 5, 3], vec![(1, Borrow::Shared)], no_cpi()),
        ("funding_exclusive_borrow", [0, 1, 3, 4, 5, 3], vec![(0, Borrow::Mut)], no_cpi()),
        ("callee_writes", [0, 1, 3, 4, 5, 3], vec![], cpi_writes(1, None)),
        ("callee_fails", [0, 1, 3, 4, 5, 3], vec![], cpi_terminates()),
    ];
    for (label, ix, borrows, script) in rows {
        let call = move |v: &[AccountView]| {
            CreateIdempotent {
                funding_account: &v[ix[0]],
                account: &v[ix[1]],
                wallet: &v[ix[2]],
                mint: &v[ix[3]],
                system_program: &v[ix[4]],
                token_program: &v[ix[5]],
            }
            .invoke()
        };
        run(c, FUNCTION, vec![], Case {
            id: format!("create_idempotent/{label}"),
            input: standard_input(needed(ix.into_iter().chain(borrows.iter().map(|b| b.0)))),
            borrows,
            script,
            args: Json::obj([
                ("funding_account", ix[0].into()),
                ("account", ix[1].into()),
                ("wallet", ix[2].into()),
                ("mint", ix[3].into()),
                ("system_program", ix[4].into()),
                ("token_program", ix[5].into()),
            ]),
            call: &call,
        });
    }
}

// ---------------------------------------------------------------------------
// solana-instruction-view 2.1.0 `invoke_signed::<ACCOUNTS, &AccountView>`
// ---------------------------------------------------------------------------

pub struct Meta {
    pub key: [u8; 32],
    pub writable: bool,
    pub signer: bool,
}

fn meta_json(m: &Meta) -> Json {
    Json::obj([("pubkey", rec::bytes(&m.key)), ("is_signer", m.signer.into()), ("is_writable", m.writable.into())])
}

fn invoke_case<const N: usize>(c: &mut Corpus, label: &str, metas: Vec<Meta>, data: Vec<u8>, accounts: [usize; N],
                                signers: &'static [&'static [&'static [u8]]], borrows: Vec<(usize, Borrow)>, script: Script) {
    invoke_case_raw(c, label, metas, data, accounts, signers, borrows, script, &[], false)
}

#[allow(clippy::too_many_arguments)]
fn invoke_case_raw<const N: usize>(c: &mut Corpus, label: &str, metas: Vec<Meta>, data: Vec<u8>, accounts: [usize; N],
                                    signers: &'static [&'static [&'static [u8]]], borrows: Vec<(usize, Borrow)>,
                                    script: Script, pokes: &[Poke], raw_header: bool) {
    let program = key32(0xc0);
    let args = Json::obj([
        ("instruction", Json::obj([
            ("program_id", rec::bytes(&program)),
            ("accounts", Json::arr(metas.iter(), meta_json)),
            ("data", rec::bytes(&data)),
        ])),
        ("accounts", Json::arr(accounts.iter(), |i| Json::from(*i))),
        ("signers", signers_json(signers)),
    ]);
    let call = move |v: &[AccountView]| {
        let program = Address::new_from_array(program);
        let keys: Vec<Address> = metas.iter().map(|m| Address::new_from_array(m.key)).collect();
        let ias: Vec<InstructionAccount> =
            metas.iter().zip(keys.iter()).map(|(m, k)| InstructionAccount::new(k, m.writable, m.signer)).collect();
        let instruction = InstructionView { program_id: &program, data: &data, accounts: &ias };
        let array: [&AccountView; N] = accounts.map(|i| &v[i]);
        with_signers(signers, |s| invoke_signed::<N, &AccountView>(&instruction, &array, s))
    };
    run_raw(c, "solana_instruction_view::cpi::invoke_signed",
        vec![("ACCOUNTS", N.to_string()), ("A", "&solana_account_view::AccountView".to_string())],
        Case { id: format!("invoke_signed/{label}"),
            input: standard_input(needed(accounts.into_iter().chain(borrows.iter().map(|b| b.0)))),
            borrows, script, args, call: &call }, pokes, raw_header);
}

pub fn record_invoke_signed(c: &mut Corpus) {
    let m = |k: u8, writable: bool, signer: bool| Meta { key: key32(k), writable, signer };
    const NONE: &[&[&[u8]]] = &[];
    const NESTED: &[&[&[u8]]] = &[&[b"a", b"bc"], &[], &[b""]];
    invoke_case(c, "ok_asymmetric_flags", vec![m(0x10, false, true), m(0x30, true, false)], vec![7, 9],
        [0, 1], NESTED, vec![], cpi_ok());
    invoke_case(c, "extra_trailing_account", vec![m(0x10, true, true), m(0x30, true, false)], vec![],
        [0, 1, 3], NONE, vec![], cpi_ok());
    invoke_case(c, "too_few_accounts", vec![m(0x10, true, true), m(0x30, true, false)], vec![1],
        [0], NONE, vec![], no_cpi());
    invoke_case(c, "address_mismatch_second", vec![m(0x10, true, true), m(0x50, false, false)], vec![],
        [0, 1], NONE, vec![], no_cpi());
    invoke_case(c, "borrow_error_before_later_mismatch", vec![m(0x30, true, false), m(0x10, true, true)], vec![],
        [1, 3], NONE, vec![(1, Borrow::Mut)], no_cpi());
    invoke_case(c, "address_mismatch_before_borrow", vec![m(0x10, true, true)], vec![],
        [1], NONE, vec![(1, Borrow::Mut)], no_cpi());
    invoke_case(c, "writable_shared_borrow", vec![m(0x10, true, true), m(0x30, true, false)], vec![],
        [0, 1], NONE, vec![(1, Borrow::Shared)], no_cpi());
    invoke_case(c, "readonly_exclusive_borrow_ok", vec![m(0x10, false, false), m(0x30, true, false)], vec![],
        [0, 1], NONE, vec![(0, Borrow::Mut)], cpi_ok());
    invoke_case(c, "duplicate_entries", vec![m(0x10, true, true), m(0x10, false, false)], vec![3],
        [0, 2], NONE, vec![], cpi_ok());
    invoke_case(c, "data_accounts", vec![m(0x70, false, true), m(0x90, true, false)], vec![0xff; 5],
        [4, 5], NONE, vec![], cpi_writes(4, Some(vec![0xab, 0xcd])));
    invoke_case::<0>(c, "empty", vec![], vec![], [], NONE, vec![], cpi_ok());
    invoke_case(c, "callee_fails", vec![m(0x10, true, true)], vec![], [0], NONE, vec![], cpi_terminates());
    // v2 copies the four header bytes as one word: the padding byte and non-0/1 flag bytes
    // reach the CPI account info unchanged (logged raw with the shim header option).
    invoke_case_raw(c, "raw_header_padding", vec![m(0x10, true, true), m(0x30, true, false)], vec![], [0, 1],
        NONE, vec![], cpi_ok(), &[(0, 4, 0x5a), (1, 4, 0xff)], true);
    invoke_case_raw(c, "raw_header_noncanonical_flags", vec![m(0x10, false, true), m(0x30, true, false)], vec![],
        [0, 1], NONE, vec![], cpi_ok(), &[(0, 1, 2), (0, 3, 7), (1, 2, 0x80), (1, 4, 1)], true);
}

// ---------------------------------------------------------------------------
// solana-instruction-view 2.1.0 `invoke_signed::<ACCOUNTS, Recording>`: a recording `AsRef`
// ---------------------------------------------------------------------------

/// One scripted answer of `Recording::as_ref`.
#[derive(Clone)]
pub enum Step {
    /// Return the view of this input entry.
    Ret(usize),
    /// Panic with this message.
    Panic(&'static str),
}

fn step_json(s: &Step) -> Json {
    match s {
        Step::Ret(j) => Json::obj([("ret", (*j).into())]),
        Step::Panic(m) => Json::obj([("panic", (*m).into())]),
    }
}

thread_local! {
    static VIEWS: std::cell::Cell<*const AccountView> = const { std::cell::Cell::new(core::ptr::null()) };
    static STEPS: std::cell::RefCell<std::collections::VecDeque<Step>> =
        const { std::cell::RefCell::new(std::collections::VecDeque::new()) };
    static CALLS: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// The array element `A`: each `as_ref` call logs `index` and answers from the case script,
/// or with the element view once the script is exhausted.
pub struct Recording {
    pub index: usize,
}

impl AsRef<AccountView> for Recording {
    fn as_ref(&self) -> &AccountView {
        CALLS.with(|c| c.borrow_mut().push(self.index));
        let j = match STEPS.with(|s| s.borrow_mut().pop_front()) {
            Some(Step::Ret(j)) => j,
            Some(Step::Panic(m)) => panic!("{m}"),
            None => self.index,
        };
        // The case views outlive the call (they are owned by the running case).
        unsafe { &*VIEWS.with(|v| v.get()).add(j) }
    }
}

fn as_ref_state() -> Json {
    Json::obj([
        ("script", STEPS.with(|s| Json::arr(s.borrow().iter(), step_json))),
        ("calls", CALLS.with(|c| Json::arr(c.borrow().iter(), |i| Json::from(*i)))),
    ])
}

#[allow(clippy::too_many_arguments)]
fn recording_case<const N: usize>(c: &mut Corpus, label: &str, metas: Vec<Meta>, accounts: [usize; N],
                                   steps: Vec<Step>, borrows: Vec<(usize, Borrow)>, script: Script) {
    let program = key32(0xc0);
    let input = standard_input(needed(accounts.into_iter().chain(borrows.iter().map(|b| b.0)).chain(
        steps.iter().filter_map(|s| if let Step::Ret(j) = s { Some(*j) } else { None }))));
    let args = Json::obj([
        ("instruction", Json::obj([
            ("program_id", rec::bytes(&program)),
            ("accounts", Json::arr(metas.iter(), meta_json)),
            ("data", rec::bytes(&[])),
        ])),
        ("accounts", Json::arr(accounts.iter(), |i| Json::from(*i))),
        ("signers", signers_json(&[])),
    ]);
    let reset = |steps: &[Step]| {
        STEPS.with(|s| *s.borrow_mut() = steps.iter().cloned().collect());
        CALLS.with(|c| c.borrow_mut().clear());
    };
    reset(&steps);
    let before = with_views(&input, &borrows, |_, region| region.read_back());
    let state = Json::obj([("region", before), ("syscalls", script.state_before()), ("as_ref", as_ref_state())]);
    let outcome = shim::case(&script, || {
        reset(&steps);
        with_views(&input, &borrows, |views, region| {
            VIEWS.with(|v| v.set(views.as_ptr()));
            let result = rec::catch(|| {
                let program = Address::new_from_array(program);
                let keys: Vec<Address> = metas.iter().map(|m| Address::new_from_array(m.key)).collect();
                let ias: Vec<InstructionAccount> = metas.iter().zip(keys.iter())
                    .map(|(m, k)| InstructionAccount::new(k, m.writable, m.signer)).collect();
                let instruction = InstructionView { program_id: &program, data: &[], accounts: &ias };
                let array: [Recording; N] = accounts.map(|index| Recording { index });
                invoke_signed::<N, Recording>(&instruction, &array, &[])
            });
            let after = Json::obj([("region", region.read_back()), ("syscalls", shim::state()),
                ("as_ref", as_ref_state())]);
            match result {
                Ok(r) => rec::returned(result_json(&r), after),
                Err(reason) => rec::unwound(reason, after),
            }
        })
    });
    c.push(Record {
        id: format!("invoke_signed_recording/{label}"),
        function: "solana_instruction_view::cpi::invoke_signed",
        generics: vec![("ACCOUNTS", N.to_string()), ("A", "conformance_instruction_view_2_1_0_cpi::cpi::Recording".to_string())],
        layout: None,
        state,
        args,
        outcome,
        observed: None,
    });
}

pub fn record_invoke_signed_recording(c: &mut Corpus) {
    let m = |k: u8, writable: bool, signer: bool| Meta { key: key32(k), writable, signer };
    use Step::{Panic, Ret};
    // Writable metas call `as_ref` three times (address, borrow check, initialization),
    // read-only metas twice; the answer to each call is used.
    recording_case(c, "identity_call_order", vec![m(0x10, true, true), m(0x30, false, false)], [0, 1],
        vec![], vec![], cpi_ok());
    recording_case(c, "init_returns_other_account", vec![m(0x10, true, true)], [0],
        vec![Ret(0), Ret(0), Ret(4)], vec![], cpi_ok());
    recording_case(c, "borrow_check_on_other_account", vec![m(0x10, true, true)], [0],
        vec![Ret(0), Ret(1)], vec![(1, Borrow::Shared)], no_cpi());
    recording_case(c, "address_check_on_other_account", vec![m(0x10, true, true)], [0],
        vec![Ret(3)], vec![], no_cpi());
    recording_case(c, "readonly_has_no_borrow_call", vec![m(0x10, false, false)], [0],
        vec![Ret(0), Ret(5)], vec![(0, Borrow::Mut)], cpi_ok());
    recording_case(c, "panic_on_borrow_call", vec![m(0x10, true, true), m(0x30, true, false)], [0, 1],
        vec![Ret(0), Panic("scripted as_ref panic")], vec![], no_cpi());
    recording_case(c, "panic_on_second_init", vec![m(0x10, true, true), m(0x30, false, false)], [0, 1],
        vec![Ret(0), Ret(0), Ret(0), Ret(1), Panic("scripted as_ref panic")], vec![], no_cpi());
    recording_case(c, "count_check_before_any_call", vec![m(0x10, true, true), m(0x30, true, false)], [0],
        vec![Panic("scripted as_ref panic")], vec![], no_cpi());
    recording_case(c, "trailing_element_not_called", vec![m(0x10, true, true)], [0, 3],
        vec![], vec![], cpi_ok());
    recording_case(c, "duplicate_elements", vec![m(0x10, true, true), m(0x10, false, false)], [0, 2],
        vec![], vec![], cpi_ok());
}
