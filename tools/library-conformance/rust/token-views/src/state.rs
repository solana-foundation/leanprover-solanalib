//! `Account`/`Mint` byte views: the parsers `from_account_view` and the getters
//! `amount`, `mint`, `owner`, `state` (Account) and `decimals` (Mint), for
//! pinocchio-token 0.6.0 and pinocchio-token-2022 0.3.1.
//!
//! Parser cases cover each admission check and its order (length or layout,
//! owner, borrow), shared-borrow saturation (254 outstanding) and the
//! token-2022 extended layouts. A getter case holds the typed `Ref` from a
//! successful parse (marker 254, or lower with further shared borrows) and
//! calls the getter on it.

use crate::common::*;
use conformance_accounts::Account;
use conformance_recorder::{self as rec, Corpus, Json};
use conformance_shim as shim;
use solana_account_view::{AccountView, Ref, RefMut};
use solana_address::Address;
use solana_program_error::ProgramError;

pub struct Version<A: 'static, M: 'static, S> {
    pub krate: &'static str,
    pub id: [u8; 32],
    pub other_id: [u8; 32],
    pub token2022: bool,
    pub account_from: for<'a> fn(&'a AccountView) -> Result<Ref<'a, A>, ProgramError>,
    pub mint_from: for<'a> fn(&'a AccountView) -> Result<Ref<'a, M>, ProgramError>,
    pub amount: fn(&A) -> u64,
    pub mint: fn(&A) -> &Address,
    pub owner: fn(&A) -> &Address,
    pub state: fn(&A) -> S,
    pub decimals: fn(&M) -> u8,
}

fn name(krate: &str, path: &str) -> &'static str {
    Box::leak(format!("{krate}::state::{path}").into_boxed_str())
}

/// Borrows held across the call: shared counts and exclusive borrows by account.
#[derive(Clone, Default)]
struct Borrows {
    shared: Vec<(usize, usize)>,
    exclusive: Vec<usize>,
}

fn shared(j: usize, n: usize) -> Borrows {
    Borrows { shared: vec![(j, n)], exclusive: vec![] }
}

fn exclusive(j: usize) -> Borrows {
    Borrows { shared: vec![], exclusive: vec![j] }
}

const ACCOUNT_LEN: usize = 165;
const MINT_LEN: usize = 82;
const MULTISIG_LEN: usize = 355;

/// The bytes of a token account: zeros, except the amount and the state byte
/// (zero runs of 64 bytes or more are recorded compactly).
fn account_data(len: usize, amount: u64, state: u8) -> Vec<u8> {
    let mut d = vec![0u8; len];
    if len >= ACCOUNT_LEN {
        d[64..72].copy_from_slice(&amount.to_le_bytes());
        d[108] = state;
    }
    d
}

/// The same with the first and last byte of the mint (0..32) and owner
/// (32..64) fields set, for the field-reference getters.
fn account_data_keys(len: usize) -> Vec<u8> {
    let mut d = account_data(len, 1, 1);
    d[0] = 0x11;
    d[31] = 0x1f;
    d[32] = 0x22;
    d[63] = 0x3f;
    d
}

/// The bytes of a mint: zeros, except the decimals byte.
fn mint_data(len: usize, decimals: u8) -> Vec<u8> {
    let mut d = vec![0u8; len];
    if len >= MINT_LEN {
        d[44] = decimals;
    }
    d
}

fn with_type(mut d: Vec<u8>, byte: u8) -> Vec<u8> {
    if d.len() > ACCOUNT_LEN {
        d[ACCOUNT_LEN] = byte;
    }
    d
}

fn parser_case<T>(c: &mut Corpus, id: String, function: &'static str, accounts: Vec<Account>, target: usize,
                  borrows: Borrows, parse: for<'a> fn(&'a AccountView) -> Result<Ref<'a, T>, ProgramError>) {
    let world = World::new(accounts);
    let mut exclusive_views: Vec<AccountView> = borrows.exclusive.iter().map(|&j| world.views[j].clone()).collect();
    let _exclusive: Vec<RefMut<[u8]>> = exclusive_views.iter_mut().map(|v| v.try_borrow_mut().unwrap()).collect();
    let _shared: Vec<Ref<[u8]>> = borrows.shared.iter()
        .flat_map(|&(j, n)| (0..n).map(move |_| j))
        .map(|j| world.views[j].try_borrow().unwrap())
        .collect();
    let script = no_script();
    let before = state(&world, script.state_before(), vec![]);
    let outcome = shim::case(&script, || {
        let r = parse(&world.views[target]);
        let result = result_json(&r, |view| {
            let p = &**view as *const T as *const u8 as usize;
            let (j, offset) = world.data_offset(p).expect("Ref into an account's data");
            Json::obj([("account", j.into()), ("offset", offset.into()), ("len", core::mem::size_of::<T>().into())])
        });
        let after = after(&world, vec![]);
        drop(r);
        rec::returned(result, after)
    });
    c.push(record(id, function, vec![], before, Json::obj([("account", target.into())]), outcome));
}

/// A getter on the typed `Ref` of account `target` (parsed before the call).
fn getter_case<T>(c: &mut Corpus, id: String, function: &'static str, accounts: Vec<Account>, target: usize,
                  extra_shared: usize, parse: for<'a> fn(&'a AccountView) -> Result<Ref<'a, T>, ProgramError>,
                  call: impl FnOnce(&World, &T) -> Result<Json, String>) {
    let world = World::new(accounts);
    let view = parse(&world.views[target]).expect("typed view for a getter case");
    let _shared: Vec<Ref<[u8]>> = (0..extra_shared).map(|_| world.views[target].try_borrow().unwrap()).collect();
    let script = no_script();
    let before = state(&world, script.state_before(), vec![]);
    let len = core::mem::size_of::<T>();
    let (j, offset) = world.data_offset(&*view as *const T as usize).expect("Ref into an account's data");
    let args = Json::obj([("ref", Json::obj([("account", j.into()), ("offset", offset.into()), ("len", len.into())]))]);
    let outcome = shim::case(&script, || {
        let result = call(&world, &view);
        let after = after(&world, vec![]);
        match result {
            Ok(v) => rec::returned(v, after),
            Err(reason) => rec::unwound(reason, after),
        }
    });
    drop(view);
    c.push(record(id, function, vec![], before, args, outcome));
}

fn key_ref(world: &World, a: &Address) -> Json {
    let (j, offset) = world.data_offset(a as *const Address as usize).expect("field reference into account data");
    Json::obj([("account", j.into()), ("offset", offset.into()), ("value", rec::bytes(a.as_ref()))])
}

/// Case selection: every admission outcome class and check
/// order once, its first and last input (shortest and longest rejected
/// lengths, both sides of each layout boundary), the borrow-count boundaries
/// (1, 253 and 254 outstanding shared borrows), and getter boundary values.
pub fn record_version<A, M, S: core::fmt::Debug>(c: &mut Corpus, v: &Version<A, M, S>) {
    let id = v.id;
    let other = v.other_id;
    let account_from = name(v.krate, "account::Account::from_account_view");
    let mint_from = name(v.krate, "mint::Mint::from_account_view");

    // --- Account::from_account_view ---
    let mut n = 0;
    let mut acase = |c: &mut Corpus, what: &str, accounts: Vec<Account>, target: usize, borrows: Borrows| {
        n += 1;
        parser_case(c, format!("account_from_view/{n:02}_{what}"), account_from, accounts, target, borrows, v.account_from);
    };
    let base = |len: usize, ty: u8| with_type(account_data(len, 5, 0), ty);
    let ok = account(1, id, base(ACCOUNT_LEN, 0));
    acase(c, "base_free", vec![ok.clone()], 0, Borrows::default());
    acase(c, "invalid_state_byte", vec![account(2, id, account_data(ACCOUNT_LEN, 9, 7))], 0, Borrows::default());
    acase(c, "wrong_owner", vec![account(3, other, base(ACCOUNT_LEN, 0))], 0, Borrows::default());
    let lengths: &[(usize, u8)] = if v.token2022 {
        &[(0, 0), (164, 0), (166, 2), (166, 1), (MULTISIG_LEN, 2), (356, 2)]
    } else {
        &[(0, 0), (164, 0), (166, 2), (MULTISIG_LEN, 2)]
    };
    for &(len, ty) in lengths {
        acase(c, &format!("len_{len}_type_{ty}"), vec![account(4, id, base(len, ty))], 0, Borrows::default());
    }
    acase(c, "wrong_owner_and_length", vec![account(5, other, base(164, 0))], 0, Borrows::default());
    acase(c, "exclusive_borrow", vec![ok.clone()], 0, exclusive(0));
    acase(c, "wrong_owner_exclusive", vec![account(6, other, base(ACCOUNT_LEN, 0))], 0, exclusive(0));
    acase(c, "bad_length_exclusive", vec![account(7, id, base(164, 0))], 0, exclusive(0));
    if v.token2022 {
        acase(c, "bad_type_shared_1", vec![account(8, id, base(170, 1))], 0, shared(0, 1));
        acase(c, "extended_shared_2", vec![account(9, id, base(240, 2))], 0, shared(0, 2));
    }
    for k in [1usize, 253, 254] {
        acase(c, &format!("shared_{k}"), vec![ok.clone()], 0, shared(0, k));
    }
    acase(c, "second_of_two_other_exclusive", vec![account(10, id, base(ACCOUNT_LEN, 0)), ok.clone()], 1, exclusive(0));

    // --- Mint::from_account_view ---
    let mut n = 0;
    let mut mcase = |c: &mut Corpus, what: &str, accounts: Vec<Account>, target: usize, borrows: Borrows| {
        n += 1;
        parser_case(c, format!("mint_from_view/{n:02}_{what}"), mint_from, accounts, target, borrows, v.mint_from);
    };
    let mbase = |len: usize, ty: u8| with_type(mint_data(len, 6), ty);
    let mok = account(21, id, mbase(MINT_LEN, 0));
    mcase(c, "base_free", vec![mok.clone()], 0, Borrows::default());
    mcase(c, "wrong_owner", vec![account(22, other, mbase(MINT_LEN, 0))], 0, Borrows::default());
    let lengths: &[(usize, u8)] = if v.token2022 {
        &[(0, 0), (81, 0), (83, 0), (ACCOUNT_LEN, 0), (166, 1), (166, 2), (MULTISIG_LEN, 1), (356, 1)]
    } else {
        &[(0, 0), (81, 0), (83, 0), (MULTISIG_LEN, 1)]
    };
    for &(len, ty) in lengths {
        mcase(c, &format!("len_{len}_type_{ty}"), vec![account(23, id, mbase(len, ty))], 0, Borrows::default());
    }
    mcase(c, "wrong_owner_and_length", vec![account(24, other, mbase(81, 0))], 0, Borrows::default());
    mcase(c, "exclusive_borrow", vec![mok.clone()], 0, exclusive(0));
    mcase(c, "wrong_owner_exclusive", vec![account(25, other, mbase(MINT_LEN, 0))], 0, exclusive(0));
    mcase(c, "bad_length_exclusive", vec![account(26, id, mbase(81, 0))], 0, exclusive(0));
    if v.token2022 {
        mcase(c, "bad_type_shared_1", vec![account(27, id, mbase(170, 2))], 0, shared(0, 1));
    }
    for k in [1usize, 253, 254] {
        mcase(c, &format!("shared_{k}"), vec![mok.clone()], 0, shared(0, k));
    }
    mcase(c, "second_of_two", vec![account(28, id, mbase(10, 0)), mok.clone()], 1, Borrows::default());

    // --- Account getters on a live Ref<Account> ---
    let amount_fn = name(v.krate, "account::Account::amount");
    for (i, amount) in [0u64, 1, 1 << 63, u64::MAX].into_iter().enumerate() {
        let accounts = vec![account(40 + i as u8, id, account_data(ACCOUNT_LEN, amount, 1))];
        let f = v.amount;
        getter_case(c, format!("amount/{i:02}_{amount}"), amount_fn, accounts, 0, 0, v.account_from,
                    move |_, a| Ok(Json::from(f(a))));
    }
    {
        let accounts = vec![account(50, id, account_data(ACCOUNT_LEN, 1234, 2)), account(51, id, account_data(ACCOUNT_LEN, 0x0102_0304_0506_0708, 1))];
        let f = v.amount;
        getter_case(c, "amount/04_second_account_extra_borrows".into(), amount_fn, accounts, 1, 3, v.account_from,
                    move |_, a| Ok(Json::from(f(a))));
    }
    if v.token2022 {
        let accounts = vec![account(52, id, with_type(account_data(230, 987654321, 1), 2))];
        let f = v.amount;
        getter_case(c, "amount/05_extended_account".into(), amount_fn, accounts, 0, 0, v.account_from,
                    move |_, a| Ok(Json::from(f(a))));
    }
    for (field, getter) in [("mint", v.mint), ("owner", v.owner)] {
        let function = name(v.krate, &format!("account::Account::{field}"));
        let accounts = vec![account(60, id, account_data_keys(ACCOUNT_LEN))];
        getter_case(c, format!("{field}/00"), function, accounts, 0, 0, v.account_from,
                    move |w, a| Ok(key_ref(w, getter(a))));
        let accounts = vec![account(61, id, mint_data(MINT_LEN, 1)), account(62, id, account_data_keys(ACCOUNT_LEN))];
        getter_case(c, format!("{field}/01_second_account_extra_borrows"), function, accounts, 1, 5, v.account_from,
                    move |w, a| Ok(key_ref(w, getter(a))));
        if v.token2022 {
            let accounts = vec![account(63, id, with_type(account_data_keys(200), 2))];
            getter_case(c, format!("{field}/02_extended"), function, accounts, 0, 0, v.account_from,
                        move |w, a| Ok(key_ref(w, getter(a))));
        }
    }
    let state_fn = name(v.krate, "account::Account::state");
    for byte in [0u8, 1, 2, 3, 255] {
        let accounts = vec![account(70, id, account_data(ACCOUNT_LEN, 5, byte))];
        let f = v.state;
        getter_case(c, format!("state/byte_{byte:03}"), state_fn, accounts, 0, 0, v.account_from,
                    move |_, a| rec::catch(|| Json::from(format!("{:?}", f(a)))));
    }
    {
        let accounts = vec![account(71, id, account_data(ACCOUNT_LEN, 5, 9))];
        let f = v.state;
        getter_case(c, "state/byte_009_extra_borrows".into(), state_fn, accounts, 0, 2, v.account_from,
                    move |_, a| rec::catch(|| Json::from(format!("{:?}", f(a)))));
    }

    // --- Mint::decimals on a live Ref<Mint> ---
    let decimals_fn = name(v.krate, "mint::Mint::decimals");
    for (i, d) in [0u8, 6, 255].into_iter().enumerate() {
        let accounts = vec![account(80 + i as u8, id, mint_data(MINT_LEN, d))];
        let f = v.decimals;
        getter_case(c, format!("decimals/{i:02}_{d}"), decimals_fn, accounts, 0, 0, v.mint_from,
                    move |_, m| Ok(Json::from(f(m))));
    }
    {
        let accounts = vec![account(90, id, mint_data(0, 0)), account(91, id, mint_data(MINT_LEN, 3))];
        let f = v.decimals;
        getter_case(c, "decimals/03_second_account_extra_borrows".into(), decimals_fn, accounts, 1, 4, v.mint_from,
                    move |_, m| Ok(Json::from(f(m))));
    }
    if v.token2022 {
        let accounts = vec![account(92, id, with_type(mint_data(210, 11), 1))];
        let f = v.decimals;
        getter_case(c, "decimals/04_extended_mint".into(), decimals_fn, accounts, 0, 0, v.mint_from,
                    move |_, m| Ok(Json::from(f(m))));
    }
}
