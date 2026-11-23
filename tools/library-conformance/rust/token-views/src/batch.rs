//! pinocchio-token 0.6.0 Batch preparation: `Batch::new`, `Batch::invoke_signed`,
//! the single-owner `TransferChecked::new` and `IntoBatch::into_batch` at
//! `MultisigSigner = &AccountView` and at the scripted `ScriptedSigner`.
//!
//! The three buffers are fully initialized before every call (data bytes with
//! a pattern, account and metadata entries from a filler account), so every
//! slot is observable. `CpiAccount` entries are read as their `repr(C)` bytes
//! and their four pointers resolved to one account of the region;
//! `InstructionAccount` addresses are resolved likewise. The committed lengths
//! are private fields of `Batch`: `batch_lengths` reads them from the value
//! words, at positions calibrated once (`calibrate`).

use crate::common::*;
use conformance_accounts::Account;
use conformance_recorder::{self as rec, Corpus, Json};
use conformance_shim::{self as shim, Script};
use core::cell::RefCell;
use core::mem::MaybeUninit;
use pinocchio_token::instructions::{Batch, IntoBatch, TransferChecked};
use solana_account_view::{AccountView, Ref, RefMut};
use solana_instruction_view::cpi::{CpiAccount, Seed, Signer};
use solana_instruction_view::InstructionAccount;
use std::sync::OnceLock;

const NEW: &str = "pinocchio_token::instructions::batch::Batch::<'account, 'state>::new";
const INVOKE: &str = "pinocchio_token::instructions::batch::Batch::<'account, 'state>::invoke_signed";
const TC_NEW: &str = "pinocchio_token::instructions::transfer_checked::TransferChecked::<'account, '_, &'account solana_account_view::AccountView>::new";
const INTO: &str = "<pinocchio_token::instructions::transfer_checked::TransferChecked<'_, '_, MultisigSigner> as pinocchio_token::instructions::batch::IntoBatch>::into_batch";
const IDENTITY: &str = "&solana_account_view::AccountView";
const SCRIPTED: &str = "conformance_token_views::ScriptedSigner";

// ---------------------------------------------------------------------------
// Scripted signers
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub enum Step {
    Ret(usize),
    Panic,
}

/// The script of one case: `as_ref` call `k` (counted over both passes)
/// logs its signer id and then follows step `k`.
pub struct ScriptCtx<'a> {
    views: &'a [AccountView],
    steps: Vec<Step>,
    log: RefCell<Vec<u64>>,
}

pub struct ScriptedSigner<'a> {
    id: u64,
    ctx: &'a ScriptCtx<'a>,
}

impl AsRef<AccountView> for ScriptedSigner<'_> {
    fn as_ref(&self) -> &AccountView {
        let k = {
            let mut log = self.ctx.log.borrow_mut();
            log.push(self.id);
            log.len() - 1
        };
        match self.ctx.steps.get(k) {
            Some(Step::Ret(j)) => &self.ctx.views[*j],
            Some(Step::Panic) => panic!("scripted as_ref panic"),
            None => panic!("as_ref script exhausted"),
        }
    }
}

fn steps_json(steps: &[Step]) -> Json {
    Json::arr(steps.iter(), |s| match s {
        Step::Ret(j) => Json::obj([("return", (*j).into())]),
        Step::Panic => Json::from("panic"),
    })
}

// ---------------------------------------------------------------------------
// Buffers and observations
// ---------------------------------------------------------------------------

struct Bufs<'w> {
    data: Vec<MaybeUninit<u8>>,
    metas: Vec<MaybeUninit<InstructionAccount<'w>>>,
    accounts: Vec<MaybeUninit<CpiAccount<'w>>>,
}

/// Raw views of the three buffers, for observation while a `Batch` holds them.
#[derive(Clone, Copy)]
struct Raw {
    data: (*const u8, usize),
    metas: (*const u8, usize),
    accounts: (*const u8, usize),
}

impl<'w> Bufs<'w> {
    fn new(world: &'w World, filler: usize, data: usize, metas: usize, accounts: usize) -> Bufs<'w> {
        let v = &world.views[filler];
        Bufs {
            data: (0..data).map(|i| MaybeUninit::new(0xa0 ^ (i as u8).wrapping_mul(3))).collect(),
            metas: (0..metas).map(|i| MaybeUninit::new(InstructionAccount::new(v.address(), i % 2 == 0, i % 3 == 0))).collect(),
            accounts: (0..accounts)
                .map(|_| {
                    let mut m = MaybeUninit::uninit();
                    CpiAccount::init_from_account_view(v, &mut m);
                    m
                })
                .collect(),
        }
    }

    fn raw(&self) -> Raw {
        Raw {
            data: (self.data.as_ptr() as *const u8, self.data.len()),
            metas: (self.metas.as_ptr() as *const u8, self.metas.len()),
            accounts: (self.accounts.as_ptr() as *const u8, self.accounts.len()),
        }
    }
}

unsafe fn word(p: *const u8, at: usize) -> usize {
    (p.add(at) as *const usize).read_unaligned()
}

/// Every slot of the three buffers (all initialized by construction). Entries
/// are tuples: metadata `[account, is_signer, is_writable]`, CPI accounts
/// `[account, data_len, rent_epoch, is_signer, is_writable, executable, padding]`.
fn buffers_json(world: &World, raw: Raw) -> Json {
    unsafe {
        let data = core::slice::from_raw_parts(raw.data.0, raw.data.1);
        let meta_size = core::mem::size_of::<InstructionAccount>();
        let metas = Json::arr(0..raw.metas.1, |i| {
            let m = &*(raw.metas.0.add(i * meta_size) as *const InstructionAccount);
            let address = m.address as *const _ as usize;
            let account = world.field_of(address, ADDRESS_AT).map_or(Json::from("unresolved"), Json::from);
            Json::Arr(vec![account, (m.is_signer as u8).into(), (m.is_writable as u8).into()])
        });
        let size = core::mem::size_of::<CpiAccount>();
        let accounts = Json::arr(0..raw.accounts.1, |i| cpi_account_json(world, raw.accounts.0.add(i * size)));
        Json::obj([("data", rec::bytes(data)), ("accounts", accounts), ("instruction_accounts", metas)])
    }
}

/// A `CpiAccount` (`repr(C)`: address, lamports, data_len, data, owner,
/// rent_epoch, is_signer, is_writable, executable, padding byte), as
/// `[account, data_len, rent_epoch, is_signer, is_writable, executable, padding]`.
unsafe fn cpi_account_json(world: &World, p: *const u8) -> Json {
    let fields = [world.field_of(word(p, 0), ADDRESS_AT), world.field_of(word(p, 8), LAMPORTS_AT),
                  world.field_of(word(p, 24), DATA_AT), world.field_of(word(p, 32), OWNER_AT)];
    let account = match fields {
        [Some(a), Some(b), Some(c), Some(d)] if a == b && b == c && c == d => Json::from(a),
        _ => Json::from("unresolved"),
    };
    Json::Arr(vec![account, (word(p, 16) as u64).into(), (word(p, 40) as u64).into(), (*p.add(48)).into(),
                   (*p.add(49)).into(), (*p.add(50)).into(), (*p.add(51)).into()])
}

/// Word positions of `data_len` and of the two account lengths in `Batch`.
static LENGTH_WORDS: OnceLock<(usize, usize, usize)> = OnceLock::new();

fn length_candidates(batch: &Batch, raw: Raw) -> Vec<usize> {
    assert_eq!(core::mem::size_of::<Batch>(), 9 * 8, "Batch is three slices and three lengths");
    let p = batch as *const Batch as *const u8;
    let words: Vec<usize> = (0..9).map(|i| unsafe { word(p, 8 * i) }).collect();
    let mut used = [false; 9];
    for (ptr, len) in [raw.data, raw.metas, raw.accounts] {
        let i = words.iter().position(|&w| w == ptr as usize).expect("slice pointer in Batch");
        let j = if i + 1 < 9 && words[i + 1] == len { i + 1 } else { assert!(i > 0 && words[i - 1] == len); i - 1 };
        used[i] = true;
        used[j] = true;
    }
    (0..9).filter(|&i| !used[i]).collect()
}

/// Calibrate on a fresh batch, whose lengths are (1, 0, 0), over buffers of
/// lengths that differ from these values.
pub fn calibrate(world: &World) {
    let mut b = Bufs::new(world, 0, 37, 41, 43);
    let raw = b.raw();
    let batch = Batch::new(&mut b.data, &mut b.metas, &mut b.accounts).unwrap();
    let rest = length_candidates(&batch, raw);
    assert_eq!(rest.len(), 3);
    let p = &batch as *const Batch as *const u8;
    let values: Vec<usize> = rest.iter().map(|&i| unsafe { word(p, 8 * i) }).collect();
    let d = values.iter().position(|&v| v == 1).expect("data_len word");
    let others: Vec<usize> = (0..3).filter(|&k| k != d).map(|k| rest[k]).collect();
    assert!(others.iter().all(|&i| unsafe { word(p, 8 * i) } == 0));
    LENGTH_WORDS.set((rest[d], others[0], others[1])).unwrap();
}

/// The committed lengths. Every `IntoBatch` commits as many CPI accounts as
/// metadata entries, so the two account lengths are equal in every reachable
/// state; this is asserted, and their word order does not matter.
fn batch_lengths(batch: &Batch, raw: Raw) -> Json {
    let (d, a, m) = *LENGTH_WORDS.get().expect("calibrated");
    let rest = length_candidates(batch, raw);
    assert!(rest.contains(&d) && rest.contains(&a) && rest.contains(&m));
    let p = batch as *const Batch as *const u8;
    let (dl, al, ml) = unsafe { (word(p, 8 * d), word(p, 8 * a), word(p, 8 * m)) };
    assert_eq!(al, ml, "account and metadata lengths differ");
    Json::obj([("data", dl.into()), ("accounts", al.into()), ("instruction_accounts", ml.into())])
}

// ---------------------------------------------------------------------------
// Worlds
// ---------------------------------------------------------------------------

/// Accounts: 0 filler, 1 source, 2 mint, 3 destination, 4 authority, 5..7 signers.
fn world_accounts() -> Vec<Account> {
    let token = pinocchio_token::ID.to_bytes();
    let mut v = vec![
        account(100, [0; 32], bytes(100, 2)),
        account(101, token, bytes(101, 4)),
        account(102, token, bytes(102, 2)),
        account(103, token, bytes(103, 3)),
        account(104, [0; 32], vec![]),
    ];
    for s in 0..3u8 {
        v.push(account(105 + s, [0; 32], bytes(105 + s as u64, s as usize)));
    }
    v[2].is_writable = false;
    v[4].is_signer = true;
    v[4].is_writable = false;
    v[5].is_signer = true;
    v[6].is_signer = true;
    v[6].executable = true;
    v[7].is_writable = false;
    v
}

/// The world accounts up to the highest index a case uses (account 0, the
/// filler, is always present).
fn world_upto(indices: impl IntoIterator<Item = usize>) -> World {
    let last = indices.into_iter().max().unwrap_or(0);
    World::new(world_accounts().into_iter().take(last + 1).collect())
}

fn tc_indices(t: &Tc) -> Vec<usize> {
    let mut v = vec![t.from, t.mint, t.to, t.authority];
    v.extend(&t.signers);
    v
}

fn scenario_indices(s: &Scenario) -> Vec<usize> {
    let mut v: Vec<usize> = s.prior.iter().flat_map(tc_indices).collect();
    v.extend(&s.held.shared);
    v.extend(&s.held.exclusive);
    v
}

#[derive(Clone)]
struct Tc {
    from: usize,
    mint: usize,
    to: usize,
    authority: usize,
    amount: u64,
    decimals: u8,
    signers: Vec<usize>,
}

fn tc(signers: &[usize]) -> Tc {
    Tc { from: 1, mint: 2, to: 3, authority: 4, amount: 1_000_000_007, decimals: 6, signers: signers.to_vec() }
}

fn tc_args(t: &Tc, signers: Json) -> Vec<(&'static str, Json)> {
    vec![("from", t.from.into()), ("mint", t.mint.into()), ("to", t.to.into()), ("authority", t.authority.into()),
         ("amount", t.amount.into()), ("decimals", t.decimals.into()), ("multisig_signers", signers)]
}

/// `into_batch` requires the signer slice to outlive the batch account
/// lifetime, so the slice is leaked (a few bytes per case).
fn push_identity<'w>(world: &'w World, batch: &mut Batch<'w, '_>, t: &Tc)
                     -> Result<(), solana_program_error::ProgramError> {
    let v = &world.views;
    let signers: &'w [&'w AccountView] = Box::leak(t.signers.iter().map(|&j| &v[j]).collect::<Vec<_>>().into_boxed_slice());
    TransferChecked::with_multisig_signers(&v[t.from], &v[t.mint], &v[t.to], &v[t.authority], t.amount, t.decimals,
                                           signers)
        .into_batch(batch)
}

/// The borrows held across a call.
#[derive(Clone, Default)]
struct Held {
    shared: Vec<usize>,
    exclusive: Vec<usize>,
}

/// One Batch scenario: buffer sizes, prior pushes, held borrows.
#[derive(Clone)]
struct Scenario {
    data: usize,
    metas: usize,
    accounts: usize,
    prior: Vec<Tc>,
    held: Held,
}

fn scenario(data: usize, metas: usize, accounts: usize) -> Scenario {
    Scenario { data, metas, accounts, prior: vec![], held: Held::default() }
}

fn hold<'v>(world: &'v World, held: &Held, exclusive_views: &'v mut Vec<AccountView>)
            -> (Vec<Ref<'v, [u8]>>, Vec<RefMut<'v, [u8]>>) {
    *exclusive_views = held.exclusive.iter().map(|&j| world.views[j].clone()).collect();
    let shared = held.shared.iter().map(|&j| world.views[j].try_borrow().unwrap()).collect();
    let exclusive = exclusive_views.iter_mut().map(|v| v.try_borrow_mut().unwrap()).collect();
    (shared, exclusive)
}

// ---------------------------------------------------------------------------
// Cases
// ---------------------------------------------------------------------------

fn new_case(c: &mut Corpus, id: &str, data: usize, metas: usize, accounts: usize) {
    let world = world_upto([0]);
    let mut b = Bufs::new(&world, 0, data, metas, accounts);
    let raw = b.raw();
    let script = no_script();
    let before = state(&world, script.state_before(), vec![("buffers", buffers_json(&world, raw))]);
    let outcome = shim::case(&script, || {
        let r = Batch::new(&mut b.data, &mut b.metas, &mut b.accounts);
        let result = result_json(&r, |batch| batch_lengths(batch, raw));
        drop(r);
        rec::returned(result, after(&world, vec![("buffers", buffers_json(&world, raw))]))
    });
    c.push(record(format!("batch_new/{id}"), NEW, vec![], before, Json::Null, outcome));
}

fn tc_new_case(c: &mut Corpus, id: &str, t: Tc) {
    let world = world_upto(tc_indices(&t));
    let script = no_script();
    let before = state(&world, script.state_before(), vec![]);
    let args = Json::Obj(tc_args(&t, Json::Arr(vec![])).into_iter().filter(|(k, _)| *k != "multisig_signers")
        .map(|(k, v)| (k.to_string(), v)).collect());
    let outcome = shim::case(&script, || {
        let v = &world.views;
        let r = TransferChecked::new(&v[t.from], &v[t.mint], &v[t.to], &v[t.authority], t.amount, t.decimals);
        let result = Json::obj([
            ("from", world.view_index(r.from).into()), ("mint", world.view_index(r.mint).into()),
            ("to", world.view_index(r.to).into()), ("authority", world.view_index(r.authority).into()),
            ("multisig_signers", Json::arr(r.multisig_signers.iter(), |s| world.view_index(s).into())),
            ("amount", r.amount.into()), ("decimals", r.decimals.into()),
        ]);
        rec::returned(result, after(&world, vec![]))
    });
    c.push(record(format!("transfer_checked_new/{id}"), TC_NEW, vec![], before, args, outcome));
}

fn into_identity_case(c: &mut Corpus, id: &str, s: Scenario, t: Tc) {
    let world = world_upto(scenario_indices(&s).into_iter().chain(tc_indices(&t)));
    let mut b = Bufs::new(&world, 0, s.data, s.metas, s.accounts);
    let raw = b.raw();
    let mut batch = Batch::new(&mut b.data, &mut b.metas, &mut b.accounts).unwrap();
    for p in &s.prior {
        push_identity(&world, &mut batch, p).unwrap();
    }
    let mut exclusive_views = Vec::new();
    let _held = hold(&world, &s.held, &mut exclusive_views);
    let script = no_script();
    let observe = |batch: &Batch, syscalls: Json| {
        state(&world, syscalls, vec![("buffers", buffers_json(&world, raw)), ("lengths", batch_lengths(batch, raw)),
                                     ("asref_log", Json::Arr(vec![]))])
    };
    let before = observe(&batch, script.state_before());
    let args = Json::Obj(tc_args(&t, Json::arr(t.signers.iter(), |&j| j.into())).into_iter()
        .map(|(k, v)| (k.to_string(), v)).collect());
    let outcome = shim::case(&script, || {
        let r = push_identity(&world, &mut batch, &t);
        rec::returned(result_json(&r, |_| Json::Null), observe(&batch, shim::state()))
    });
    c.push(record(format!("into_batch_identity/{id}"), INTO, vec![("MultisigSigner", IDENTITY.to_string())], before,
                  args, outcome));
}

fn into_scripted_case(c: &mut Corpus, id: &str, s: Scenario, t: Tc, ids: &[u64], steps: Vec<Step>) {
    let returned = steps.iter().filter_map(|s| match s { Step::Ret(j) => Some(*j), Step::Panic => None }).collect::<Vec<_>>();
    let world = world_upto(scenario_indices(&s).into_iter().chain(tc_indices(&t)).chain(returned));
    let ctx = ScriptCtx { views: &world.views, steps: steps.clone(), log: RefCell::new(Vec::new()) };
    let signers: Vec<ScriptedSigner> = ids.iter().map(|&id| ScriptedSigner { id, ctx: &ctx }).collect();
    let mut b = Bufs::new(&world, 0, s.data, s.metas, s.accounts);
    let raw = b.raw();
    let mut batch = Batch::new(&mut b.data, &mut b.metas, &mut b.accounts).unwrap();
    for p in &s.prior {
        push_identity(&world, &mut batch, p).unwrap();
    }
    let mut exclusive_views = Vec::new();
    let _held = hold(&world, &s.held, &mut exclusive_views);
    let script = no_script();
    let observe = |batch: &Batch, syscalls: Json| {
        state(&world, syscalls, vec![("buffers", buffers_json(&world, raw)), ("lengths", batch_lengths(batch, raw)),
                                     ("asref_log", Json::arr(ctx.log.borrow().iter(), |&i| i.into()))])
    };
    let before = observe(&batch, script.state_before());
    let mut args = tc_args(&t, Json::arr(ids.iter(), |&i| i.into()));
    args.push(("script", steps_json(&steps)));
    let args = Json::Obj(args.into_iter().map(|(k, v)| (k.to_string(), v)).collect());
    let outcome = shim::case(&script, || {
        let v = &world.views;
        let r = rec::catch(|| {
            TransferChecked::with_multisig_signers(&v[t.from], &v[t.mint], &v[t.to], &v[t.authority], t.amount,
                                                   t.decimals, &signers)
                .into_batch(&mut batch)
        });
        let after = observe(&batch, shim::state());
        match r {
            Ok(r) => rec::returned(result_json(&r, |_| Json::Null), after),
            Err(reason) => rec::unwound(reason, after),
        }
    });
    c.push(record(format!("into_batch_scripted/{id}"), INTO, vec![("MultisigSigner", SCRIPTED.to_string())], before,
                  args, outcome));
}

fn invoke_case(c: &mut Corpus, id: &str, s: Scenario, failed: Option<Tc>, signers: Vec<Vec<Vec<u8>>>, script: Script) {
    let world = world_upto(scenario_indices(&s).into_iter().chain(failed.iter().flat_map(tc_indices)));
    let mut b = Bufs::new(&world, 0, s.data, s.metas, s.accounts);
    let raw = b.raw();
    let mut batch = Batch::new(&mut b.data, &mut b.metas, &mut b.accounts).unwrap();
    for p in &s.prior {
        push_identity(&world, &mut batch, p).unwrap();
    }
    if let Some(f) = &failed {
        assert!(push_identity(&world, &mut batch, f).is_err());
    }
    let mut exclusive_views = Vec::new();
    let _held = hold(&world, &s.held, &mut exclusive_views);
    let observe = |batch: &Batch, syscalls: Json| {
        state(&world, syscalls, vec![("buffers", buffers_json(&world, raw)), ("lengths", batch_lengths(batch, raw))])
    };
    let before = observe(&batch, script.state_before());
    let args = Json::obj([("signers", Json::arr(signers.iter(), |s| Json::arr(s.iter(), |b| rec::bytes(b))))]);
    let outcome = shim::case(&script, || {
        let seeds: Vec<Vec<Seed>> = signers.iter().map(|s| s.iter().map(|b| Seed::from(b.as_slice())).collect()).collect();
        let signer_values: Vec<Signer> = seeds.iter().map(|s| Signer::from(s.as_slice())).collect();
        let r = batch.invoke_signed(&signer_values);
        rec::returned(result_json(&r, |_| Json::Null), observe(&batch, shim::state()))
    });
    c.push(record(format!("batch_invoke_signed/{id}"), INVOKE, vec![], before, args, outcome));
}

/// Case selection: each outcome class of each writer stage
/// once with its boundary (one slot short and exact), each check order
/// (header room, data room, account capacity before the borrow flags, borrow
/// flags before metadata capacity), the borrow flags that are and are not
/// checked, and for the scripted signer an unwind at each callback position.
/// Buffers are sized to the case plus one spare slot, so the untouched suffix
/// is observed.
pub fn record_all(c: &mut Corpus) {
    calibrate(&World::new(world_accounts()));

    // Batch::new: the empty data buffer fails, any other writes byte 0.
    for (id, d, m, a) in [("data_0", 0, 0, 0), ("data_0_accounts_2", 0, 2, 2), ("data_1", 1, 0, 0),
                          ("data_3_accounts_2", 3, 2, 1)] {
        new_case(c, id, d, m, a);
    }

    // TransferChecked::new (single owner).
    tc_new_case(c, "distinct", tc(&[]));
    tc_new_case(c, "aliases_max_values", Tc { from: 1, mint: 1, to: 1, authority: 1, amount: u64::MAX, decimals: 255,
                                             signers: vec![] });

    // into_batch, MultisigSigner = &AccountView.
    let fit = |m: usize| scenario(14, 5 + m, 5 + m);
    into_identity_case(c, "single_owner", fit(0), tc(&[]));
    into_identity_case(c, "duplicate_signers", fit(4), tc(&[5, 5, 7, 4]));
    into_identity_case(c, "aliased_accounts_max_values", fit(1),
                       Tc { from: 3, mint: 3, to: 3, authority: 3, amount: u64::MAX, decimals: 255, signers: vec![3] });
    into_identity_case(c, "after_one_instruction", Scenario { prior: vec![tc(&[5])], ..scenario(26, 12, 12) },
                       tc(&[6, 7]));
    into_identity_case(c, "header_room_missing", scenario(2, 5, 5), tc(&[]));
    into_identity_case(c, "second_header_room_missing", Scenario { prior: vec![tc(&[])], ..scenario(14, 9, 9) },
                       tc(&[]));
    into_identity_case(c, "data_room_missing_12", scenario(12, 5, 5), tc(&[]));
    into_identity_case(c, "data_exact_13", scenario(13, 5, 5), tc(&[]));
    into_identity_case(c, "accounts_room_missing", scenario(14, 7, 5), tc(&[5, 6]));
    into_identity_case(c, "accounts_exact", scenario(14, 7, 6), tc(&[5, 6]));
    into_identity_case(c, "metas_room_missing", scenario(14, 5, 7), tc(&[5, 6]));
    into_identity_case(c, "metas_exact", scenario(14, 6, 6), tc(&[5, 6]));
    let held = |shared: Vec<usize>, exclusive: Vec<usize>, s: Scenario| Scenario { held: Held { shared, exclusive }, ..s };
    into_identity_case(c, "source_shared_borrow", held(vec![1], vec![], fit(0)), tc(&[]));
    into_identity_case(c, "destination_exclusive_borrow", held(vec![], vec![3], fit(1)), tc(&[5]));
    into_identity_case(c, "unchecked_borrows", held(vec![4], vec![2, 5], fit(1)), tc(&[5]));
    into_identity_case(c, "capacity_before_borrow", held(vec![1], vec![], scenario(14, 5, 3)), tc(&[]));
    into_identity_case(c, "borrow_before_metas_capacity", held(vec![], vec![3], scenario(14, 2, 5)), tc(&[]));

    // into_batch, MultisigSigner = ScriptedSigner.
    use Step::*;
    into_scripted_case(c, "pass_dependent_accounts", fit(2), tc(&[]), &[10, 11], vec![Ret(5), Ret(6), Ret(7), Ret(1)]);
    into_scripted_case(c, "duplicate_signers", fit(3), tc(&[]), &[3, 3, 3],
                       vec![Ret(1), Ret(2), Ret(3), Ret(3), Ret(2), Ret(1)]);
    into_scripted_case(c, "panic_first_call", fit(2), tc(&[]), &[10, 11], vec![Panic]);
    into_scripted_case(c, "script_exhausted", fit(1), tc(&[]), &[10], vec![Ret(5)]);
    into_scripted_case(c, "panic_second_call", fit(2), tc(&[]), &[10, 11], vec![Ret(5), Panic]);
    into_scripted_case(c, "panic_first_metadata_call", fit(2), tc(&[]), &[10, 11], vec![Ret(5), Ret(6), Panic]);
    into_scripted_case(c, "panic_last_call", fit(2), tc(&[]), &[10, 11], vec![Ret(5), Ret(6), Ret(7), Panic]);
    into_scripted_case(c, "panic_after_prior_instruction", Scenario { prior: vec![tc(&[5])], ..scenario(26, 11, 11) },
                       tc(&[]), &[20], vec![Ret(6), Panic]);
    into_scripted_case(c, "metas_capacity_after_calls", scenario(14, 5, 7), tc(&[]), &[10, 11],
                       vec![Ret(5), Ret(6), Panic]);
    into_scripted_case(c, "borrow_no_calls", held(vec![1], vec![], fit(1)), tc(&[]), &[10], vec![Panic]);

    // Batch::invoke_signed: the shim logs the committed prefixes.
    let one = Scenario { prior: vec![tc(&[])], ..scenario(14, 5, 5) };
    invoke_case(c, "empty_batch", scenario(2, 1, 1), None, vec![], invoke_reply(0));
    invoke_case(c, "one_instruction", one.clone(), None, vec![], invoke_reply(0));
    invoke_case(c, "two_instructions_seeds", Scenario { prior: vec![tc(&[5, 6]), tc(&[7])], ..scenario(26, 12, 12) },
                None, vec![vec![b"vault".to_vec(), vec![254]], vec![], vec![vec![], vec![1, 2, 3]]], invoke_reply(7));
    invoke_case(c, "after_failed_push", Scenario { prior: vec![tc(&[])], ..scenario(26, 5, 5) }, Some(tc(&[5])), vec![],
                invoke_reply(0));
    invoke_case(c, "borrowed_accounts", Scenario { held: Held { shared: vec![1], exclusive: vec![3] }, ..one.clone() },
                None, vec![], invoke_reply(0));
    invoke_case(c, "callee_fails", one.clone(), None, vec![vec![b"x".to_vec()]], invoke_terminates());
}
