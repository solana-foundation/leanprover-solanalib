//! solana-instruction-view 1.0.0: `Seed::from(&[u8])`, `Signer::from(&[Seed])` and the checked
//! slice entries `invoke_signed_with_slice` / `invoke_with_slice` (the `slice-cpi` feature, as
//! the default `alloc` feature in pinocchio 0.10.2 enables it in this profile).
//!
//! CPI cases run as in the instruction-view 2.1.0 driver: a loader input region, one `AccountView` per
//! entry (a duplicate views its target), live borrows taken through the AccountView API, and the
//! shim `sol_invoke_signed_c` under the case script.

use conformance_accounts::{Account, Entry, Input, Region};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, AccountWrite, Reply, Script};
use solana_account_view::{AccountView, RuntimeAccount};
use solana_address::Address;
use solana_instruction_view::cpi::{invoke_signed_with_slice, invoke_with_slice, Seed, Signer};
use solana_instruction_view::{InstructionAccount, InstructionView};
use solana_program_error::ProgramError;

const SEED_SLICE: &str = "<solana_instruction_view::cpi::Seed<'a> as core::convert::From<&'a [u8]>>::from";
const SIGNER_SLICE: &str = "<solana_instruction_view::cpi::Signer<'a, 'b> as core::convert::From<&'b [solana_instruction_view::cpi::Seed<'a>]>>::from";
const SIGNED: &str = "solana_instruction_view::cpi::invoke_signed_with_slice";
const UNSIGNED: &str = "solana_instruction_view::cpi::invoke_with_slice";

#[repr(C)]
struct RawSeed {
    ptr: *const u8,
    len: u64,
}

#[repr(C)]
struct RawSigner {
    ptr: *const RawSeed,
    len: u64,
}

fn signer_seeds(signer: &Signer) -> Vec<Vec<u8>> {
    assert_eq!(std::mem::size_of::<Signer>(), std::mem::size_of::<RawSigner>());
    let raw = unsafe { &*(signer as *const Signer as *const RawSigner) };
    (0..raw.len as usize)
        .map(|i| {
            let s = unsafe { &*raw.ptr.add(i) };
            if s.len == 0 { vec![] } else { unsafe { std::slice::from_raw_parts(s.ptr, s.len as usize) }.to_vec() }
        })
        .collect()
}

fn push_value(c: &mut Corpus, id: String, function: &'static str, args: Json, result: Json) {
    c.push(Record { id, function, generics: vec![], layout: None, state: Json::Null, args,
        outcome: rec::returned(result, Json::Null), observed: None });
}

pub fn record_values(c: &mut Corpus) {
    let long: Vec<u8> = (0..40u8).collect();
    for (label, bytes) in [("empty", &[][..]), ("one", &[7u8][..]), ("seed32", &long[..32]), ("over_pda_limit40", &long[..])] {
        let seed = Seed::from(bytes);
        assert_eq!(seed.as_ptr(), bytes.as_ptr());
        push_value(c, format!("seed_from_slice/{label}"), SEED_SLICE, Json::obj([("bytes", rec::bytes(bytes))]),
            rec::bytes(&seed));
    }
    let groups: [(&str, Vec<&[u8]>); 4] = [
        ("empty", vec![]),
        ("one_empty_seed", vec![&[]]),
        ("two", vec![b"vault", &[0xfe]]),
        ("duplicates", vec![b"a", b"a", b"", b"a"]),
    ];
    for (label, seeds) in groups {
        let array: Vec<Seed> = seeds.iter().map(|s| Seed::from(*s)).collect();
        let signer = Signer::from(&array[..]);
        let raw = unsafe { &*(&signer as *const Signer as *const RawSigner) };
        assert_eq!(raw.ptr as usize, array.as_ptr() as usize);
        push_value(c, format!("signer_from_slice/{label}"), SIGNER_SLICE,
            Json::obj([("seeds", Json::arr(seeds.iter(), |s| rec::bytes(s)))]),
            Json::arr(signer_seeds(&signer).iter(), |s| rec::bytes(s)));
    }
}

#[derive(Clone, Copy)]
enum Borrow {
    Shared,
    Mut,
}

/// `start`, 30 zero bytes and `start + 1`: distinct keys with a compact zero run.
fn key32(start: u8) -> [u8; 32] {
    let mut k = [0u8; 32];
    k[0] = start;
    k[31] = start.wrapping_add(1);
    k
}

fn account(key: u8, signer: bool, writable: bool, lamports: u64, data: &[u8]) -> Entry {
    Entry::Account(Account { key: key32(key), owner: [0; 32], lamports, data: data.to_vec(), is_signer: signer,
        is_writable: writable, executable: false, rent_epoch: 0 })
}

/// The first `n` of the standard entries (a case serializes only the entries it uses).
fn standard_input(n: usize) -> Input {
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

fn with_views<R>(input: &Input, borrows: &[(usize, Borrow)], call: impl FnOnce(&[AccountView], &Region) -> R) -> R {
    let mut region = input.serialize();
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
        match b {
            Borrow::Shared => core::mem::forget(views[*i].try_borrow().expect("shared borrow")),
            Borrow::Mut => core::mem::forget(views[*i].try_borrow_mut().expect("exclusive borrow")),
        }
    }
    call(&views, &region)
}

struct Meta {
    key: [u8; 32],
    writable: bool,
    signer: bool,
}

fn m(k: u8, writable: bool, signer: bool) -> Meta {
    Meta { key: key32(k), writable, signer }
}

fn meta_json(m: &Meta) -> Json {
    Json::obj([("pubkey", rec::bytes(&m.key)), ("is_signer", m.signer.into()), ("is_writable", m.writable.into())])
}

/// The instruction metas; more than 8 equal metas are written `{"repeat": n, "meta": m}`.
fn metas_json(metas: &[Meta]) -> Json {
    let same = metas.windows(2).all(|w| w[0].key == w[1].key && w[0].writable == w[1].writable && w[0].signer == w[1].signer);
    if metas.len() > 8 && same {
        Json::obj([("repeat", metas.len().into()), ("meta", meta_json(&metas[0]))])
    } else {
        Json::arr(metas.iter(), meta_json)
    }
}

fn signers_json(signers: &[&[&[u8]]]) -> Json {
    Json::arr(signers.iter(), |s| Json::arr(s.iter(), |b| rec::bytes(b)))
}

fn with_signers<R>(signers: &[&[&[u8]]], f: impl FnOnce(&[Signer]) -> R) -> R {
    let seeds: Vec<Vec<Seed>> = signers.iter().map(|s| s.iter().map(|b| Seed::from(*b)).collect()).collect();
    let signers: Vec<Signer> = seeds.iter().map(|s| Signer::from(&s[..])).collect();
    f(&signers)
}

fn cpi_ok() -> Script {
    Script::new(vec![Reply::new("sol_invoke_signed_c", 0)])
}

fn no_cpi() -> Script {
    Script::new(vec![])
}

fn cpi_writes(data: Option<Vec<u8>>) -> Script {
    Script::new(vec![Reply::new("sol_invoke_signed_c", 0).write(AccountWrite {
        account: 0, lamports: Some(4), data, owner: Some(key32(0x55)) })])
}

fn cpi_terminates() -> Script {
    Script::new(vec![Reply::new("sol_invoke_signed_c", 0).terminate("callee failed")])
}

#[allow(clippy::too_many_arguments)]
fn slice_case(c: &mut Corpus, signed: bool, label: &str, metas: Vec<Meta>, data: Vec<u8>, accounts: Vec<usize>,
              signers: &'static [&'static [&'static [u8]]], borrows: Vec<(usize, Borrow)>, script: Script) {
    let input = standard_input(needed(accounts.iter().copied().chain(borrows.iter().map(|b| b.0))));
    let program = key32(0xc0);
    let mut args = vec![
        ("instruction".to_string(), Json::obj([
            ("program_id", rec::bytes(&program)),
            ("accounts", metas_json(&metas)),
            ("data", rec::bytes(&data)),
        ])),
        ("accounts".to_string(), Json::arr(accounts.iter(), |i| Json::from(*i))),
    ];
    if signed {
        args.push(("signers".to_string(), signers_json(signers)));
    }
    let call = |views: &[AccountView]| -> Result<(), ProgramError> {
        let program = Address::new_from_array(program);
        let keys: Vec<Address> = metas.iter().map(|m| Address::new_from_array(m.key)).collect();
        let ias: Vec<InstructionAccount> =
            metas.iter().zip(keys.iter()).map(|(m, k)| InstructionAccount::new(k, m.writable, m.signer)).collect();
        let instruction = InstructionView { program_id: &program, data: &data, accounts: &ias };
        let list: Vec<&AccountView> = accounts.iter().map(|i| &views[*i]).collect();
        if signed {
            with_signers(signers, |s| invoke_signed_with_slice(&instruction, &list, s))
        } else {
            invoke_with_slice(&instruction, &list)
        }
    };
    let before = with_views(&input, &borrows, |_, region| region.read_back());
    let state = Json::obj([("region", before), ("syscalls", script.state_before())]);
    let outcome = shim::case(&script, || {
        with_views(&input, &borrows, |views, region| {
            let result = match call(views) {
                Ok(()) => rec::ok(Json::Null),
                Err(e) => rec::err(format!("{e:?}").into()),
            };
            rec::returned(result, Json::obj([("region", region.read_back()), ("syscalls", shim::state())]))
        })
    });
    let (function, prefix) = if signed { (SIGNED, "invoke_signed_with_slice") } else { (UNSIGNED, "invoke_with_slice") };
    c.push(Record { id: format!("{prefix}/{label}"), function, generics: vec![], layout: None, state,
        args: Json::Obj(args), outcome, observed: None });
}

pub fn record_slices(c: &mut Corpus) {
    const NONE: &[&[&[u8]]] = &[];
    const NESTED: &[&[&[u8]]] = &[&[b"a", b"bc"], &[], &[b""]];
    for signed in [true, false] {
        let signers = if signed { NESTED } else { NONE };
        slice_case(c, signed, "ok_asymmetric_flags", vec![m(0x10, false, true), m(0x30, true, false)], vec![7, 9],
            vec![0, 1], signers, vec![], cpi_ok());
        slice_case(c, signed, "too_few_accounts", vec![m(0x10, true, true), m(0x30, true, false)], vec![],
            vec![0], signers, vec![], no_cpi());
        slice_case(c, signed, "readonly_exclusive_borrow", vec![m(0x10, false, false), m(0x30, true, false)], vec![],
            vec![0, 1], signers, vec![(0, Borrow::Mut)], no_cpi());
        slice_case(c, signed, "callee_fails", vec![m(0x10, true, true)], vec![], vec![0], signers, vec![],
            cpi_terminates());
    }
    slice_case(c, true, "extra_trailing_account", vec![m(0x10, true, true), m(0x30, true, false)], vec![],
        vec![0, 1, 3], NONE, vec![], cpi_ok());
    slice_case(c, true, "address_mismatch_second", vec![m(0x10, true, true), m(0x50, false, false)], vec![],
        vec![0, 1], NONE, vec![], no_cpi());
    slice_case(c, true, "address_mismatch_before_borrow", vec![m(0x10, true, true)], vec![],
        vec![1], NONE, vec![(1, Borrow::Mut)], no_cpi());
    slice_case(c, true, "writable_shared_borrow", vec![m(0x10, true, true), m(0x30, true, false)], vec![],
        vec![0, 1], NONE, vec![(1, Borrow::Shared)], no_cpi());
    slice_case(c, true, "readonly_shared_borrow_ok", vec![m(0x10, false, false), m(0x30, true, false)], vec![],
        vec![0, 1], NONE, vec![(0, Borrow::Shared)], cpi_ok());
    slice_case(c, true, "duplicate_entries", vec![m(0x10, true, true), m(0x10, false, false)], vec![3],
        vec![0, 2], NONE, vec![], cpi_ok());
    slice_case(c, true, "data_accounts_callee_writes", vec![m(0x70, false, true), m(0x90, true, false)], vec![0xff; 5],
        vec![4, 5], NONE, vec![], cpi_writes(Some(vec![0xab, 0xcd])));
    slice_case(c, true, "empty_instruction", vec![], vec![], vec![], NONE, vec![], cpi_ok());
    let at = |n: usize| (0..n).map(|_| Meta { key: [0; 32], writable: false, signer: false }).collect::<Vec<_>>();
    slice_case(c, true, "max_128_metas_then_count_check", at(128), vec![], vec![0; 3], NONE, vec![], no_cpi());
    slice_case(c, true, "over_max_129_metas", at(129), vec![], vec![0; 3], NONE, vec![], no_cpi());
    slice_case(c, false, "over_max_129_metas", at(129), vec![], vec![], NONE, vec![(0, Borrow::Mut)], no_cpi());
}
