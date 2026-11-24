//! solana-instruction-view 2.1.0 value conversions: `Seed::from(&[u8])`, `Seed::from(&[u8; N])`,
//! `Signer::from(&[Seed; N])` and `InstructionAccount::readonly_signer`.
//!
//! A `Seed`/`Signer` is the C-ABI pointer and length of the borrowed data; the record holds the
//! bytes it denotes, read through that representation. The drivers assert natively that the
//! pointers belong to the argument (nothing is copied).

use conformance_recorder::{self as rec, Corpus, Json, Record};
use solana_address::Address;
use solana_instruction_view::cpi::{Seed, Signer};
use solana_instruction_view::InstructionAccount;

const SEED_SLICE: &str = "<solana_instruction_view::cpi::Seed<'bytes> as core::convert::From<&'bytes [u8]>>::from";
const SEED_ARRAY: &str = "<solana_instruction_view::cpi::Seed<'bytes> as core::convert::From<&'bytes [u8; SIZE]>>::from";
const SIGNER_ARRAY: &str = "<solana_instruction_view::cpi::Signer<'bytes, 'seeds> as core::convert::From<&'seeds [solana_instruction_view::cpi::Seed<'bytes>; SIZE]>>::from";
const READONLY_SIGNER: &str = "solana_instruction_view::InstructionAccount::<'a>::readonly_signer";

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

fn seed_bytes(seed: &Seed) -> Vec<u8> {
    assert_eq!(std::mem::size_of::<Seed>(), std::mem::size_of::<RawSeed>());
    let raw = unsafe { &*(seed as *const Seed as *const RawSeed) };
    assert_eq!(raw.len as usize, seed.len());
    seed.to_vec()
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

fn push(c: &mut Corpus, id: String, function: &'static str, generics: Vec<(&'static str, String)>, args: Json, result: Json) {
    c.push(Record { id, function, generics, layout: None, state: Json::Null, args,
        outcome: rec::returned(result, Json::Null), observed: None });
}

fn seed_array<const N: usize>(c: &mut Corpus, label: &str, bytes: [u8; N]) {
    let seed = Seed::from(&bytes);
    assert_eq!(seed.as_ptr(), bytes.as_ptr());
    push(c, format!("seed_from_array/{label}"), SEED_ARRAY, vec![("SIZE", N.to_string())],
        Json::obj([("bytes", rec::bytes(&bytes))]), rec::bytes(&seed_bytes(&seed)));
}

fn signer_array<const N: usize>(c: &mut Corpus, label: &str, seeds: [&[u8]; N]) {
    let array: [Seed; N] = seeds.map(Seed::from);
    let signer = Signer::from(&array);
    let raw = unsafe { &*(&signer as *const Signer as *const RawSigner) };
    assert_eq!(raw.ptr as usize, array.as_ptr() as usize);
    push(c, format!("signer_from_array/{label}"), SIGNER_ARRAY, vec![("SIZE", N.to_string())],
        Json::obj([("seeds", Json::arr(seeds.iter(), |s| rec::bytes(s)))]),
        Json::arr(signer_seeds(&signer).iter(), |s| rec::bytes(s)));
}

pub fn record(c: &mut Corpus) {
    let long: Vec<u8> = (0..40u8).collect();
    for (label, bytes) in [("empty", &[][..]), ("one", &[7u8][..]), ("seed32", &long[..32]), ("over_pda_limit40", &long[..])] {
        let seed = Seed::from(bytes);
        assert_eq!(seed.as_ptr(), bytes.as_ptr());
        push(c, format!("seed_from_slice/{label}"), SEED_SLICE, vec![], Json::obj([("bytes", rec::bytes(bytes))]),
            rec::bytes(&seed_bytes(&seed)));
    }
    seed_array(c, "empty", []);
    seed_array(c, "one", [0xff]);
    let mut a32 = [0u8; 32];
    a32.copy_from_slice(&long[..32]);
    seed_array(c, "seed32", a32);
    let mut a33 = [0u8; 33];
    a33.copy_from_slice(&long[..33]);
    seed_array(c, "seed33", a33);
    signer_array::<0>(c, "empty", []);
    signer_array(c, "one_empty_seed", [&[]]);
    signer_array(c, "three_with_duplicate", [b"vault".as_slice(), &[0xfe], b"vault".as_slice()]);
    for (label, start) in [("zero", 0u8), ("k10", 0x10), ("ff", 0xff)] {
        let address = Address::new_from_array(core::array::from_fn(|i| if start == 0xff { 0xff } else { start.wrapping_add(i as u8) }));
        let account = InstructionAccount::readonly_signer(&address);
        assert!(core::ptr::eq(account.address, &address));
        push(c, format!("readonly_signer/{label}"), READONLY_SIGNER, vec![],
            Json::obj([("address", rec::bytes(address.as_ref()))]),
            Json::obj([
                ("pubkey", rec::bytes(account.address.as_ref())),
                ("is_signer", account.is_signer.into()),
                ("is_writable", account.is_writable.into()),
            ]));
    }
}
