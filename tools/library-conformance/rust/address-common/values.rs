//! solana-address 2.6.x value operations: `new_from_array`, `as_array`,
//! `as_ref`, `to_bytes`, `Default::default` and `PartialEq::eq`. Shared by the
//! 2.6.0 and 2.6.1 drivers (`#[path]`-included); the including crate selects
//! the version.
//!
//! Values are built and observed through the `#[repr(transparent)]` representation of `Address`
//! layout over `[u8; 32]`, not through the functions under test. Every call
//! state is `()` (recorded as `null`): the models are value observations.
//! Whether a returned reference points into `self` is a native-only
//! observation (`observed.borrows_self`), never compared.

use conformance_recorder::{self as rec, Corpus, Json, Record};
use solana_address::Address;

pub const NEW_FROM_ARRAY: &str = "solana_address::Address::new_from_array";
pub const AS_ARRAY: &str = "solana_address::Address::as_array";
pub const AS_REF: &str = "<solana_address::Address as core::convert::AsRef<[u8]>>::as_ref";
pub const TO_BYTES: &str = "solana_address::Address::to_bytes";
pub const DEFAULT: &str = "<solana_address::Address as core::default::Default>::default";
pub const EQ: &str = "<solana_address::Address as core::cmp::PartialEq>::eq";

/// `Address` is `#[repr(transparent)]` over `[u8; 32]`.
pub fn address(bytes: [u8; 32]) -> Address {
    // SAFETY: same size and layout; every byte array is a valid `Address`.
    unsafe { core::mem::transmute::<[u8; 32], Address>(bytes) }
}

pub fn bytes_of(a: &Address) -> [u8; 32] {
    // SAFETY: `#[repr(transparent)]` over `[u8; 32]`.
    unsafe { *(a as *const Address as *const [u8; 32]) }
}

pub fn enc(a: &Address) -> Json {
    rec::bytes(&bytes_of(a))
}

/// The sample values: zero (the system program id), all ones, a pattern, and
/// a single set bit at each end.
pub fn samples() -> Vec<(&'static str, [u8; 32])> {
    let mut pattern = [0u8; 32];
    for (i, b) in pattern.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(37).wrapping_add(11);
    }
    let mut first = [0u8; 32];
    first[0] = 1;
    let mut last = [0u8; 32];
    last[31] = 0x80;
    vec![
        ("zero", [0; 32]),
        ("ones", [0xff; 32]),
        ("pattern", pattern),
        ("first_bit", first),
        ("last_bit", last),
    ]
}

fn unit_call<T>(f: impl FnOnce() -> T, enc: impl Fn(&T) -> Json) -> Json {
    match rec::catch(f) {
        Ok(v) => rec::returned(enc(&v), Json::Null),
        Err(reason) => rec::unwound(reason, Json::Null),
    }
}

fn push(c: &mut Corpus, id: String, function: &'static str, args: Json, outcome: Json, observed: Option<Json>) {
    c.push(Record { id, function, generics: vec![], layout: None, state: Json::Null, args, outcome, observed });
}

pub fn record(c: &mut Corpus) {
    let samples = samples();
    for (name, bytes) in &samples {
        let outcome = unit_call(|| Address::new_from_array(*bytes), enc);
        push(c, format!("new_from_array/{name}"), NEW_FROM_ARRAY, Json::obj([("array", rec::bytes(bytes))]), outcome, None);
    }
    for (name, bytes) in &samples {
        let a = address(*bytes);
        let base = &a as *const Address as usize;
        let mut borrows = None;
        let outcome = unit_call(
            || {
                let r = a.as_array();
                borrows = Some(r.as_ptr() as usize == base);
                *r
            },
            |r| rec::bytes(r),
        );
        let observed = borrows.map(|b| Json::obj([("borrows_self", b.into())]));
        push(c, format!("as_array/{name}"), AS_ARRAY, Json::obj([("self", enc(&a))]), outcome, observed);
    }
    for (name, bytes) in &samples {
        let a = address(*bytes);
        let base = &a as *const Address as usize;
        let mut borrows = None;
        let outcome = unit_call(
            || {
                let r: &[u8] = a.as_ref();
                borrows = Some(r.as_ptr() as usize == base);
                r.to_vec()
            },
            |r| rec::bytes(r),
        );
        let observed = borrows.map(|b| Json::obj([("borrows_self", b.into())]));
        push(c, format!("as_ref/{name}"), AS_REF, Json::obj([("self", enc(&a))]), outcome, observed);
    }
    for (name, bytes) in &samples {
        let a = address(*bytes);
        let outcome = unit_call(|| a.to_bytes(), |r| rec::bytes(r));
        push(c, format!("to_bytes/{name}"), TO_BYTES, Json::obj([("self", enc(&a))]), outcome, None);
    }
    let outcome = unit_call(<Address as Default>::default, enc);
    push(c, "default".to_string(), DEFAULT, Json::Null, outcome, None);

    // Equality: each sample with an equal value in separate storage, distinct
    // samples, and the pattern changed in one byte at several positions.
    let mut pairs: Vec<(String, [u8; 32], [u8; 32])> = Vec::new();
    for (name, bytes) in &samples {
        pairs.push((format!("{name}=={name}"), *bytes, *bytes));
    }
    pairs.push(("zero!=ones".into(), samples[0].1, samples[1].1));
    pairs.push(("first_bit!=last_bit".into(), samples[3].1, samples[4].1));
    pairs.push(("zero!=last_bit".into(), samples[0].1, samples[4].1));
    let pattern = samples[2].1;
    for i in [0usize, 1, 7, 8, 15, 16, 24, 31] {
        let mut other = pattern;
        other[i] ^= 0x01;
        pairs.push((format!("pattern!=pattern^byte{i}"), pattern, other));
    }
    for (name, left, right) in pairs {
        let (l, r) = (address(left), address(right));
        let outcome = unit_call(|| l == r, |b| Json::from(*b));
        push(c, format!("eq/{name}"), EQ, Json::obj([("self", enc(&l)), ("other", enc(&r))]), outcome, None);
    }
}
