//! Total value functions: solana-hash 4.5.0 `Hash::to_bytes`, solana-sdk-ids 3.1.0
//! `system_program::id`, solana-zero-copy 1.2.0 `From<U64> for u64` and solana-program-option
//! 3.1.0 `COption::<T>::is_some` at four payload types. The state is `()` (`null`).

use conformance_recorder::{self as rec, Corpus, Json, Record};
use solana_program_option::COption;

fn push(c: &mut Corpus, id: String, function: &'static str, generics: Vec<(&'static str, String)>, args: Json, outcome: Json) {
    c.push(Record { id, function, generics, layout: None, state: Json::Null, args, outcome, observed: None });
}

fn value<T>(f: impl FnOnce() -> T, enc: impl Fn(&T) -> Json) -> Json {
    match rec::catch(f) {
        Ok(v) => rec::returned(enc(&v), Json::Null),
        Err(reason) => rec::unwound(reason, Json::Null),
    }
}

fn pattern(n: usize, seed: u8) -> Vec<u8> {
    (0..n).map(|i| (i as u8).wrapping_mul(37).wrapping_add(seed)).collect()
}

fn array32(bytes: &[u8]) -> [u8; 32] {
    bytes.try_into().expect("32 bytes")
}

pub fn hash_corpus() -> Corpus {
    let mut c = Corpus::new("solana_hash_4_5_0", &[("solana-hash", "4.5.0")]);
    let cases: Vec<(&str, [u8; 32])> = vec![
        ("zero", [0; 32]),
        ("ones", [0xff; 32]),
        ("pattern", array32(&pattern(32, 1))),
        ("pattern2", array32(&pattern(32, 200))),
        ("first", { let mut a = [0; 32]; a[0] = 1; a }),
        ("last", { let mut a = [0; 32]; a[31] = 0x80; a }),
    ];
    for (name, bytes) in cases {
        let hash = solana_hash::Hash::new_from_array(bytes);
        push(
            &mut c,
            format!("to_bytes/{name}"),
            "solana_hash::Hash::to_bytes",
            vec![],
            Json::obj([("hash", rec::bytes(&bytes))]),
            value(|| hash.to_bytes(), |a| rec::bytes(a)),
        );
    }
    c
}

pub fn sdk_ids_corpus() -> Corpus {
    let mut c = Corpus::new("solana_sdk_ids_3_1_0", &[("solana-sdk-ids", "3.1.0")]);
    push(
        &mut c,
        "system_program/id".into(),
        "solana_sdk_ids::system_program::id",
        vec![],
        Json::Null,
        value(solana_sdk_ids::system_program::id, |a| rec::bytes(a.as_ref())),
    );
    c
}

pub fn zero_copy_corpus() -> Corpus {
    use solana_zero_copy::unaligned::U64;
    let mut c = Corpus::new("solana_zero_copy_1_2_0", &[("solana-zero-copy", "1.2.0")]);
    let mut cases: Vec<(String, [u8; 8])> = vec![
        ("zero".into(), [0; 8]),
        ("one".into(), 1u64.to_le_bytes()),
        ("byte_boundary".into(), 256u64.to_le_bytes()),
        ("i64_max".into(), (i64::MAX as u64).to_le_bytes()),
        ("sign_bit".into(), (1u64 << 63).to_le_bytes()),
        ("max".into(), [0xff; 8]),
        ("pattern".into(), pattern(8, 3).try_into().unwrap()),
    ];
    for i in 0..8 {
        let mut b = [0u8; 8];
        b[i] = 0x80 | i as u8;
        cases.push((format!("byte{i}"), b));
    }
    for (name, bytes) in cases {
        let v = U64(bytes);
        push(
            &mut c,
            format!("into_u64/{name}"),
            "solana_zero_copy::unaligned::<impl core::convert::From<solana_zero_copy::unaligned::U64> for u64>::from",
            vec![],
            Json::obj([("value", rec::bytes(&bytes))]),
            value(|| u64::from(v), |n| Json::from(*n)),
        );
    }
    c
}

fn is_some_case<T: Copy>(
    c: &mut Corpus,
    ty: &'static str,
    name: &str,
    option: COption<T>,
    payload: impl Fn(&T) -> Json,
) {
    let args = Json::obj([(
        "option",
        match &option {
            COption::None => Json::Null,
            COption::Some(v) => Json::obj([("some", payload(v))]),
        },
    )]);
    push(
        c,
        format!("is_some/{ty}/{name}"),
        "solana_program_option::COption::<T>::is_some",
        vec![("T", ty.to_string())],
        args,
        value(|| option.is_some(), |b| Json::from(*b)),
    );
}

pub fn program_option_corpus() -> Corpus {
    let mut c = Corpus::new("solana_program_option_3_1_0", &[("solana-program-option", "3.1.0")]);
    let n = |v: &u64| Json::from(*v);
    is_some_case(&mut c, "u64", "none", COption::<u64>::None, n);
    is_some_case(&mut c, "u64", "zero", COption::Some(0u64), n);
    is_some_case(&mut c, "u64", "max", COption::Some(u64::MAX), n);
    let b = |v: &u8| Json::from(*v);
    is_some_case(&mut c, "u8", "none", COption::<u8>::None, b);
    is_some_case(&mut c, "u8", "zero", COption::Some(0u8), b);
    is_some_case(&mut c, "u8", "one", COption::Some(1u8), b);
    let u = |_: &()| Json::Null;
    is_some_case(&mut c, "()", "none", COption::<()>::None, u);
    is_some_case(&mut c, "()", "unit", COption::Some(()), u);
    let a = |v: &[u8; 32]| rec::bytes(v);
    is_some_case(&mut c, "[u8; 32]", "none", COption::<[u8; 32]>::None, a);
    is_some_case(&mut c, "[u8; 32]", "zero", COption::Some([0u8; 32]), a);
    is_some_case(&mut c, "[u8; 32]", "pattern", COption::Some(array32(&pattern(32, 5))), a);
    c
}
