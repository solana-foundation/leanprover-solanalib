//! borsh 1.6.1 serializers, called with a recording writer.
//!
//! Each value is serialized once without failure and once for every writer
//! failure plan up to one call past its last write, so every error exit and
//! the writer state it leaves are recorded.

use borsh::BorshSerialize;
use crate::borsh_de::short;
use conformance_recorder::{self as rec, Corpus, Json, Record, RecordingWriter};

pub const WRITER: &str = "conformance_recorder::RecordingWriter";
pub const VEC_WRITER: &str = "alloc::vec::Vec<u8>";
/// Bytes already in a `Vec<u8>` writer before the call: serializers append.
pub const VEC_PREFIX: [u8; 2] = [0xee, 0xdd];

pub struct SerTy<T> {
    pub name: String,
    pub function: &'static str,
    pub generics: Vec<(&'static str, String)>,
    pub enc: fn(&T) -> Json,
}

fn prim<T>(name: &str, enc: fn(&T) -> Json) -> SerTy<T> {
    SerTy {
        name: name.to_string(),
        function: Box::leak(format!("<{name} as borsh::ser::BorshSerialize>::serialize").into_boxed_str()),
        generics: vec![],
        enc,
    }
}

/// Record `value.serialize(&mut writer)` for each failure plan. The number of
/// writer calls without failure bounds the plans.
pub fn ser_cases<T: BorshSerialize>(corpus: &mut Corpus, prefix: &str, ty: &SerTy<T>, values: &[(String, T)]) {
    ser_cases_with(corpus, prefix, ty, values, true)
}

/// As `ser_cases`; without `failures` only the non-failing plan is recorded.
pub fn ser_cases_with<T: BorshSerialize>(
    corpus: &mut Corpus,
    prefix: &str,
    ty: &SerTy<T>,
    values: &[(String, T)],
    failures: bool,
) {
    for (label, value) in values {
        let mut probe = RecordingWriter::new(None);
        let _ = rec::catch(|| value.serialize(&mut probe));
        let plans = if failures { rec::fail_plans(probe.calls) } else { vec![None] };
        for plan in plans {
            let (state, writer, outcome) = rec::writer_call(plan, |w| value.serialize(w));
            let plan_label = plan.map_or("ok".to_string(), |k| format!("fail{k}"));
            let mut generics = ty.generics.clone();
            generics.push(("W", WRITER.to_string()));
            corpus.push(Record {
                id: format!("{prefix}/serialize/{}/{label}/{plan_label}", short(&ty.name)),
                function: ty.function,
                generics,
                layout: None,
                state,
                args: Json::obj([("value", (ty.enc)(value)), ("writer", writer)]),
                outcome,
                observed: None,
            });
        }
        // W = Vec<u8>, the selected Vec writer instantiation; its state is the
        // vector contents.
        let mut vec: Vec<u8> = VEC_PREFIX.to_vec();
        let before = Json::obj([("vec", rec::bytes(&vec))]);
        let result = rec::catch(|| value.serialize(&mut vec));
        let after = Json::obj([("vec", rec::bytes(&vec))]);
        let outcome = match result {
            Ok(r) => rec::returned(rec::io_result(&r, |_| Json::Null), after),
            Err(reason) => rec::unwound(reason, after),
        };
        let mut generics = ty.generics.clone();
        generics.push(("W", VEC_WRITER.to_string()));
        corpus.push(Record {
            id: format!("{prefix}/serialize/{}/{label}/vec", short(&ty.name)),
            function: ty.function,
            generics,
            layout: None,
            state: before,
            args: Json::obj([("value", (ty.enc)(value))]),
            outcome,
            observed: None,
        });
    }
}

/// `<u8 as BorshSerialize>::u8_slice(slice)`: `Some(slice)`.
pub fn u8_slice_cases(corpus: &mut Corpus, prefix: &str) {
    for (label, slice) in [("empty", vec![]), ("one", vec![0x7f]), ("pattern16", (0..16u8).map(|i| i.wrapping_mul(37)).collect())] {
        let outcome = match rec::catch(|| <u8 as BorshSerialize>::u8_slice(&slice).map(|s| (s.to_vec(), s.as_ptr() == slice.as_ptr()))) {
            Ok(r) => rec::returned(rec::option(&r.as_ref().map(|(b, _)| b.clone()), |b| rec::bytes(b)), Json::Null),
            Err(reason) => rec::unwound(reason, Json::Null),
        };
        corpus.push(Record {
            id: format!("{prefix}/u8_slice/{label}"),
            function: "<u8 as borsh::ser::BorshSerialize>::u8_slice",
            generics: vec![],
            layout: None,
            state: Json::Null,
            args: Json::obj([("slice", rec::bytes(&slice))]),
            outcome,
            observed: None,
        });
    }
}

macro_rules! labelled {
    ($($v:expr),* $(,)?) => { vec![$((format!("{}", $v), $v)),*] };
}

pub fn record(corpus: &mut Corpus, prefix: &str) {
    u8_slice_cases(corpus, prefix);
    // u8: boundary values, each with fault injection at every call.
    let u8_ty = prim::<u8>("u8", |v| Json::from(*v));
    ser_cases(corpus, prefix, &u8_ty, &labelled![0u8, 1u8, 0x7fu8, 0x80u8, 0xffu8]);

    let bool_ty = prim::<bool>("bool", |v| Json::from(*v));
    ser_cases(corpus, prefix, &bool_ty, &labelled![false, true]);

    let u32_ty = prim::<u32>("u32", |v| Json::from(*v));
    ser_cases(corpus, prefix, &u32_ty, &labelled![0u32, 1u32, 0x0102_0304u32, 0x8000_0000u32, u32::MAX]);

    let u64_ty = prim::<u64>("u64", |v| Json::from(*v));
    ser_cases(corpus, prefix, &u64_ty, &labelled![0u64, 1u64, 0x0102_0304_0506_0708u64, 1u64 << 63, u64::MAX]);

    let i64_ty = prim::<i64>("i64", |v| Json::from(*v));
    ser_cases(corpus, prefix, &i64_ty, &labelled![0i64, 1i64, -1i64, i64::MAX, i64::MIN, -0x0102_0304_0506_0708i64]);

    let f64_ty = prim::<f64>("f64", |v| rec::f64_bits(*v));
    let floats: Vec<(String, f64)> =
        rec::F64_PATTERNS.iter().map(|(l, b)| (l.to_string(), f64::from_bits(*b))).collect();
    ser_cases(corpus, prefix, &f64_ty, &floats);

    // Option<T>
    macro_rules! opt {
        ($t:ty, $name:expr, $enc:expr, [$($v:expr),*]) => {{
            let ty = SerTy::<Option<$t>> {
                name: format!("core::option::Option<{}>", $name),
                function: "<core::option::Option<T> as borsh::ser::BorshSerialize>::serialize",
                generics: vec![("T", $name.to_string())],
                enc: |v| rec::option(v, $enc),
            };
            let mut values: Vec<(String, Option<$t>)> = vec![("none".to_string(), None)];
            $(values.push((format!("some_{}", stringify!($v)), Some($v)));)*
            ser_cases(corpus, prefix, &ty, &values);
        }};
    }
    opt!(u8, "u8", |x: &u8| Json::from(*x), [0u8, 0xffu8]);
    opt!(bool, "bool", |x: &bool| Json::from(*x), [false, true]);
    opt!(u32, "u32", |x: &u32| Json::from(*x), [0x0102_0304u32]);
    opt!(u64, "u64", |x: &u64| Json::from(*x), [u64::MAX]);
    opt!(i64, "i64", |x: &i64| Json::from(*x), [i64::MIN]);
    opt!(f64, "f64", |x: &f64| rec::f64_bits(*x), [1.5f64, f64::NAN, f64::INFINITY]);

    // [T; N]
    macro_rules! arr {
        ($t:ty, $n:expr, $name:expr, $enc:expr, [$($label:expr => $v:expr),*]) => {{
            let ty = SerTy::<[$t; $n]> {
                name: format!("[{}; {}]", $name, $n),
                function: "<[T; N] as borsh::ser::BorshSerialize>::serialize",
                generics: vec![("T", $name.to_string()), ("N", $n.to_string())],
                enc: $enc,
            };
            let values: Vec<(String, [$t; $n])> = vec![$(($label.to_string(), $v)),*];
            ser_cases(corpus, prefix, &ty, &values);
        }};
    }
    arr!(u8, 0, "u8", |v: &[u8; 0]| rec::bytes(v), ["empty" => []]);
    arr!(u8, 1, "u8", |v: &[u8; 1]| rec::bytes(v), ["x7f" => [0x7f]]);
    arr!(u8, 16, "u8", |v: &[u8; 16]| rec::bytes(v),
        ["pattern" => core::array::from_fn(|i| (i as u8).wrapping_mul(29).wrapping_add(1))]);
    arr!(u8, 32, "u8", |v: &[u8; 32]| rec::bytes(v),
        ["zero" => [0; 32], "ones" => [0xff; 32], "pattern" => core::array::from_fn(|i| (i as u8).wrapping_mul(37).wrapping_add(5))]);
    arr!(u64, 0, "u64", |v: &[u64; 0]| Json::arr(v.iter(), |x| Json::from(*x)), ["empty" => []]);
    arr!(u64, 3, "u64", |v: &[u64; 3]| Json::arr(v.iter(), |x| Json::from(*x)),
        ["mixed" => [0, 0x0102_0304_0506_0708, u64::MAX]]);
    arr!(bool, 2, "bool", |v: &[bool; 2]| Json::arr(v.iter(), |x| Json::from(*x)), ["tf" => [true, false]]);
    arr!(f64, 2, "f64", |v: &[f64; 2]| Json::arr(v.iter(), |x| rec::f64_bits(*x)),
        ["finite" => [0.5, -2.0], "nan_second" => [1.0, f64::NAN], "nan_first" => [f64::NAN, 1.0]]);
}
