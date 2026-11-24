//! solana-borsh 3.0.2 `v1::try_from_slice_unchecked::<T>` over borsh 1.6.1.
//!
//! `T` ranges over the borsh implementations for `u8`, `u32`, `Option<u8>` and `[u8; 32]` (the Lean side composes
//! the registered borsh 1.6.1 `deserialize` member at that `T`) and over a scripted type whose
//! `deserialize` logs the slice it receives, consumes a chosen prefix and then returns a chosen
//! value or error, or panics.

use borsh::BorshDeserialize;
use conformance_recorder::{self as rec, Corpus, Json, Record};
use std::cell::RefCell;
use std::io;

const FUNCTION: &str = "solana_borsh::v1::try_from_slice_unchecked";
pub const SCRIPTED: &str = "conformance_instructions_3_4_0_bincode::borsh_unchecked::Scripted";

fn real<T: BorshDeserialize>(c: &mut Corpus, t: &str, label: &str, inputs: &[(&str, Vec<u8>)], enc: impl Fn(&T) -> Json) {
    for (il, data) in inputs {
        c.push(Record {
            id: format!("{label}/{il}"),
            function: FUNCTION,
            generics: vec![("T", t.to_string())],
            layout: None,
            state: Json::Null,
            args: Json::obj([("data", rec::bytes(data))]),
            outcome: rec::value_call(|| solana_borsh::v1::try_from_slice_unchecked::<T>(data), &enc),
            observed: None,
        });
    }
}

#[derive(Clone)]
enum Result_ {
    Ok(u64),
    Err(io::ErrorKind, &'static str),
    Panic(&'static str),
}

#[derive(Clone)]
struct Script {
    consume: usize,
    result: Result_,
}

impl Script {
    fn json(&self) -> Json {
        let result = match &self.result {
            Result_::Ok(v) => Json::obj([("ok", (*v).into())]),
            Result_::Err(kind, message) => Json::obj([("err", rec::io_error(&io::Error::new(*kind, *message)))]),
            Result_::Panic(message) => Json::obj([("panic", (*message).into())]),
        };
        Json::obj([("consume", self.consume.into()), ("result", result)])
    }
}

thread_local! {
    static SCRIPT: RefCell<Option<Script>> = const { RefCell::new(None) };
    static LOG: RefCell<Vec<Vec<u8>>> = const { RefCell::new(Vec::new()) };
}

/// The scripted `T`. Only `deserialize` (the entry `try_from_slice_unchecked` calls) is used.
pub struct Scripted(pub u64);

impl BorshDeserialize for Scripted {
    fn deserialize_reader<R: io::Read>(_reader: &mut R) -> io::Result<Self> {
        unreachable!("try_from_slice_unchecked calls `deserialize`")
    }

    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        LOG.with(|log| log.borrow_mut().push(buf.to_vec()));
        let script = SCRIPT.with(|s| s.borrow().clone()).expect("script");
        let k = script.consume.min(buf.len());
        *buf = &buf[k..];
        match script.result {
            Result_::Ok(v) => Ok(Scripted(v)),
            Result_::Err(kind, message) => Err(io::Error::new(kind, message)),
            Result_::Panic(message) => panic!("{message}"),
        }
    }
}

fn log_state() -> Json {
    Json::obj([("log", LOG.with(|log| Json::arr(log.borrow().iter(), |b| rec::bytes(b))))])
}

fn scripted(c: &mut Corpus) {
    let data = vec![1u8, 2, 3, 4];
    let cases: Vec<(&str, Vec<u8>, Script)> = vec![
        ("ok_exact", data.clone(), Script { consume: 4, result: Result_::Ok(7) }),
        ("ok_trailing", data.clone(), Script { consume: 1, result: Result_::Ok(u64::MAX) }),
        ("ok_nothing_read", data.clone(), Script { consume: 0, result: Result_::Ok(0) }),
        ("ok_empty_input", vec![], Script { consume: 0, result: Result_::Ok(5) }),
        ("err_after_read", data.clone(), Script {
            consume: 2,
            result: Result_::Err(io::ErrorKind::InvalidData, "scripted invalid data"),
        }),
        ("err_empty_input", vec![], Script {
            consume: 0,
            result: Result_::Err(io::ErrorKind::UnexpectedEof, "scripted eof"),
        }),
        ("panic", data.clone(), Script { consume: 3, result: Result_::Panic("scripted deserialize panic") }),
    ];
    for (prior, prior_log) in [("fresh", vec![]), ("prior_call", vec![vec![0xaau8]])] {
        for (label, input, script) in &cases {
            LOG.with(|log| *log.borrow_mut() = prior_log.clone());
            SCRIPT.with(|s| *s.borrow_mut() = Some(script.clone()));
            let before = log_state();
            let result = rec::catch(|| solana_borsh::v1::try_from_slice_unchecked::<Scripted>(input));
            let after = log_state();
            let outcome = match result {
                Ok(r) => rec::returned(rec::io_result(&r, |v| Json::from(v.0)), after),
                Err(reason) => rec::unwound(reason, after),
            };
            c.push(Record {
                id: format!("scripted/{label}/{prior}"),
                function: FUNCTION,
                generics: vec![("T", SCRIPTED.to_string())],
                layout: None,
                state: before,
                args: Json::obj([("data", rec::bytes(input)), ("script", script.json())]),
                outcome,
                observed: None,
            });
        }
    }
}

pub fn record(c: &mut Corpus) {
    let t = rec::TRAILING.to_vec();
    real::<u8>(c, "u8", "u8", &[("empty", vec![]), ("exact", vec![7]), ("trailing", [vec![7], t.clone()].concat())],
        |v| Json::from(*v));
    real::<u32>(c, "u32", "u32", &[
        ("empty", vec![]),
        ("short", vec![1, 2, 3]),
        ("exact", vec![1, 2, 3, 4]),
        ("trailing", [vec![1, 2, 3, 4], t.clone()].concat()),
    ], |v| Json::from(*v));
    real::<Option<u8>>(c, "core::option::Option<u8>", "option_u8", &[
        ("empty", vec![]),
        ("none", vec![0]),
        ("none+trailing", [vec![0], t.clone()].concat()),
        ("some_short", vec![1]),
        ("some", vec![1, 9]),
        ("tag2", vec![2, 9]),
    ], |v| rec::option(v, |x| Json::from(*x)));
    let pattern: Vec<u8> = (0..33u8).collect();
    real::<[u8; 32]>(c, "[u8; 32]", "array_u8_32", &[
        ("empty", vec![]),
        ("short", pattern[..31].to_vec()),
        ("exact", pattern[..32].to_vec()),
        ("trailing", pattern.clone()),
    ], |v| rec::bytes(v));
    scripted(c);
}
