//! solana-instruction 3.4.0: the `AccountMeta` constructors and `Instruction::new_with_bincode`.
//!
//! `new_with_bincode::<T>` is recorded at `T = u64`, `T = Vec<u8>` and at a scripted `Serialize`
//! implementation that emits chosen bytes, returns a `serde` error or panics. The model takes the
//! serializer as a provider; the Lean side interprets it by the same script and bincode
//! encodings of `u64` and `Vec<u8>`.

use crate::common::{instruction, key, keys, meta, pure_call};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use serde::ser::{Error as _, SerializeTuple};
use solana_address::Address;
use solana_instruction::{AccountMeta, Instruction};

const NEW: &str = "solana_instruction::account_meta::AccountMeta::new";
const NEW_READONLY: &str = "solana_instruction::account_meta::AccountMeta::new_readonly";
const NEW_WITH_BINCODE: &str = "solana_instruction::Instruction::new_with_bincode";

pub fn record_meta(c: &mut Corpus) {
    for (label, k) in keys() {
        for signer in [false, true] {
            let args = Json::obj([("pubkey", rec::bytes(k.as_ref())), ("is_signer", signer.into())]);
            for (function, name, f) in [
                (NEW, "new", AccountMeta::new as fn(Address, bool) -> AccountMeta),
                (NEW_READONLY, "new_readonly", AccountMeta::new_readonly),
            ] {
                c.push(Record {
                    id: format!("{name}/{label}/signer_{signer}"),
                    function,
                    generics: vec![],
                    layout: None,
                    state: Json::Null,
                    args: args.clone(),
                    outcome: pure_call(|| f(k, signer), meta),
                    observed: None,
                });
            }
        }
    }
}

/// A `Serialize` implementation following a per-case script.
pub enum ScriptedSerialize {
    /// Serialize as a tuple of these bytes (bincode writes them unprefixed).
    Emit(Vec<u8>),
    /// Return `S::Error::custom(message)`.
    Fail(&'static str),
    /// Panic with this message.
    Panic(&'static str),
}

impl serde::Serialize for ScriptedSerialize {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            ScriptedSerialize::Emit(bytes) => {
                let mut tuple = serializer.serialize_tuple(bytes.len())?;
                for b in bytes {
                    tuple.serialize_element(b)?;
                }
                tuple.end()
            }
            ScriptedSerialize::Fail(message) => Err(S::Error::custom(message)),
            ScriptedSerialize::Panic(message) => panic!("{message}"),
        }
    }
}

impl ScriptedSerialize {
    pub fn json(&self) -> Json {
        match self {
            ScriptedSerialize::Emit(b) => Json::obj([("emit", rec::bytes(b))]),
            ScriptedSerialize::Fail(m) => Json::obj([("fail", (*m).into())]),
            ScriptedSerialize::Panic(m) => Json::obj([("panic", (*m).into())]),
        }
    }
}

pub const SCRIPTED: &str = "conformance_instructions_3_4_0_bincode::builder::ScriptedSerialize";

/// Account lists: empty, one writable signer, and a list with a repeated entry.
pub fn account_lists() -> Vec<(&'static str, Vec<AccountMeta>)> {
    vec![
        ("no_accounts", vec![]),
        ("one", vec![AccountMeta::new(key(0x10), true)]),
        (
            "dup",
            vec![
                AccountMeta::new(key(0x10), true),
                AccountMeta::new_readonly(key(0x80), false),
                AccountMeta::new(key(0x10), true),
            ],
        ),
    ]
}

fn builder_record(
    c: &mut Corpus,
    id: String,
    t: &str,
    program_id: Address,
    data: Json,
    accounts: &[AccountMeta],
    call: impl FnOnce() -> Instruction,
) {
    let args = Json::obj([
        ("program_id", rec::bytes(program_id.as_ref())),
        ("data", data),
        ("accounts", Json::arr(accounts.iter(), meta)),
    ]);
    c.push(Record {
        id,
        function: NEW_WITH_BINCODE,
        generics: vec![("T", t.to_string())],
        layout: None,
        state: Json::Null,
        args,
        outcome: pure_call(call, instruction),
        observed: None,
    });
}

pub fn record_bincode(c: &mut Corpus) {
    let programs = [("p_zero", Address::new_from_array([0; 32])), ("p80", key(0x80))];
    for (al, accounts) in account_lists() {
        for (pl, program_id) in programs {
            for (vl, v) in [("0", 0u64), ("pattern", 0x0102_0304_0506_0708), ("max", u64::MAX)] {
                let a = accounts.clone();
                builder_record(c, format!("bincode/u64/{vl}/{al}/{pl}"), "u64", program_id, v.into(),
                    &accounts, move || Instruction::new_with_bincode(program_id, &v, a));
            }
        }
    }
    let (al, accounts) = &account_lists()[2];
    for (vl, v) in [("empty", vec![]), ("one", vec![7u8]), ("three", vec![1, 2, 3])] {
        let a = accounts.clone();
        builder_record(c, format!("bincode/vec_u8/{vl}/{al}"), "alloc::vec::Vec<u8>", key(0x80),
            rec::bytes(&v), accounts, move || Instruction::new_with_bincode(key(0x80), &v, a));
    }
    for (al, accounts) in account_lists() {
        for (vl, v) in [
            ("emit_empty", ScriptedSerialize::Emit(vec![])),
            ("emit_two", ScriptedSerialize::Emit(vec![0xde, 0xad])),
            ("fail", ScriptedSerialize::Fail("scripted serialize failure")),
            ("panic", ScriptedSerialize::Panic("scripted serialize panic")),
        ] {
            let a = accounts.clone();
            let data = v.json();
            builder_record(c, format!("bincode/scripted/{vl}/{al}"), SCRIPTED, key(0x10), data, &accounts,
                move || Instruction::new_with_bincode(key(0x10), &v, a));
        }
    }
}
