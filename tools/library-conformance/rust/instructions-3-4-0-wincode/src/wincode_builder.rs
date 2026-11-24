//! solana-instruction 3.4.0 `Instruction::new_with_wincode::<T>` at `T = u64`, `T = Vec<u8>` and
//! a scripted `SchemaWrite` that emits chosen bytes, returns `WriteError::Custom` or panics (in
//! `size_of`, which `wincode::serialize` calls first, and in `write`).

use crate::common::{instruction, key, meta, pure_call};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use solana_address::Address;
use solana_instruction::{AccountMeta, Instruction};
use wincode::config::ConfigCore;
use wincode::io::Writer;
use wincode::{SchemaWrite, WriteError, WriteResult};

const FUNCTION: &str = "solana_instruction::Instruction::new_with_wincode";
pub const SCRIPTED: &str = "conformance_instructions_3_4_0_wincode::wincode_builder::ScriptedSerialize";

pub enum ScriptedSerialize {
    Emit(Vec<u8>),
    Fail(&'static str),
    Panic(&'static str),
}

unsafe impl<C: ConfigCore> SchemaWrite<C> for ScriptedSerialize {
    type Src = ScriptedSerialize;

    fn size_of(src: &Self) -> WriteResult<usize> {
        match src {
            ScriptedSerialize::Emit(b) => Ok(b.len()),
            ScriptedSerialize::Fail(m) => Err(WriteError::Custom(m)),
            ScriptedSerialize::Panic(m) => panic!("{m}"),
        }
    }

    fn write(mut writer: impl Writer, src: &Self) -> WriteResult<()> {
        match src {
            ScriptedSerialize::Emit(b) => Ok(writer.write(b)?),
            ScriptedSerialize::Fail(m) => Err(WriteError::Custom(m)),
            ScriptedSerialize::Panic(m) => panic!("{m}"),
        }
    }
}

impl ScriptedSerialize {
    fn json(&self) -> Json {
        match self {
            ScriptedSerialize::Emit(b) => Json::obj([("emit", rec::bytes(b))]),
            ScriptedSerialize::Fail(m) => Json::obj([("fail", (*m).into())]),
            ScriptedSerialize::Panic(m) => Json::obj([("panic", (*m).into())]),
        }
    }
}

fn account_lists() -> Vec<(&'static str, Vec<AccountMeta>)> {
    vec![
        ("no_accounts", vec![]),
        ("one", vec![AccountMeta::new(key(0x10), true)]),
        ("dup", vec![
            AccountMeta::new(key(0x10), true),
            AccountMeta::new_readonly(key(0x80), false),
            AccountMeta::new(key(0x10), true),
        ]),
    ]
}

fn push(c: &mut Corpus, id: String, t: &str, program_id: Address, data: Json, accounts: &[AccountMeta],
        call: impl FnOnce() -> Instruction) {
    c.push(Record {
        id,
        function: FUNCTION,
        generics: vec![("T", t.to_string())],
        layout: None,
        state: Json::Null,
        args: Json::obj([
            ("program_id", rec::bytes(program_id.as_ref())),
            ("data", data),
            ("accounts", Json::arr(accounts.iter(), meta)),
        ]),
        outcome: pure_call(call, instruction),
        observed: None,
    });
}

pub fn record(c: &mut Corpus) {
    for (al, accounts) in account_lists() {
        for (vl, v) in [("0", 0u64), ("pattern", 0x0102_0304_0506_0708), ("max", u64::MAX)] {
            let a = accounts.clone();
            push(c, format!("wincode/u64/{vl}/{al}"), "u64", key(0x80), v.into(), &accounts,
                move || Instruction::new_with_wincode(key(0x80), &v, a));
        }
        for (vl, v) in [("empty", vec![]), ("three", vec![1u8, 2, 3])] {
            let a = accounts.clone();
            let data = rec::bytes(&v);
            push(c, format!("wincode/vec_u8/{vl}/{al}"), "alloc::vec::Vec<u8>", key(0x80), data, &accounts,
                move || Instruction::new_with_wincode(key(0x80), &v, a));
        }
        for (vl, v) in [
            ("emit_empty", ScriptedSerialize::Emit(vec![])),
            ("emit_two", ScriptedSerialize::Emit(vec![0xde, 0xad])),
            ("fail", ScriptedSerialize::Fail("scripted serialize failure")),
            ("panic", ScriptedSerialize::Panic("scripted serialize panic")),
        ] {
            let a = accounts.clone();
            let data = v.json();
            push(c, format!("wincode/scripted/{vl}/{al}"), SCRIPTED, key(0x10), data, &accounts,
                move || Instruction::new_with_wincode(key(0x10), &v, a));
        }
    }
}
