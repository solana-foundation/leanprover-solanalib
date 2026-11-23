//! Encodings shared by the instruction records.

use conformance_recorder::{self as rec, Json};
use solana_address::Address;
use solana_instruction::{AccountMeta, Instruction};

/// A 32-byte address: `start`, 30 zero bytes and `start + 1` (distinct ends, compact zero run).
pub fn key(start: u8) -> Address {
    let mut b = [0u8; 32];
    b[0] = start;
    b[31] = start.wrapping_add(1);
    Address::new_from_array(b)
}

/// The test addresses: all-zero (the System program id), two patterns and all-0xff.
pub fn keys() -> Vec<(&'static str, Address)> {
    vec![
        ("zero", Address::new_from_array([0; 32])),
        ("k10", key(0x10)),
        ("k80", key(0x80)),
        ("ff", Address::new_from_array([0xff; 32])),
    ]
}

pub fn address(a: &Address) -> Json {
    rec::bytes(a.as_ref())
}

/// `{"pubkey", "is_signer", "is_writable"}`, the fields of `AccountMeta`.
pub fn meta(m: &AccountMeta) -> Json {
    Json::obj([
        ("pubkey", address(&m.pubkey)),
        ("is_signer", m.is_signer.into()),
        ("is_writable", m.is_writable.into()),
    ])
}

/// `{"program_id", "accounts", "data"}`, the fields of `Instruction`.
pub fn instruction(i: &Instruction) -> Json {
    Json::obj([
        ("program_id", address(&i.program_id)),
        ("accounts", Json::arr(i.accounts.iter(), meta)),
        ("data", rec::bytes(&i.data)),
    ])
}

/// A call whose state is `()` (recorded as `null`): the result or the panic.
pub fn pure_call<T>(f: impl FnOnce() -> T, enc: impl Fn(&T) -> Json) -> Json {
    match rec::catch(f) {
        Ok(v) => rec::returned(enc(&v), Json::Null),
        Err(reason) => rec::unwound(reason, Json::Null),
    }
}
