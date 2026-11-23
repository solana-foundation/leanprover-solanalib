//! solana-define-syscall 5.1.0, called directly: the raw `sol_sha256`, `sol_log_`, `sol_panic_`
//! and `abort` declarations of `definitions`, which pinocchio 0.11.1 links. Each case calls the
//! `extern "C"` function, which the shim defines, with the arguments as the record states them.
//!
//! `sol_sha256` hashes into a 32-byte result buffer that starts with a known pattern; the record
//! keeps the status and the buffer after the call. Replies stay inside the modeled hash shape:
//! status 0 with exactly 32 bytes, or an error status with no bytes (the shim copies the reply
//! bytes whatever its status, the runtime only on status 0). `sol_panic_` and `abort` end every
//! case in the shim (reasons `sol_panic_` and `abort`).

use crate::syscall_cases::*;
use conformance_recorder::{self as rec, Corpus, Json};
use conformance_shim::{Reply, Script};
use solana_define_syscall::definitions as raw;

const SHA256: &str = "solana_define_syscall::definitions::sol_sha256";
const LOG: &str = "solana_define_syscall::definitions::sol_log_";
const PANIC: &str = "solana_define_syscall::definitions::sol_panic_";
const ABORT: &str = "solana_define_syscall::definitions::abort";

fn sha256(c: &mut Corpus, id: String, slices: &[Vec<u8>], script: Script) {
    let initial: [u8; 32] = pattern(32, 0xa5).try_into().unwrap();
    let args = Json::obj([("slices", hex_fields(slices)), ("hash_result", rec::bytes(&initial))]);
    let refs: Vec<&[u8]> = slices.iter().map(|s| s.as_slice()).collect();
    syscall_case(c, id, SHA256, args, script, || {
        let mut out = initial;
        // `vals` is the slice array as (address, length) pairs, `val_len` its length.
        let status = unsafe { raw::sol_sha256(refs.as_ptr() as *const u8, refs.len() as u64, out.as_mut_ptr()) };
        (status, out)
    }, |(status, out)| Json::obj([("status", (*status).into()), ("hash_result", rec::bytes(out))]));
}

pub fn corpus() -> Corpus {
    let mut c = Corpus::new("solana_define_syscall_5_1_0", &[("solana-define-syscall", "5.1.0")]);
    // No slice, one slice, and several with an empty and a repeated slice.
    let inputs: Vec<(&str, Vec<Vec<u8>>)> = vec![
        ("none", vec![]),
        ("one", vec![b"abc".to_vec()]),
        ("several", vec![vec![1, 2], vec![], b"abc".to_vec(), vec![1, 2]]),
    ];
    let digest = pattern(32, 77);
    for (name, slices) in &inputs {
        sha256(&mut c, format!("sol_sha256/{name}/status0"), slices,
            Script::new(vec![Reply::new("sol_sha256", 0).data(&digest)]));
        for &status in ERROR_STATUSES {
            sha256(&mut c, format!("sol_sha256/{name}/status{status}"), slices,
                Script::new(vec![Reply::new("sol_sha256", status)]));
        }
        sha256(&mut c, format!("sol_sha256/{name}/terminated"), slices,
            Script::new(vec![Reply::new("sol_sha256", 0).terminate("exceeded compute budget")]));
    }
    let messages: Vec<(&str, Vec<u8>)> = vec![
        ("empty", vec![]),
        ("ascii", b"hello".to_vec()),
        ("non_utf8", vec![0x68, 0xff, 0xfe, 0x80, 0x69]),
    ];
    for (name, message) in &messages {
        let args = Json::obj([("message", rec::bytes(message))]);
        syscall_case(&mut c, format!("sol_log_/{name}"), LOG, args, Script::new(vec![]),
            || unsafe { raw::sol_log_(message.as_ptr(), message.len() as u64) }, |_| Json::Null);
    }
    let panics: Vec<(&str, &[u8], u64, u64)> = vec![
        ("src_lib", b"src/lib.rs", 42, 7),
        ("empty_extremes", b"", u64::MAX, 0),
    ];
    for (name, file, line, column) in panics {
        let args = Json::obj([("file", rec::bytes(file)), ("line", line.into()), ("column", column.into())]);
        syscall_case(&mut c, format!("sol_panic_/{name}"), PANIC, args, Script::new(vec![]),
            || unsafe { raw::sol_panic_(file.as_ptr(), file.len() as u64, line, column) }, |_: &()| Json::Null);
    }
    syscall_case(&mut c, "abort/call".into(), ABORT, Json::Null, Script::new(vec![]),
        || unsafe { raw::abort() }, |_: &()| Json::Null);
    c
}
