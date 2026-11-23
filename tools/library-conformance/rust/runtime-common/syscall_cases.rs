//! Case material shared by the runtime drivers whose functions make syscalls.
//!
//! Every case runs in `conformance_shim::case`: its state before the call is the script (the
//! replies the case chose) and an empty request log; after the call, the unconsumed replies
//! and every request. Results are recorded by the closure; panics and terminal syscalls become
//! unwound and terminated outcomes in the shim.

use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, Reply, Script};

pub fn syscall_case<T>(
    c: &mut Corpus,
    id: String,
    function: &'static str,
    args: Json,
    script: Script,
    f: impl FnOnce() -> T,
    enc: impl Fn(&T) -> Json,
) {
    let state = Json::obj([("syscalls", script.state_before())]);
    let outcome = shim::case(&script, || {
        let result = f();
        rec::returned(enc(&result), Json::obj([("syscalls", shim::state())]))
    });
    c.push(Record { id, function, generics: vec![], layout: None, state, args, outcome, observed: None });
}

/// The Clock values: zeros, ordinary values with a negative timestamp, and the extremes of
/// every field.
pub fn clocks() -> Vec<(&'static str, [u64; 5])> {
    vec![
        ("zero", [0; 5]),
        ("values", [123_456_789, (-5i64) as u64, 300, 301, 1_700_000_000]),
        ("extremes", [u64::MAX, i64::MIN as u64, u64::MAX, 0, i64::MAX as u64]),
    ]
}

pub fn clock_bytes(fields: [u64; 5]) -> Vec<u8> {
    fields.iter().flat_map(|f| f.to_le_bytes()).collect()
}

pub fn clock_json(slot: u64, epoch_start_timestamp: i64, epoch: u64, leader_schedule_epoch: u64, unix_timestamp: i64) -> Json {
    Json::obj([
        ("slot", slot.into()),
        ("epoch_start_timestamp", epoch_start_timestamp.into()),
        ("epoch", epoch.into()),
        ("leader_schedule_epoch", leader_schedule_epoch.into()),
        ("unix_timestamp", unix_timestamp.into()),
    ])
}

pub fn program_error<T>(r: &Result<T, impl core::fmt::Debug>, ok: impl Fn(&T) -> Json) -> Json {
    match r {
        Ok(v) => rec::ok(ok(v)),
        Err(e) => rec::err(format!("{e:?}").into()),
    }
}

/// Status words other than success: the two the generic getter distinguishes (1, 2), an
/// unexpected small one, one whose low 32 bits are zero, and the largest.
pub const ERROR_STATUSES: &[u64] = &[1, 2, 3, 1 << 32, u64::MAX];

/// Getter scripts: success with each value, every error status without and (for the first)
/// with written bytes, and a syscall that does not return.
pub fn getter_scripts(syscall: &str, values: &[(&'static str, Vec<u8>)]) -> Vec<(String, Script)> {
    let mut v = vec![];
    for (name, bytes) in values {
        v.push((format!("ok/{name}"), Script::new(vec![Reply::new(syscall, 0).data(bytes)])));
    }
    for &status in ERROR_STATUSES {
        v.push((format!("status{status}"), Script::new(vec![Reply::new(syscall, status)])));
    }
    v.push((
        "status1/written".to_string(),
        Script::new(vec![Reply::new(syscall, 1).data(&values[values.len() - 1].1)]),
    ));
    v.push((
        "terminated".to_string(),
        Script::new(vec![Reply::new(syscall, 0).terminate("exceeded compute budget")]),
    ));
    v
}

pub fn pattern(n: usize, seed: u8) -> Vec<u8> {
    (0..n).map(|i| (i as u8).wrapping_mul(29).wrapping_add(seed)).collect()
}

/// `n` zero bytes except the first, the middle and the last: long payloads whose every byte
/// position is still checked, cheap under the corpus zero-run encoding.
pub fn sparse(n: usize, seed: u8) -> Vec<u8> {
    let mut v = vec![0u8; n];
    for i in [0, n / 2, n.saturating_sub(1)] {
        if i < n {
            v[i] = seed.wrapping_add(i as u8) | 1;
        }
    }
    v
}

pub fn hex_fields(fields: &[Vec<u8>]) -> Json {
    Json::arr(fields.iter(), |f| rec::bytes(f))
}
