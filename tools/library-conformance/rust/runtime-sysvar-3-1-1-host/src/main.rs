//! Records the host branches at the pinned versions: solana-sysvar 3.1.1 `Clock::get` and
//! `Rent::get` through `program_stubs` (target `hostStub`), and solana-msg 3.1.0 `sol_log`
//! printing a line (target `hostStd`).
#![feature(internal_output_capture)]

#[allow(dead_code)]
#[path = "../../runtime-common/host_stubs.rs"]
mod host_stubs;
#[allow(dead_code)]
#[path = "../../runtime-common/syscall_cases.rs"]
mod syscall_cases;

use conformance_recorder::{self as rec, Corpus, Json};
use host_stubs::*;
use solana_sysvar::program_stubs;
use syscall_cases::{clock_bytes, clock_json, clocks, program_error};

fn rent_json(r: &solana_rent::Rent) -> Json {
    Json::obj([
        ("lamports_per_byte_year", r.lamports_per_byte_year.into()),
        ("exemption_threshold", rec::f64_bits(r.exemption_threshold)),
        ("burn_percent", r.burn_percent.into()),
    ])
}

/// Getter scripts on the stub: success with each value (copied over the `Default`
/// destination), an error status, and a stub that panics.
fn scripts(syscall: &'static str, values: Vec<(&'static str, Vec<u8>)>) -> Vec<(String, Vec<StubReply>)> {
    let mut v: Vec<(String, Vec<StubReply>)> =
        values.into_iter().map(|(n, b)| (format!("ok/{n}"), vec![StubReply::new(syscall, 0).data(&b)])).collect();
    v.push(("status1".into(), vec![StubReply::new(syscall, 1)]));
    v.push(("status_max".into(), vec![StubReply::new(syscall, u64::MAX)]));
    v.push(("panic".into(), vec![StubReply::new(syscall, 0).panic("stub panic")]));
    v
}

fn sysvar_corpus() -> Corpus {
    use solana_sysvar::{clock::Clock, rent::Rent, Sysvar};
    let mut c = Corpus::new("solana_sysvar_3_1_1_host", &[("solana-sysvar", "3.1.1"), ("solana-rent", "3.0.0")]);
    let clock_values = vec![("values", clock_bytes(clocks()[1].1)), ("no_bytes", vec![]), ("slot_only", 77u64.to_le_bytes().to_vec())];
    for (name, replies) in scripts("sol_get_clock_sysvar", clock_values) {
        host_case(&mut c, format!("clock_get/{name}"),
            "solana_sysvar::clock::<impl solana_sysvar::Sysvar for solana_clock::Clock>::get", Json::Null, replies,
            Clock::get, |r| program_error(r, |k: &Clock| {
                clock_json(k.slot, k.epoch_start_timestamp, k.epoch, k.leader_schedule_epoch, k.unix_timestamp)
            }));
    }
    let mut rent = 1u64.to_le_bytes().to_vec();
    rent.extend_from_slice(&1.0f64.to_le_bytes());
    rent.push(100);
    let rent_values = vec![("values", rent), ("no_bytes", vec![])];
    for (name, replies) in scripts("sol_get_rent_sysvar", rent_values) {
        host_case(&mut c, format!("rent_get/{name}"),
            "solana_sysvar::rent::<impl solana_sysvar::Sysvar for solana_rent::Rent>::get", Json::Null, replies,
            Rent::get, |r| program_error(r, rent_json));
    }
    c
}

fn msg_corpus() -> Corpus {
    let mut c = Corpus::new("solana_msg_3_1_0_host", &[("solana-msg", "3.1.0")]);
    for (name, m) in [("empty", ""), ("ascii", "hello"), ("unicode", "h\u{e9}llo \u{2713} \u{1f980}"), ("newline", "a\nb")] {
        let args = Json::obj([("message", rec::bytes(m.as_bytes()))]);
        host_case(&mut c, format!("sol_log/{name}"), "solana_msg::sol_log", args, vec![], || solana_msg::sol_log(m),
            |_| Json::Null);
    }
    c
}

fn main() {
    rec::init();
    let out = rec::out_dir();
    sysvar_corpus().write(&out).expect("write corpus");
    msg_corpus().write(&out).expect("write corpus");
}
