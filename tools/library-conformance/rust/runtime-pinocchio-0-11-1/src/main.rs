//! Records pinocchio 0.11.1, at its exact pinned version: `Rent::try_minimum_balance`,
//! `Clock::get` (generic `sol_get_sysvar`) and the Instructions sysvar over a generic receiver
//! (`instructions.rs`), and over loader-serialized accounts `Rent::from_account_view`,
//! `Instructions::try_from` and the Instructions sysvar through its `Ref` (`accounts.rs`); and
//! the raw `sol_sha256`, `sol_log_`, `sol_panic_` and `abort` of solana-define-syscall 5.1.0,
//! which pinocchio 0.11.1 links, called directly (`raw_syscalls.rs`).

#[allow(dead_code)]
#[path = "../../runtime-common/rent_cases.rs"]
mod rent_cases;
#[allow(dead_code)]
#[path = "../../runtime-common/syscall_cases.rs"]
mod syscall_cases;
pub mod instructions;
mod accounts;
mod raw_syscalls;

use conformance_shim as _;

use conformance_recorder::{self as rec, Corpus, Json, Record};
use rent_cases::*;

const TRY_MINIMUM_BALANCE: &str = "pinocchio::sysvars::rent::Rent::try_minimum_balance";

fn try_minimum_balance(c: &mut Corpus, id: String, rate: u64, data_len: u64) {
    // pinocchio 0.11.1 keeps the rate private; `Rent::from_bytes` reads it (unaligned) from
    // its eight little-endian bytes.
    let rent = pinocchio::sysvars::rent::Rent::from_bytes(&rate.to_le_bytes()).expect("8-byte Rent");
    let args = Json::obj([("rent", Json::obj([("lamports_per_byte", rate.into())])), ("data_len", data_len.into())]);
    let outcome = match rec::catch(|| rent.try_minimum_balance(data_len as usize)) {
        Ok(Ok(v)) => rec::returned(rec::ok(Json::from(v)), Json::Null),
        Ok(Err(e)) => rec::returned(rec::err(format!("{e:?}").into()), Json::Null),
        Err(reason) => rec::unwound(reason, Json::Null),
    };
    c.push(Record {
        id,
        function: TRY_MINIMUM_BALANCE,
        generics: vec![],
        layout: None,
        state: Json::Null,
        args,
        outcome,
        observed: None,
    });
}

fn pinocchio_corpus() -> Corpus {
    let mut c = Corpus::new("pinocchio_0_11_1", &[("pinocchio", "0.11.1")]);
    for (name, rate, len) in pinocchio_0_11_1_cases() {
        try_minimum_balance(&mut c, format!("try_minimum_balance/{name}"), rate, len);
    }
    clock_get(&mut c);
    instructions::record(&mut c);
    c
}

fn clock_get(c: &mut Corpus) {
    use pinocchio::sysvars::{clock::Clock, Sysvar};
    use syscall_cases::*;
    let mut values: Vec<(&'static str, Vec<u8>)> = clocks().into_iter().map(|(n, f)| (n, clock_bytes(f))).collect();
    let mut long = clock_bytes(clocks()[1].1);
    long.extend_from_slice(&[0xab; 8]);
    values.push(("longer_reply", long));
    for (name, script) in getter_scripts("sol_get_sysvar", &values) {
        syscall_case(c, format!("clock_get/{name}"), "<pinocchio::sysvars::clock::Clock as pinocchio::sysvars::Sysvar>::get",
            Json::Null, script, Clock::get, |r| program_error(r, |k: &Clock| {
                clock_json(k.slot, k.epoch_start_timestamp, k.epoch, k.leader_schedule_epoch, k.unix_timestamp)
            }));
    }
}

fn main() {
    rec::init();
    let out = rec::out_dir();
    pinocchio_corpus().write(&out).expect("write corpus");
    accounts::corpus().write(&out).expect("write corpus");
    raw_syscalls::corpus().write(&out).expect("write corpus");
}
