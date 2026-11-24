//! Records the runtime helpers at the pinned versions: solana-rent 3.0.0
//! `Rent::minimum_balance` (integer then binary64 arithmetic, no guard) and solana-sysvar 3.1.1
//! `Clock::get` and `Rent::get` (typed syscalls into a `Default` destination).

#[allow(dead_code)]
#[path = "../../runtime-common/rent_cases.rs"]
mod rent_cases;
#[path = "../../runtime-common/rent_solana_rent_3_0_0.rs"]
mod rent_solana_rent_3_0_0;
#[allow(dead_code)]
#[path = "../../runtime-common/syscall_cases.rs"]
mod syscall_cases;

use conformance_shim as _;
use syscall_cases::*;

use conformance_recorder::{self as rec, Corpus, Json};
use rent_solana_rent_3_0_0::rent_json;
use solana_rent::Rent;

fn rent_corpus() -> Corpus {
    let mut c = Corpus::new("solana_rent_3_0_0", &[("solana-rent", "3.0.0")]);
    rent_solana_rent_3_0_0::record(&mut c, false);
    c
}

fn sysvar_corpus() -> Corpus {
    use solana_sysvar::{clock::Clock, Sysvar};
    let mut c = Corpus::new("solana_sysvar_3_1_1", &[("solana-sysvar", "3.1.1"), ("solana-rent", "3.0.0")]);
    // The typed getters copy the reply into a `Default` value: a short or missing reply leaves
    // the rest of the default.
    let mut values: Vec<(&'static str, Vec<u8>)> = clocks().into_iter().map(|(n, f)| (n, clock_bytes(f))).collect();
    values.push(("no_bytes", vec![]));
    values.push(("slot_only", 77u64.to_le_bytes().to_vec()));
    for (name, script) in getter_scripts("sol_get_clock_sysvar", &values) {
        syscall_case(&mut c, format!("clock_get/{name}"),
            "solana_sysvar::clock::<impl solana_sysvar::Sysvar for solana_clock::Clock>::get", Json::Null, script,
            Clock::get, |r| program_error(r, |k: &Clock| {
                clock_json(k.slot, k.epoch_start_timestamp, k.epoch, k.leader_schedule_epoch, k.unix_timestamp)
            }));
    }
    // `solana_rent::Rent` is `repr(C)`: rate, threshold, burn percent and 7 padding bytes. A
    // full reply is 17 meaningful bytes, possibly with the padding.
    let rent = |rate: u64, bits: u64, burn: u8| {
        let mut b = [rate.to_le_bytes(), bits.to_le_bytes()].concat();
        b.push(burn);
        b
    };
    let mut padded = rent(1, 0x3ff0_0000_0000_0000, 100);
    padded.extend_from_slice(&[0xcc; 7]);
    let values: Vec<(&'static str, Vec<u8>)> = vec![
        ("default", rent(3480, 0x4000_0000_0000_0000, 50)),
        ("extremes", rent(u64::MAX, 0xfff8_0000_0000_0001, 255)),
        ("padded", padded),
        ("no_bytes", vec![]),
        ("rate_only", 6960u64.to_le_bytes().to_vec()),
    ];
    for (name, script) in getter_scripts("sol_get_rent_sysvar", &values) {
        syscall_case(&mut c, format!("rent_get/{name}"),
            "solana_sysvar::rent::<impl solana_sysvar::Sysvar for solana_rent::Rent>::get", Json::Null, script,
            Rent::get, |r| program_error(r, rent_json));
    }
    c
}

fn main() {
    rec::init();
    let out = rec::out_dir();
    rent_corpus().write(&out).expect("write corpus");
    sysvar_corpus().write(&out).expect("write corpus");
}
