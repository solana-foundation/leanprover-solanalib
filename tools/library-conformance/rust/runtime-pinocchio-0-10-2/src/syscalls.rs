//! Syscall-backed functions at the pinned versions: pinocchio 0.10.2 `Clock::get` and
//! `Rent::get` (generic `sol_get_sysvar`), solana-msg 3.1.0 `sol_log`, solana-program 4.0.0
//! `sol_log_data` and `set_return_data`, solana-sha256-hasher 3.1.0 `hashv` and
//! solana-curve25519 3.1.12 `validate_edwards`.

use crate::syscall_cases::*;
use conformance_recorder::{self as rec, Corpus, Json};
use conformance_shim::{Reply, Script};
use pinocchio::sysvars::Sysvar;

pub fn pinocchio_getters(c: &mut Corpus) {
    use pinocchio::sysvars::{clock::Clock, rent::Rent};
    let mut values: Vec<(&'static str, Vec<u8>)> = clocks().into_iter().map(|(n, f)| (n, clock_bytes(f))).collect();
    // The shim copies at most the requested 40 bytes.
    let mut long = clock_bytes(clocks()[1].1);
    long.extend_from_slice(&[0xab; 8]);
    values.push(("longer_reply", long));
    for (name, script) in getter_scripts("sol_get_sysvar", &values) {
        syscall_case(c, format!("clock_get/{name}"), "<pinocchio::sysvars::clock::Clock as pinocchio::sysvars::Sysvar>::get",
            Json::Null, script, Clock::get, |r| program_error(r, |k: &Clock| {
                clock_json(k.slot, k.epoch_start_timestamp, k.epoch, k.leader_schedule_epoch, k.unix_timestamp)
            }));
    }
    let rent = |rate: u64, bits: u64| [rate.to_le_bytes(), bits.to_le_bytes()].concat();
    let values = vec![
        ("default", rent(6960, 0x4000_0000_0000_0000)),
        ("one", rent(3480, 0x3ff0_0000_0000_0000)),
        ("extremes", rent(u64::MAX, 0xfff8_0000_0000_0001)),
    ];
    for (name, script) in getter_scripts("sol_get_sysvar", &values) {
        syscall_case(c, format!("rent_get/{name}"), "<pinocchio::sysvars::rent::Rent as pinocchio::sysvars::Sysvar>::get",
            Json::Null, script, Rent::get, |r| program_error(r, |k: &Rent| {
                // `Rent` is `repr(C)` (rate, then eight threshold bytes); its fields are private.
                let b = unsafe { &*(k as *const Rent as *const [u8; 16]) };
                let rate = u64::from_le_bytes(b[..8].try_into().unwrap());
                let bits = u64::from_le_bytes(b[8..].try_into().unwrap());
                Json::obj([("lamports_per_byte", rate.into()), ("exemption_threshold", rec::f64_bits(f64::from_bits(bits)))])
            }));
    }
}

fn messages() -> Vec<(&'static str, String)> {
    vec![
        ("empty", String::new()),
        ("ascii", "hello".into()),
        ("unicode", "h\u{e9}llo \u{2713} \u{1f980}".into()),
        ("nul", "a\u{0}b".into()),
        ("newline", "line1\nline2".into()),
        ("long", "x".repeat(1000)),
    ]
}

pub fn msg_corpus() -> Corpus {
    let mut c = Corpus::new("solana_msg_3_1_0", &[("solana-msg", "3.1.0")]);
    for (name, m) in messages() {
        let args = Json::obj([("message", rec::bytes(m.as_bytes()))]);
        syscall_case(&mut c, format!("sol_log/{name}"), "solana_msg::sol_log", args, Script::new(vec![]),
            || solana_msg::sol_log(&m), |_| Json::Null);
    }
    c
}

pub fn program_corpus() -> Corpus {
    let mut c = Corpus::new("solana_program_4_0_0", &[("solana-program", "4.0.0")]);
    let field_sets: Vec<(&str, Vec<Vec<u8>>)> = vec![
        ("none", vec![]),
        ("one_empty", vec![vec![]]),
        ("three", vec![vec![1, 2], vec![], vec![3]]),
        ("large", vec![sparse(1024, 7)]),
        ("many", (0..5u8).map(|i| vec![i; i as usize]).collect()),
    ];
    for (name, fields) in field_sets {
        let args = Json::obj([("fields", hex_fields(&fields))]);
        let slices: Vec<&[u8]> = fields.iter().map(|f| f.as_slice()).collect();
        syscall_case(&mut c, format!("sol_log_data/{name}"), "solana_program::log::sol_log_data", args, Script::new(vec![]),
            || solana_program::log::sol_log_data(&slices), |_| Json::Null);
    }
    let datas: Vec<(&str, Vec<u8>)> = vec![
        ("empty", vec![]),
        ("three", vec![1, 2, 3]),
        ("max", sparse(1024, 3)),
        ("over_max", sparse(1025, 4)),
        ("large", sparse(4096, 5)),
    ];
    for (name, data) in datas {
        let args = Json::obj([("data", rec::bytes(&data))]);
        syscall_case(&mut c, format!("set_return_data/{name}"), "solana_program::program::set_return_data", args,
            Script::new(vec![]), || solana_program::program::set_return_data(&data), |_| Json::Null);
    }
    c
}

pub fn sha256_corpus() -> Corpus {
    let mut c = Corpus::new("solana_sha256_hasher_3_1_0", &[("solana-sha256-hasher", "3.1.0")]);
    let inputs: Vec<(&str, Vec<Vec<u8>>)> = vec![
        ("none", vec![]),
        ("one_empty", vec![vec![]]),
        ("abc", vec![b"abc".to_vec()]),
        ("three", vec![vec![1], vec![2, 3], vec![]]),
        ("large", vec![sparse(300, 1), sparse(64, 2)]),
    ];
    let digest = pattern(32, 77);
    for (name, slices) in &inputs {
        for &status in &[0u64, 1, u64::MAX] {
            let script = Script::new(vec![Reply::new("sol_sha256", status).data(&digest)]);
            let args = Json::obj([("slices", hex_fields(slices))]);
            let refs: Vec<&[u8]> = slices.iter().map(|s| s.as_slice()).collect();
            syscall_case(&mut c, format!("hashv/{name}/status{status}"), "solana_sha256_hasher::hashv", args, script,
                || solana_sha256_hasher::hashv(&refs), |h| rec::bytes(&h.to_bytes()));
        }
    }
    let script = Script::new(vec![Reply::new("sol_sha256", 0).terminate("exceeded compute budget")]);
    let args = Json::obj([("slices", hex_fields(&inputs[2].1))]);
    syscall_case(&mut c, "hashv/abc/terminated".into(), "solana_sha256_hasher::hashv", args, script,
        || solana_sha256_hasher::hashv(&[b"abc"]), |h| rec::bytes(&h.to_bytes()));
    c
}

pub fn curve_corpus() -> Corpus {
    use solana_curve25519::edwards::PodEdwardsPoint;
    let mut c = Corpus::new("solana_curve25519_3_1_12", &[("solana-curve25519", "3.1.12")]);
    // The encoding of the ed25519 base point, the identity, all ones and a pattern.
    let base: [u8; 32] = [
        0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    ];
    let mut identity = [0u8; 32];
    identity[0] = 1;
    let points: Vec<(&str, [u8; 32])> =
        vec![("base", base), ("identity", identity), ("ones", [0xff; 32]), ("pattern", pattern(32, 9).try_into().unwrap())];
    for (name, point) in &points {
        for &status in &[0u64, 1, 1 << 32, u64::MAX] {
            let script = Script::new(vec![Reply::new("sol_curve_validate_point", status)]);
            let args = Json::obj([("point", rec::bytes(point))]);
            let p = PodEdwardsPoint(*point);
            syscall_case(&mut c, format!("validate_edwards/{name}/status{status}"),
                "solana_curve25519::edwards::target_arch::validate_edwards", args, script,
                || solana_curve25519::edwards::validate_edwards(&p), |b| Json::from(*b));
        }
    }
    let script = Script::new(vec![Reply::new("sol_curve_validate_point", 0).terminate("exceeded compute budget")]);
    let args = Json::obj([("point", rec::bytes(&base))]);
    syscall_case(&mut c, "validate_edwards/base/terminated".into(),
        "solana_curve25519::edwards::target_arch::validate_edwards", args, script,
        || solana_curve25519::edwards::validate_edwards(&PodEdwardsPoint(base)), |b| Json::from(*b));
    c
}
