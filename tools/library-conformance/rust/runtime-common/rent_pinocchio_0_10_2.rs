//! pinocchio 0.10.2 `Rent::try_minimum_balance`, recorded by the checked and wrapping arithmetic drivers
//! (checked and wrapping arithmetic profiles).

use crate::rent_cases::*;
use conformance_recorder::{self as rec, Corpus, Json, Record};

const TRY_MINIMUM_BALANCE: &str = "pinocchio::sysvars::rent::Rent::try_minimum_balance";

/// pinocchio 0.10.2 keeps the `Rent` fields private; `Rent::from_bytes` reads its 16-byte
/// representation (rate, then the eight little-endian threshold bytes) from an 8-aligned
/// buffer.
#[repr(C, align(8))]
struct RentBytes([u8; 16]);

fn rent_bytes(rate: u64, threshold_bits: u64) -> RentBytes {
    let mut b = [0u8; 16];
    b[..8].copy_from_slice(&rate.to_le_bytes());
    b[8..].copy_from_slice(&threshold_bits.to_le_bytes());
    RentBytes(b)
}

fn profile() -> Json {
    profile_json(&[("target_bpf", Json::from(cfg!(target_arch = "bpf")))])
}

fn try_minimum_balance(c: &mut Corpus, id: String, rate: u64, bits: u64, data_len: u64) {
    let bytes = rent_bytes(rate, bits);
    let rent = pinocchio::sysvars::rent::Rent::from_bytes(&bytes.0).expect("aligned 16-byte Rent");
    let state = profile();
    let args = Json::obj([
        (
            "rent",
            Json::obj([("lamports_per_byte", rate.into()), ("exemption_threshold", rec::f64_bits(f64::from_bits(bits)))]),
        ),
        ("data_len", data_len.into()),
    ]);
    let outcome = profile_call(&state, || rent.try_minimum_balance(data_len as usize), |r| match r {
        Ok(v) => rec::ok(Json::from(*v)),
        Err(e) => rec::err(format!("{e:?}").into()),
    });
    c.push(Record {
        id,
        function: TRY_MINIMUM_BALANCE,
        generics: vec![],
        layout: None,
        state,
        args,
        outcome,
        observed: None,
    });
}

/// pinocchio 0.10.2 `try_minimum_balance` at every selected case; `wrapping_only` keeps the
/// cases whose outcome depends on overflow checking.
pub fn record(c: &mut Corpus, wrapping_only: bool) {
    for (name, rate, bits, len, wrapping) in pinocchio_0_10_2_cases() {
        if wrapping || !wrapping_only {
            try_minimum_balance(c, format!("try_minimum_balance/{name}"), rate, bits, len);
        }
    }
}
