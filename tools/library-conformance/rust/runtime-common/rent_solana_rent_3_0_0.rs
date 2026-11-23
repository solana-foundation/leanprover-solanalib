//! solana-rent 3.0.0 `Rent::minimum_balance`, recorded by the checked and wrapping arithmetic drivers
//! (checked and wrapping arithmetic profiles).

use crate::rent_cases::*;
use conformance_recorder::{self as rec, Corpus, Json, Record};
use solana_rent::Rent;

const MINIMUM_BALANCE: &str = "solana_rent::Rent::minimum_balance";

pub fn rent_json(r: &Rent) -> Json {
    Json::obj([
        ("lamports_per_byte_year", r.lamports_per_byte_year.into()),
        ("exemption_threshold", rec::f64_bits(r.exemption_threshold)),
        ("burn_percent", r.burn_percent.into()),
    ])
}

fn minimum_balance(c: &mut Corpus, id: String, rent: Rent, data_len: u64) {
    let state = profile_json(&[]);
    let args = Json::obj([("rent", rent_json(&rent)), ("data_len", data_len.into())]);
    let outcome = profile_call(&state, || rent.minimum_balance(data_len as usize), |v| Json::from(*v));
    c.push(Record {
        id,
        function: MINIMUM_BALANCE,
        generics: vec![],
        layout: None,
        state,
        args,
        outcome,
        observed: None,
    });
}

/// solana-rent 3.0.0 `minimum_balance` at every selected case; `wrapping_only` keeps the cases
/// whose outcome depends on overflow checking.
pub fn record(c: &mut Corpus, wrapping_only: bool) {
    let rent = |rate: u64, bits: u64, burn: u8| Rent {
        lamports_per_byte_year: rate,
        exemption_threshold: f64::from_bits(bits),
        burn_percent: burn,
    };
    for (name, rate, bits, len, wrapping) in sdk_cases() {
        if wrapping || !wrapping_only {
            minimum_balance(c, format!("minimum_balance/{name}"), rent(rate, bits, 50), len);
        }
    }
    if !wrapping_only {
        // The burn percentage does not enter the calculation.
        minimum_balance(c, "minimum_balance/burn_ignored".into(), rent(3480, TWO, 255), 165);
    }
}
