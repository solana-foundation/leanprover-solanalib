//! Exact SDK rent calls over the shared binary64 and integer boundary cases.
use crate::{rent_cases, Rent};
use conformance_recorder::{self as rec, Corpus, Json, Record};

pub fn json(r: &Rent) -> Json {
    Json::obj([("lamports_per_byte_year", r.lamports_per_byte_year.into()),
        ("exemption_threshold", rec::f64_bits(r.exemption_threshold)),
        ("burn_percent", r.burn_percent.into())])
}

pub fn record(c: &mut Corpus, minimum: Option<&'static str>, exempt: &'static str) {
    let state = rent_cases::profile_json(&[]);
    for (name, rate, threshold, len, _) in rent_cases::sdk_cases() {
        let rent = Rent { lamports_per_byte_year: rate,
            exemption_threshold: f64::from_bits(threshold), burn_percent: 253 };
        if let Some(function) = minimum {
            c.push(Record { id: format!("minimum/{name}"), function, generics: vec![], layout: None,
                state: state.clone(), args: Json::obj([("rent", json(&rent)), ("data_len", len.into())]),
                outcome: rent_cases::profile_call(&state, || rent.minimum_balance(len as usize), |v| (*v).into()),
                observed: None });
        }
        let balances: &[u64] = if name == "default" { &[0, 890879, 890880, 890881, u64::MAX] } else { &[0, u64::MAX] };
        for &balance in balances {
            c.push(Record { id: format!("exempt/{name}/{balance}"), function: exempt, generics: vec![], layout: None,
                state: state.clone(), args: Json::obj([("rent", json(&rent)), ("data_len", len.into()), ("balance", balance.into())]),
                outcome: rent_cases::profile_call(&state, || rent.is_exempt(balance, len as usize), |v| (*v).into()),
                observed: None });
        }
    }
}
