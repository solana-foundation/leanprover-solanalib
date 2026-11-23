//! Records solana-rent 3.0.0 `Rent::minimum_balance` without overflow checks: the same cases as
//! `runtime-rent-3-0-0`, under the model wrapping arithmetic profile.

#[allow(dead_code)]
#[path = "../../runtime-common/rent_cases.rs"]
mod rent_cases;
#[path = "../../runtime-common/rent_solana_rent_3_0_0.rs"]
mod rent_solana_rent_3_0_0;

use conformance_recorder::{self as rec, Corpus};

fn main() {
    rec::init();
    assert!(!rent_cases::overflow_checks(), "this driver is built without overflow checks");
    let out = rec::out_dir();
    let mut c = Corpus::new("solana_rent_3_0_0_wrapping", &[("solana-rent", "3.0.0")]);
    rent_solana_rent_3_0_0::record(&mut c, true);
    c.write(&out).expect("write corpus");
}
