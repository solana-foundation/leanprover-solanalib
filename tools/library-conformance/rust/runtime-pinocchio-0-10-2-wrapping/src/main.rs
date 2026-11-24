//! Records pinocchio 0.10.2 `Rent::try_minimum_balance` without overflow checks: the same
//! cases as `runtime-pinocchio-0-10-2`, under the wrapping arithmetic profile of the models.

#[allow(dead_code)]
#[path = "../../runtime-common/rent_cases.rs"]
mod rent_cases;
#[path = "../../runtime-common/rent_pinocchio_0_10_2.rs"]
mod rent_pinocchio_0_10_2;

use conformance_recorder::{self as rec, Corpus};

fn main() {
    rec::init();
    assert!(!rent_cases::overflow_checks(), "this driver is built without overflow checks");
    let out = rec::out_dir();
    let mut c = Corpus::new("pinocchio_0_10_2_wrapping", &[("pinocchio", "0.10.2")]);
    rent_pinocchio_0_10_2::record(&mut c, true);
    c.write(&out).expect("write corpus");
}
