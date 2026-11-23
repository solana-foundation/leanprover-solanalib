//! Records solana-address 2.6.0 on the selected Solana branch (`--cfg
//! target_os="solana"`): the value operations of `Address`, and
//! `try_find_program_address`/`find_program_address` through the
//! `sol_try_find_program_address` test shim and `is_on_curve` through
//! `sol_curve_validate_point`.

#[path = "../../address-common/syscalls.rs"]
mod syscalls;
#[path = "../../address-common/values.rs"]
mod values;

use conformance_recorder::{self as rec, Corpus};

fn main() {
    rec::init();
    let out = rec::out_dir();
    let mut c = Corpus::new("solana_address_2_6_0_api", &[("solana-address", "2.6.0")]);
    values::record(&mut c);
    syscalls::record_pda(&mut c);
    syscalls::record_curve(&mut c);
    c.write(&out).expect("write corpus");
}
