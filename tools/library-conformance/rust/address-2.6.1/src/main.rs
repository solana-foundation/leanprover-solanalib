//! Records solana-address 2.6.1 on the selected Solana branch (`--cfg
//! target_os="solana"`): the value operations of `Address`, and
//! `try_find_program_address`/`find_program_address` through the
//! `sol_try_find_program_address` test shim.

#[allow(dead_code)]
#[path = "../../address-common/syscalls.rs"]
mod syscalls;
#[path = "../../address-common/values.rs"]
mod values;

use conformance_recorder::{self as rec, Corpus};

fn main() {
    rec::init();
    let out = rec::out_dir();
    let mut c = Corpus::new("solana_address_2_6_1_api", &[("solana-address", "2.6.1")]);
    values::record(&mut c);
    syscalls::record_pda(&mut c);
    c.write(&out).expect("write corpus");
}
