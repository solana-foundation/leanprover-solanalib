//! Records solana-address 2.6.0 on the plain host branch: `find_program_address` and `is_on_curve`
//! computed in process, against an explicit Crypto table.

#[path = "../../address-common/host.rs"]
mod host;

use conformance_recorder::{self as rec, Corpus};

fn main() {
    rec::init();
    let out = rec::out_dir();
    let mut c = Corpus::new(
        "solana_address_2_6_0_host",
        &[("solana-address", "2.6.0"), ("sha2", "0.10.9"), ("curve25519-dalek", "4.1.3")],
    );
    host::record_find(&mut c);
    host::record_is_on_curve(&mut c);
    c.write(&out).expect("write corpus");
}
