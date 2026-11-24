//! Records the pinned versions: solana-instruction-view 2.1.0 (seed and signer
//! conversions, read-only signer metadata, fixed-array `invoke_signed`), pinocchio-system 0.6.0
//! (`Allocate`, `Assign`, `Transfer`) and pinocchio-associated-token-account 0.4.0
//! (`CreateIdempotent::invoke`). CPI cases run over a loader input region (`conformance-accounts`)
//! with the shim `sol_invoke_signed_c` (`conformance-shim`).

mod cpi;
mod values;

use conformance_recorder::{self as rec, Corpus};
use conformance_shim as _;

fn main() {
    rec::init();
    let out = rec::out_dir();

    let mut view = Corpus::new("solana_instruction_view_2_1_0", &[("solana-instruction-view", "2.1.0")]);
    values::record(&mut view);
    cpi::record_invoke_signed(&mut view);
    cpi::record_invoke_signed_recording(&mut view);

    let mut system = Corpus::new(
        "pinocchio_system_0_6_0",
        &[("pinocchio-system", "0.6.0"), ("solana-instruction-view", "2.1.0"), ("solana-account-view", "2.0.0")],
    );
    cpi::record_system(&mut system);

    let mut ata = Corpus::new(
        "pinocchio_associated_token_account_0_4_0",
        &[("pinocchio-associated-token-account", "0.4.0"), ("solana-instruction-view", "2.1.0"),
          ("solana-account-view", "2.0.0")],
    );
    cpi::record_ata(&mut ata);

    for corpus in [view, system, ata] {
        corpus.write(&out).expect("write corpus");
    }
}
