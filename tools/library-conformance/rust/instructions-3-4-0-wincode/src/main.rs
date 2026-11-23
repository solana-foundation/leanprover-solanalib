//! Records the pinned versions: solana-instruction 3.4.0 `Instruction::new_with_wincode`,
//! solana-system-interface 3.2.0 built with the selected features (`bincode` and `wincode`, so
//! `create_instruction` calls `new_with_wincode`), and solana-instruction-view 1.0.0 (seed and
//! signer conversions, the checked slice CPI entries over a loader input region and the shim).

#[allow(dead_code)]
#[path = "../../instructions-common/instruction.rs"]
mod common;
mod cpi;
#[path = "../../instructions-common/system.rs"]
mod system;
mod wincode_builder;

use conformance_recorder::{self as rec, Corpus};
use conformance_shim as _;

fn main() {
    rec::init();
    let out = rec::out_dir();

    let mut instruction =
        Corpus::new("solana_instruction_3_4_0_wincode", &[("solana-instruction", "3.4.0"), ("wincode", "0.5.5")]);
    wincode_builder::record(&mut instruction);

    let mut system = Corpus::new(
        "solana_system_interface_3_2_0_wincode",
        &[("solana-system-interface", "3.2.0"), ("wincode", "0.5.5")],
    );
    system::record(&mut system);

    let mut view = Corpus::new(
        "solana_instruction_view_1_0_0",
        &[("solana-instruction-view", "1.0.0"), ("solana-account-view", "1.0.0")],
    );
    cpi::record_values(&mut view);
    cpi::record_slices(&mut view);

    for corpus in [instruction, system, view] {
        corpus.write(&out).expect("write corpus");
    }
}
