//! Records the pinned versions of the libraries in the instruction family:
//! solana-instruction 3.4.0 (`AccountMeta` constructors, `Instruction::new_with_bincode`),
//! solana-system-interface 3.2.0 with the `bincode` feature (`create_account`, `transfer`),
//! solana-borsh 3.0.2 `v1::try_from_slice_unchecked`, switchboard-on-demand 0.12.1
//! `PullFeedAccountData::parse` and the pyth-solana-receiver-sdk 2.0.0 price getter.

mod borsh_unchecked;
mod builder;
#[path = "../../instructions-common/instruction.rs"]
mod common;
mod pyth_getter;
mod switchboard;
#[path = "../../instructions-common/system.rs"]
mod system;

use conformance_recorder::{self as rec, Corpus};

fn main() {
    rec::init();
    let out = rec::out_dir();

    let mut instruction = Corpus::new("solana_instruction_3_4_0", &[("solana-instruction", "3.4.0")]);
    builder::record_meta(&mut instruction);
    builder::record_bincode(&mut instruction);

    let mut values = Corpus::new("solana_system_interface_3_2_0", &[("solana-system-interface", "3.2.0")]);
    system::record(&mut values);
    let mut operational =
        Corpus::new("solana_system_interface_3_2_0_bincode", &[("solana-system-interface", "3.2.0")]);
    system::record(&mut operational);

    let mut borsh = Corpus::new("solana_borsh_3_0_2", &[("solana-borsh", "3.0.2"), ("borsh", "1.6.1")]);
    borsh_unchecked::record(&mut borsh);

    let mut feed = Corpus::new(
        "switchboard_on_demand_0_12_1",
        &[("switchboard-on-demand", "0.12.1"), ("bytemuck", "1.25.0")],
    );
    switchboard::record(&mut feed);

    let mut getter =
        Corpus::new("pyth_solana_receiver_sdk_2_0_0_getter", &[("pyth-solana-receiver-sdk", "2.0.0")]);
    pyth_getter::record(&mut getter);

    for corpus in [instruction, values, operational, borsh, feed, getter] {
        corpus.write(&out).expect("write corpus");
    }
}
