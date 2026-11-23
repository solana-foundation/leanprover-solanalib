//! Records spl-token-interface 2.0.0 and spl-token-2022-interface 3.1.1
//! natively (host build of the Solana branches; see `.cargo/config.toml`).
//! Writes four corpus files into the directory given as the first argument.

mod common;
mod extensions;
mod fees;
mod instructions;

use conformance_recorder::Corpus;

#[global_allocator]
static ALLOCATOR: common::Counting = common::Counting;

fn main() {
    conformance_recorder::init();
    let out = conformance_recorder::out_dir();

    let mut legacy = Corpus::new("spl_token_interface_2_0_0", &[("spl-token-interface", "2.0.0")]);
    instructions::legacy(&mut legacy);
    legacy.write(&out).unwrap();

    let interface = [("spl-token-2022-interface", "3.1.1")];
    let mut token = Corpus::new("spl_token_2022_interface_3_1_1", &interface);
    instructions::token_2022(&mut token);
    token.write(&out).unwrap();

    let mut fee = Corpus::new("spl_token_2022_interface_3_1_1_fee", &interface);
    fees::record(&mut fee);
    fee.write(&out).unwrap();

    let mut extension = Corpus::new("spl_token_2022_interface_3_1_1_extension", &interface);
    extensions::record(&mut extension);
    extension.write(&out).unwrap();
}
