use conformance_recorder::{self as rec, Corpus};
use solana_address::Address as Key;
const KEY_PATH: &str = "solana_address::Address";
const ZEROED: bool = false;
#[path = "../../address-profiles-common/operations.rs"]
mod operations;
#[path = "../../address-profiles-common/io.rs"]
mod io;

fn main() {
    rec::init();
    let mut c = Corpus::new("address_profiles_261", &[("solana-address", "2.6.1"), ("borsh", "1.6.0"), ("solana-loader-v3-interface", "6.1.1"), ("spl-associated-token-account-interface", "2.0.0")]);
    operations::record_values(&mut c, &["cmp"]);
    operations::record_create(&mut c);
    io::record_serialize(&mut c);
    io::record_reader(&mut c);
    operations::record_derived(&mut c, "spl_associated_token_account_interface::address::get_associated_token_address_with_program_id", |wallet, mint, token| spl_associated_token_account_interface::address::get_associated_token_address_with_program_id(wallet, mint, token));
    operations::record_derived(&mut c, "solana_loader_v3_interface::get_program_data_address", |program, _, _| solana_loader_v3_interface::get_program_data_address(program));
    c.write(&rec::out_dir()).expect("write corpus");
}
