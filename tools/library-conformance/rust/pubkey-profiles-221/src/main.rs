use conformance_recorder::{self as rec, Corpus};
use solana_pubkey::Pubkey as Key;
const KEY_PATH: &str = "solana_pubkey::Pubkey";
const ZEROED: bool = true;
#[path = "../../address-profiles-common/operations.rs"]
mod operations;
#[path = "../../address-profiles-common/io.rs"]
mod io;

fn main() {
    rec::init();
    let mut c = Corpus::new("pubkey_profiles_221", &[("solana-pubkey", "2.2.1"), ("borsh", "0.10.4"), ("spl-associated-token-account-client", "2.0.0")]);
    operations::record_values(&mut c, &["new_from_array", "from", "to_bytes", "as_ref", "default", "eq", "clone", "cmp"]);
    operations::record_create(&mut c);
    operations::record_find(&mut c);
    operations::record_seed(&mut c);
    io::record_serialize(&mut c);
    io::record_reader(&mut c);
    operations::record_derived(&mut c, "spl_associated_token_account_client::address::get_associated_token_address_with_program_id", |wallet, mint, token| spl_associated_token_account_client::address::get_associated_token_address_with_program_id(wallet, mint, token));
    c.write(&rec::out_dir()).expect("write corpus");
}
