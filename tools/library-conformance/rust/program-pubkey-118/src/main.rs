use conformance_recorder::{self as rec, Corpus};
use solana_program::pubkey::Pubkey as Key;
const KEY_PATH: &str = "solana_program::pubkey::Pubkey";
const ZEROED: bool = true;
#[path = "../../address-profiles-common/operations.rs"]
mod operations;
#[path = "../../address-profiles-common/io.rs"]
mod io;

fn main() {
    rec::init();
    let mut c = Corpus::new("program_pubkey_118", &[("solana-program", "1.18.26"), ("borsh", "0.10.4")]);
    operations::record_values(&mut c, &["to_bytes", "as_ref", "default", "eq", "clone"]);
    operations::record_create(&mut c);
    operations::record_find(&mut c);
    operations::record_seed(&mut c);
    io::record_serialize(&mut c);
    io::record_reader(&mut c);
    c.write(&rec::out_dir()).expect("write corpus");
}
