#![allow(deprecated)]
use conformance_recorder::{self as rec, Corpus};
use solana_program::{address_lookup_table::state::{AddressLookupTable, LookupTableMeta, ProgramState},
    borsh0_10::get_instance_packed_len, pubkey::Pubkey};
const LOOKUP_FUNCTION: &str = "solana_program::address_lookup_table::state::AddressLookupTable::<'_>::deserialize";
const PACKED_LEN_FUNCTION: &str = "solana_program::borsh0_10::get_instance_packed_len";
const SERIALIZER_NAME: &str = "conformance_stake_codecs_program::packed_len::Probe";
#[path = "../../stake-codec-cases/alloc_trace.rs"] mod alloc_trace;
#[path = "../../stake-codec-cases/lookup.rs"] mod lookup;
#[path = "../../stake-codec-cases/packed_len.rs"] mod packed_len;
fn main() {
    rec::init();
    let mut c = Corpus::new("stake_codecs_program", &[("solana-program", "1.18.26"), ("bincode", "1.3.3"), ("borsh", "0.10.4")]);
    lookup::record(&mut c); packed_len::record(&mut c);
    c.write(&rec::out_dir()).expect("write corpus");
}
