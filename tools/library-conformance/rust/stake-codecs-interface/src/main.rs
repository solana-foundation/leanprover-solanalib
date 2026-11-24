use conformance_recorder::{self as rec, Corpus};
use solana_address_lookup_table_interface::state::{AddressLookupTable, LookupTableMeta, ProgramState};
use solana_borsh::v0_10::get_instance_packed_len;
use solana_pubkey::Pubkey;
const LOOKUP_FUNCTION: &str = "solana_address_lookup_table_interface::state::AddressLookupTable::<'_>::deserialize";
const PACKED_LEN_FUNCTION: &str = "solana_borsh::v0_10::get_instance_packed_len";
const SERIALIZER_NAME: &str = "conformance_stake_codecs_interface::packed_len::Probe";
#[path = "../../stake-codec-cases/alloc_trace.rs"] mod alloc_trace;
#[path = "../../stake-codec-cases/lookup.rs"] mod lookup;
#[path = "../../stake-codec-cases/packed_len.rs"] mod packed_len;
fn main() {
    rec::init();
    let mut c = Corpus::new("stake_codecs_interface", &[("solana-address-lookup-table-interface", "2.2.2"), ("solana-borsh", "2.2.1"), ("borsh", "0.10.4"), ("bincode", "1.3.3")]);
    lookup::record(&mut c); packed_len::record(&mut c);
    c.write(&rec::out_dir()).expect("write corpus");
}
