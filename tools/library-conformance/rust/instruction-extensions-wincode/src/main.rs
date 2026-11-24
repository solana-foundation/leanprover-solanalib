//! Exact version profile for generic instruction construction and cloning.
use solana_address::Address as Pubkey;
use solana_instruction::{AccountMeta, Instruction};
use solana_system_interface::instruction::create_account_allow_prefund;
#[path = "../../instruction-extensions-common/allocator.rs"]
mod allocator;
#[path = "../../instruction-extensions-common/record.rs"]
mod record;
#[global_allocator]
static ALLOCATOR: allocator::ObservedAllocator = allocator::ObservedAllocator;

const META_NEW: &str = "solana_instruction::account_meta::AccountMeta::new";
const META_READONLY: &str = "solana_instruction::account_meta::AccountMeta::new_readonly";
const META_CLONE: &str =
    "<solana_instruction::account_meta::AccountMeta as core::clone::Clone>::clone";
const INSTRUCTION_CLONE: &str = "<solana_instruction::Instruction as core::clone::Clone>::clone";
const SYSTEM_FUNCTION: &str = "solana_system_interface::instruction::create_account_allow_prefund";

fn main() {
    conformance_recorder::init();
    if record::child() {
        return;
    }
    let mut corpus = conformance_recorder::Corpus::new(
        "instruction_extensions_wincode",
        &[
            ("solana-instruction", "3.4.0"),
            ("solana-system-interface", "3.2.0"),
        ],
    );
    record::record_metadata(&mut corpus);
    record::record_clone(&mut corpus);
    record::record_system(&mut corpus);
    corpus.write(&conformance_recorder::out_dir()).unwrap();
}
