//! Exact version profile for generic instruction construction and cloning.
use solana_program::{
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
    system_instruction::create_account_with_seed,
};
#[path = "../../instruction-extensions-common/allocator.rs"]
mod allocator;
#[path = "../../instruction-extensions-common/record.rs"]
mod record;
#[global_allocator]
static ALLOCATOR: allocator::ObservedAllocator = allocator::ObservedAllocator;

const META_NEW: &str = "solana_program::instruction::AccountMeta::new";
const META_READONLY: &str = "solana_program::instruction::AccountMeta::new_readonly";
const META_CLONE: &str = "<solana_program::instruction::AccountMeta as core::clone::Clone>::clone";
const INSTRUCTION_CLONE: &str =
    "<solana_program::instruction::Instruction as core::clone::Clone>::clone";
const SYSTEM_FUNCTION: &str = "solana_program::system_instruction::create_account_with_seed";

fn main() {
    conformance_recorder::init();
    if record::child() {
        return;
    }
    let mut corpus = conformance_recorder::Corpus::new(
        "instruction_extensions_legacy_15",
        &[("solana-program", "1.15.2")],
    );

    record::record_clone(&mut corpus);
    record::record_system(&mut corpus);
    corpus.write(&conformance_recorder::out_dir()).unwrap();
}
