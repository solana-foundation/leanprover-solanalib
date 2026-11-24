#[allow(dead_code)]
#[path = "../../runtime-common/rent_cases.rs"]
mod rent_cases;
#[allow(dead_code)]
#[path = "../../runtime-common/syscall_cases.rs"]
mod syscall_cases;
#[allow(dead_code)]
#[path = "../../anchor/src/track.rs"]
mod track;
#[path = "../../utility-common/instructions.rs"]
mod instructions;
#[global_allocator]
static ALLOC: track::Tracking = track::Tracking;
use solana_account_info::AccountInfo;
use solana_instruction::Instruction;
use solana_pubkey::Pubkey;
use solana_instructions_sysvar as instructions_sysvar;
fn main() {
    use conformance_recorder::{self as rec, Corpus};
    rec::init();
    let mut corpus = Corpus::new("utility_instructions4", &[("solana-instructions-sysvar", "4.0.0")]);
    instructions::record(&mut corpus);
    corpus.write(&rec::out_dir()).expect("write checked-loader corpus");
}
