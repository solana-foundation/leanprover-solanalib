use solana_program::{account_info::AccountInfo, instruction::{Instruction, AccountMeta}, program_error::ProgramError};
const CORPUS: &str = "cpi_program_2_3_0";
const PROFILE: &str = "solana-program-2.3.0";
const CRATES: &[(&str, &str)] = &[("solana-program", "2.3.0")];
const SIGNED: &str = "solana_program::program::invoke_signed";
const UNSIGNED: &str = "solana_program::program::invoke";

// Type checking only; native recording leaves this feature disabled.
#[cfg(feature = "signature-check")]
fn source_signatures() {
    let _: fn(&Instruction, &[AccountInfo<'_>]) -> Result<(), ProgramError> = solana_program::program::invoke;
    let _: fn(&Instruction, &[AccountInfo<'_>], &[&[&[u8]]]) -> Result<(), ProgramError> = solana_program::program::invoke_signed;
}
macro_rules! new_account { ($key:expr, $lamports:expr, $data:expr, $owner:expr) => {
    AccountInfo::new($key, false, false, $lamports, $data, $owner, true, 0)
}; }
fn rent_offset() -> usize { std::mem::offset_of!(AccountInfo<'_>, rent_epoch) }

// Ordinary public constructor control, outside the mocked invocation. This
// never calls the invocation implementation or attributes this run to it.
fn constructor_control(instruction: &Instruction) -> conformance_recorder::Json {
    use solana_program::stable_layout::stable_instruction::StableInstruction;
    let before = instruction_json(instruction).to_text();
    let stable = StableInstruction::from(instruction.clone());
    let same_value = stable.program_id == instruction.program_id
        && stable.accounts[..] == instruction.accounts[..]
        && stable.data[..] == instruction.data[..];
    let fresh_accounts = instruction.accounts.is_empty()
        || stable.accounts.as_ptr() != instruction.accounts.as_ptr();
    let fresh_data = instruction.data.is_empty()
        || stable.data.as_ptr() != instruction.data.as_ptr();
    drop(stable);
    conformance_recorder::Json::obj([
        ("kind", "owned-stable-constructor".into()),
        ("same_value", same_value.into()),
        ("fresh_accounts", fresh_accounts.into()),
        ("fresh_data", fresh_data.into()),
        ("input_retained_after_drop", (before == instruction_json(instruction).to_text()).into()),
    ])
}
include!("../../common/cpi_signature_mocks.rs");
