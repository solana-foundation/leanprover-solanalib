use solana_account_info::AccountInfo;
use solana_instruction::{Instruction, AccountMeta};
use solana_program_error::ProgramError;
const CORPUS: &str = "cpi_invoke_0_5_0_s3_0_1";
const PROFILE: &str = "solana-invoke-0.5.0-s3.0.1";
const CRATES: &[(&str, &str)] = &[("solana-invoke", "0.5.0")];
const SIGNED: &str = "solana_invoke::invoke_signed";
const UNSIGNED: &str = "solana_invoke::invoke";

// Type checking only; native recording leaves this feature disabled.
#[cfg(feature = "signature-check")]
fn source_signatures() {
    let _: fn(&Instruction, &[AccountInfo<'_>]) -> Result<(), ProgramError> = solana_invoke::invoke;
    let _: fn(&Instruction, &[AccountInfo<'_>], &[&[&[u8]]]) -> Result<(), ProgramError> = solana_invoke::invoke_signed;
}
macro_rules! new_account { ($key:expr, $lamports:expr, $data:expr, $owner:expr) => {
    AccountInfo::new($key, false, false, $lamports, $data, $owner, true)
}; }
#[allow(deprecated)]
fn rent_offset() -> usize { std::mem::offset_of!(AccountInfo<'_>, _unused) }

fn constructor_control(_: &Instruction) -> conformance_recorder::Json {
    // The private borrowed preparation and invocation implementations stay opaque.
    conformance_recorder::Json::Null
}
include!("../../common/cpi_signature_mocks.rs");
