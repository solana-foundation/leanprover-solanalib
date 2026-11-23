use solana_program::{account_info::AccountInfo, instruction::{Instruction, AccountMeta}, program_error::ProgramError};
const CORPUS: &str = "cpi_program_1_15_2";
const PROFILE: &str = "solana-program-1.15.2";
const CRATES: &[(&str, &str)] = &[("solana-program", "1.15.2")];
const SIGNED: &str = "solana_program::program::invoke_signed";
const UNSIGNED: &str = "solana_program::program::invoke";

// Compile-check only. Native recording never enables this feature or obtains
// an SDK invocation function pointer.
#[cfg(feature = "signature-check")]
fn source_signatures() {
    let _: fn(&Instruction, &[AccountInfo<'_>]) -> Result<(), ProgramError> = solana_program::program::invoke;
    let _: fn(&Instruction, &[AccountInfo<'_>], &[&[&[u8]]]) -> Result<(), ProgramError> = solana_program::program::invoke_signed;
}
macro_rules! new_account { ($key:expr, $lamports:expr, $data:expr, $owner:expr) => {
    AccountInfo::new($key, false, false, $lamports, $data, $owner, true, 0)
}; }
fn rent_offset() -> usize { std::mem::offset_of!(AccountInfo<'_>, rent_epoch) }

fn constructor_control(_: &Instruction) -> conformance_recorder::Json {
    // The private borrowed preparation and invocation implementations stay opaque.
    conformance_recorder::Json::Null
}
include!("../../common/cpi_signature_mocks.rs");
