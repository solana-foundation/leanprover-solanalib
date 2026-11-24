const CORPUS: &str = "cpi_raw_program_1_15_2";
const PROFILE: &str = "solana-program-1.15.2";
const CRATES: &[(&str, &str)] = &[("solana-program", "1.15.2")];
const FUNCTION: &str = "solana_program::syscalls::definitions::sol_invoke_signed_rust";
#[cfg(feature = "signature-check")]
fn source_signature() {
    let _: unsafe extern "C" fn(*const u8, *const u8, u64, *const u8, u64) -> u64 = solana_program::syscalls::sol_invoke_signed_rust;
}
include!("../../common/cpi_raw_mocks.rs");
