const CORPUS: &str = "cpi_raw_define_2_3_0";
const PROFILE: &str = "solana-define-syscall-2.3.0";
const CRATES: &[(&str, &str)] = &[("solana-define-syscall", "2.3.0")];
const FUNCTION: &str = "solana_define_syscall::definitions::sol_invoke_signed_rust";
#[cfg(feature = "signature-check")]
fn source_signature() {
    let _: unsafe extern "C" fn(*const u8, *const u8, u64, *const u8, u64) -> u64 = solana_define_syscall::definitions::sol_invoke_signed_rust;
}
include!("../../common/cpi_raw_mocks.rs");
