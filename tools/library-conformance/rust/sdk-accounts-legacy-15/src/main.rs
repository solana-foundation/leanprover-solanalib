// Exact pinned SDK identity; shared fixtures contain no implementation substitutions.
use solana_program::{account_info::AccountInfo, entrypoint::deserialize, program_error::ProgramError, pubkey::Pubkey};
#[allow(dead_code)]
#[path = "../../accounts-v1/src/region.rs"]
mod region;
const CORPUS: &str = "sdk_accounts_1_15_2";
const TYPE_PATH: &str = "solana_program::account_info::AccountInfo";
const METHODS: &[&str] = &["assign", "clone", "data_len", "lamports", "realloc", "try_borrow_data", "try_borrow_mut_data", "try_borrow_mut_lamports", "try_data_len"];
const CRATES: &[(&str, &str)] = &[("solana-program", "1.15.2")];
include!("../../sdk-accounts-common/main.rs");
fn main() { run(); }
