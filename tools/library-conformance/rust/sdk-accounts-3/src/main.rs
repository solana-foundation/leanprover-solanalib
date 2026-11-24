// Exact pinned SDK identity; shared fixtures contain no implementation substitutions.
use solana_account_info::AccountInfo;
use solana_program_entrypoint::deserialize;
use solana_program_error::ProgramError;
use solana_address::Address as Pubkey;
#[allow(dead_code)]
#[path = "../../accounts-v1/src/region.rs"]
mod region;
const CORPUS: &str = "sdk_accounts_3_1_1";
const TYPE_PATH: &str = "solana_account_info::AccountInfo";
const METHODS: &[&str] = &["as_ref", "assign", "data_is_empty", "resize", "try_borrow_lamports", "try_borrow_mut_lamports", "try_data_len"];
const CRATES: &[(&str, &str)] = &[("solana-account-info", "3.1.1")];
include!("../../sdk-accounts-common/main.rs");
fn main() { run(); }
