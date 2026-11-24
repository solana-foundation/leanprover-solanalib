#[path = "../../sdk-values-common/support.rs"]
mod support;
#[path = "../../sdk-values-common/options.rs"]
mod options;
pub use solana_program::program_option::COption;
const PREFIX: &str = "solana_program::program_option";
const VERSION: &str = "1.15.2";
const PACKAGE: &str = "solana-program";
const OPTION_CORPUS: &str = "sdk_values_solana_program_1_15_2";
fn main() {
    conformance_recorder::init();
    options::record(&["contains", "is_none", "unwrap_or_default"]);
}
