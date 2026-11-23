#[path = "../../sdk-values-common/support.rs"]
mod support;
#[path = "../../sdk-values-common/options.rs"]
mod options;
#[path = "../../sdk-values-common/numeric.rs"]
mod numeric;
pub use solana_program_option::COption;
const PREFIX: &str = "solana_program_option";
const VERSION: &str = "2.2.1";
const PACKAGE: &str = "solana-program-option";
const OPTION_CORPUS: &str = "sdk_values_solana_program_option_2_2_1";
fn main() {
    conformance_recorder::init();
    options::record(&["as_ref", "is_none", "map", "unwrap_or"]);
    numeric::record_zero("1.0.1", "sdk_values_solana_zero_copy_1_0_1");
    numeric::record_pod();
}
