#[path = "../../sdk-values-common/support.rs"]
mod support;
#[path = "../../sdk-values-common/options.rs"]
mod options;
#[path = "../../sdk-values-common/numeric.rs"]
mod numeric;
#[path = "../../sdk-values-common/modern.rs"]
mod modern;
pub use solana_program_option::COption;
const PREFIX: &str = "solana_program_option";
const VERSION: &str = "3.1.0";
const PACKAGE: &str = "solana-program-option";
const OPTION_CORPUS: &str = "sdk_values_solana_program_option_3_1_0";
fn main() {
    conformance_recorder::init();
    options::record(&["eq", "unwrap"]);
    numeric::record_zero("1.1.1", "sdk_values_solana_zero_copy_1_1_1");
    modern::record();
}
