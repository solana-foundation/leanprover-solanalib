const PACKAGE: &str = "spl-token-2022-interface";
const VERSION: &str = "2.1.0";
const RUST_CRATE: &str = "spl_token_2022_interface";
const CORPUS: &str = "token_state_interface_2_1_0";
const LEGACY: bool = true;
const REQUIRE_TLV: bool = false;
const UNPACK: bool = true;
const CLONE: bool = false;
#[path = "../../common/token_state_versions_alloc.rs"]
mod allocation;
#[path = "../../common/token_state_versions.rs"]
mod cases;
#[path = "../../common/token_extension_reference_alloc.rs"]
mod reference_allocation;
#[global_allocator]
static ALLOCATOR: reference_allocation::Observed = reference_allocation::Observed;
fn main() { reference_allocation::check_sdk(); cases::main(); }
