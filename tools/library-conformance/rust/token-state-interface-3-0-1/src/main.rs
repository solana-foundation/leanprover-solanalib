const PACKAGE: &str = "spl-token-2022-interface";
const VERSION: &str = "3.0.1";
const RUST_CRATE: &str = "spl_token_2022_interface";
const CORPUS: &str = "token_state_interface_3_0_1";
const LEGACY: bool = false;
const REQUIRE_TLV: bool = false;
const UNPACK: bool = true;
const CLONE: bool = false;
#[path = "../../common/token_state_versions_alloc.rs"]
mod allocation;
#[path = "../../common/token_state_versions.rs"]
mod cases;
#[global_allocator]
static ALLOCATOR: allocation::Counter = allocation::Counter;
fn main() { cases::main(); }
