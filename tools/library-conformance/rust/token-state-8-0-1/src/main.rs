const PACKAGE: &str = "spl-token-2022";
const VERSION: &str = "8.0.1";
const RUST_CRATE: &str = "spl_token_2022";
const CORPUS: &str = "token_state_8_0_1";
const LEGACY: bool = true;
const REQUIRE_TLV: bool = true;
const UNPACK: bool = true;
const CLONE: bool = false;
#[path = "../../common/token_state_versions_alloc.rs"]
mod allocation;
#[path = "../../common/token_state_versions.rs"]
mod cases;
#[global_allocator]
static ALLOCATOR: allocation::Counter = allocation::Counter;
fn main() { cases::main(); }
