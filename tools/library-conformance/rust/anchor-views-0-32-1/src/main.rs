mod identities;
#[path = "../../anchor-views-cases.rs"]
mod cases;
const CORPUS: &str = "anchor_views_0_32_1";
const VERSION: &str = "0.32.1";
const DEBUG: bool = cfg!(feature = "debug");
fn main() { cases::run(); }
