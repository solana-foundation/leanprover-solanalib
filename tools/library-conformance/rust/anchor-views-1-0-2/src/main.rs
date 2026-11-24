mod identities;
#[path = "../../anchor-views-cases.rs"]
mod cases;
const CORPUS: &str = "anchor_views_1_0_2";
const VERSION: &str = "1.0.2";
const DEBUG: bool = cfg!(feature = "debug");
fn main() { cases::run(); }
