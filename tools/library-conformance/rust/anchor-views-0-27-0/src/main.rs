mod identities;
#[path = "../../anchor-views-cases.rs"]
mod cases;
const CORPUS: &str = "anchor_views_0_27_0";
const VERSION: &str = "0.27.0";
const DEBUG: bool = cfg!(feature = "debug");
fn main() { cases::run(); }
