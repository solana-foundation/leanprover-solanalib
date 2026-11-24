//! Projected-wrapper conformance; see projection.json and the family README.
mod projected;
#[path = "../../common/anchor_system.rs"]
mod driver;
#[path = "../../anchor/src/track.rs"]
mod track;
#[global_allocator]
static GLOBAL: track::Tracking = track::Tracking;
const VERSION: &str = "0.27.0";
const CORPUS: &str = "anchor_system_0_27_0";
pub mod solana_program {
    pub use anchor_lang::solana_program::system_instruction;
    pub mod program { pub use crate::driver::invoke_signed; }
}
fn main() { driver::main(); }
