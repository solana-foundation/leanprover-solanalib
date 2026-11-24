//! Immutable source projection: only complete invocation/getter signatures are replaced.
extern crate anchor_lang as actual_anchor_lang;
pub mod anchor_lang {
    pub use actual_anchor_lang::*;
    pub mod solana_program {
        pub use actual_anchor_lang::solana_program::*;
        pub mod program { pub use crate::driver::{invoke, invoke_signed, get_return_data}; }
    }
}
pub mod solana_program { pub use crate::anchor_lang::solana_program::*; }
mod projected;
mod cases;
#[path = "../../common/anchor_spl_token.rs"] mod driver;
#[path = "../../common/anchor_spl_token_track.rs"] mod track;
#[global_allocator] static GLOBAL: track::Tracking = track::Tracking;
const VERSION: &str = "0.29.0";
const CORPUS: &str = "anchor_spl_token_0_29_0";
fn main() { driver::main(); }
