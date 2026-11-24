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
const VERSION: &str = "1.1.2";
const CORPUS: &str = "anchor_spl_token_1_1_2";
fn main() {
    if std::env::args().nth(1).as_deref() == Some("--build-config") {
        println!("{{\"scope\":\"projected-wrapper\",\"panic\":\"{}\",\"debug_assertions\":{},\"solana_cfg\":{},\"pointer_width\":{},\"little_endian\":{},\"signature_check_enabled\":{}}}",
            if cfg!(panic = "unwind") { "unwind" } else { "abort" },
            cfg!(debug_assertions), cfg!(target_os = "solana"), usize::BITS,
            cfg!(target_endian = "little"), cfg!(feature = "signature-check"));
        return;
    }
    driver::main();
}
