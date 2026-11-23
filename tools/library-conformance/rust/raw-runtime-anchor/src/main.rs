//! The published defining crate supplies each declaration used here.
use conformance_raw_runtime_common::{Calls, record};
use anchor_lang::solana_program::instruction as s;

unsafe fn anchor_stack() -> u64 { unsafe { s::get_stack_height() as u64 } }

fn main() {
    record("raw_runtime_anchor_lang_1_0_2", "anchor-lang", "1.0.2",
        "anchor_lang::solana_program::instruction", Calls {
            stack: Some(anchor_stack),
            stack_wrapper: true,
            ..Calls::default()
        });
}
