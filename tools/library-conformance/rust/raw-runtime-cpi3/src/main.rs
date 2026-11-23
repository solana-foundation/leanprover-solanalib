//! The published defining crate supplies each declaration used here.
use conformance_raw_runtime_common::{Calls, record};
use solana_cpi as s;

unsafe fn sdk_set_return(a: *const u8, n: u64) { unsafe { s::set_return_data(core::slice::from_raw_parts(a, n as usize)) } }

fn main() {
    record("raw_runtime_solana_cpi_3_1_0", "solana-cpi", "3.1.0",
        "solana_cpi", Calls {
            set_return: Some(sdk_set_return),
            setter_slice: true,
            ..Calls::default()
        });
}
