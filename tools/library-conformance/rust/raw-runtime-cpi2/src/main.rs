//! The published defining crate supplies each declaration used here.
use conformance_raw_runtime_common::{Calls, record};
use solana_cpi::syscalls as s;

unsafe fn get_return(a: *mut u8, n: u64, p: *mut u8) -> u64 { unsafe { s::sol_get_return_data(a, n, p.cast()) } }

fn main() {
    record("raw_runtime_solana_cpi_2_2_1", "solana-cpi", "2.2.1",
        "solana_cpi::syscalls", Calls {
            get_return: Some(get_return),
            ..Calls::default()
        });
}
