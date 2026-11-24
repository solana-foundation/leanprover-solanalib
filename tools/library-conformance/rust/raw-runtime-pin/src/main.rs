//! The published defining crate supplies each declaration used here.
use conformance_raw_runtime_common::{Calls, record};
use pinocchio::syscalls as s;

unsafe fn clock(a: *mut u8) -> u64 { unsafe { s::sol_get_clock_sysvar(a) } }

fn main() {
    record("raw_runtime_pinocchio_0_9_2", "pinocchio", "0.9.2",
        "pinocchio::syscalls", Calls {
            clock: Some(clock),
            ..Calls::default()
        });
}
