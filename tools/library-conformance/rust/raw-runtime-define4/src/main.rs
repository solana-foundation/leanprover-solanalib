//! The published defining crate supplies each declaration used here.
use conformance_raw_runtime_common::{Calls, record};
use solana_define_syscall::definitions as s;

unsafe fn copy(a: *mut u8, b: *const u8, n: u64) { unsafe { s::sol_memcpy_(a, b, n) } }
unsafe fn set(a: *mut u8, b: u8, n: u64) { unsafe { s::sol_memset_(a, b, n) } }
unsafe fn epoch(a: *mut u8) -> u64 { unsafe { s::sol_get_epoch_schedule_sysvar(a) } }
unsafe fn set_return(a: *const u8, n: u64) { unsafe { s::sol_set_return_data(a, n) } }

fn main() {
    record("raw_runtime_solana_define_syscall_4_0_1", "solana-define-syscall", "4.0.1",
        "solana_define_syscall::definitions", Calls {
            copy: Some(copy),
            set: Some(set),
            epoch: Some(epoch),
            set_return: Some(set_return),
            ..Calls::default()
        });
}
