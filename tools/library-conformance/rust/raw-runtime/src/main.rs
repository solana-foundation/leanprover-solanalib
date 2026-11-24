//! The published defining crate supplies each declaration used here.
use conformance_raw_runtime_common::{Calls, record};
use solana_define_syscall::definitions as s;

unsafe fn copy(a: *mut u8, b: *const u8, n: u64) { unsafe { s::sol_memcpy_(a, b, n) } }
unsafe fn set(a: *mut u8, b: u8, n: u64) { unsafe { s::sol_memset_(a, b, n) } }
unsafe fn create(a: *const u8, n: u64, p: *const u8, r: *mut u8) -> u64 { unsafe { s::sol_create_program_address(a, n, p, r) } }
unsafe fn find(a: *const u8, n: u64, p: *const u8, r: *mut u8, b: *mut u8) -> u64 { unsafe { s::sol_try_find_program_address(a, n, p, r, b) } }
unsafe fn hash(a: *const u8, n: u64, r: *mut u8) -> u64 { unsafe { s::sol_sha256(a, n, r) } }
unsafe fn clock(a: *mut u8) -> u64 { unsafe { s::sol_get_clock_sysvar(a) } }
unsafe fn rent(a: *mut u8) -> u64 { unsafe { s::sol_get_rent_sysvar(a) } }
unsafe fn epoch(a: *mut u8) -> u64 { unsafe { s::sol_get_epoch_schedule_sysvar(a) } }
unsafe fn stack() -> u64 { unsafe { s::sol_get_stack_height() } }
unsafe fn set_return(a: *const u8, n: u64) { unsafe { s::sol_set_return_data(a, n) } }
unsafe fn get_return(a: *mut u8, n: u64, p: *mut u8) -> u64 { unsafe { s::sol_get_return_data(a, n, p.cast()) } }

fn main() {
    record("raw_runtime_solana_define_syscall_5_1_0", "solana-define-syscall", "5.1.0",
        "solana_define_syscall::definitions", Calls {
            copy: Some(copy),
            set: Some(set),
            create: Some(create),
            find: Some(find),
            hash: Some(hash),
            clock: Some(clock),
            rent: Some(rent),
            epoch: Some(epoch),
            stack: Some(stack),
            set_return: Some(set_return),
            get_return: Some(get_return),
            ..Calls::default()
        });
}
