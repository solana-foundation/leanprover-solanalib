//! The published defining crate supplies each declaration used here.
use conformance_raw_runtime_common::{Calls, record};
use solana_program::syscalls as s;

unsafe fn copy(a: *mut u8, b: *const u8, n: u64) { unsafe { s::sol_memcpy_(a, b, n) } }
unsafe fn set(a: *mut u8, b: u8, n: u64) { unsafe { s::sol_memset_(a, b, n) } }
unsafe fn create(a: *const u8, n: u64, p: *const u8, r: *mut u8) -> u64 { unsafe { s::sol_create_program_address(a, n, p, r) } }
unsafe fn find(a: *const u8, n: u64, p: *const u8, r: *mut u8, b: *mut u8) -> u64 { unsafe { s::sol_try_find_program_address(a, n, p, r, b) } }
unsafe fn hash(a: *const u8, n: u64, r: *mut u8) -> u64 { unsafe { s::sol_sha256(a, n, r) } }
unsafe fn clock(a: *mut u8) -> u64 { unsafe { s::sol_get_clock_sysvar(a) } }
unsafe fn rent(a: *mut u8) -> u64 { unsafe { s::sol_get_rent_sysvar(a) } }

fn main() {
    record("raw_runtime_solana_program_1_18_26", "solana-program", "1.18.26",
        "solana_program::syscalls::definitions", Calls {
            copy: Some(copy),
            set: Some(set),
            create: Some(create),
            find: Some(find),
            hash: Some(hash),
            clock: Some(clock),
            rent: Some(rent),
            ..Calls::default()
        });
}
