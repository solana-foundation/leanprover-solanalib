//! Encoders shared by the token-interface recordings, and an allocation
//! counter.
//!
//! The counter is the global allocator for this binary: it forwards to `System`
//! and counts fresh allocations and deallocations made while a measured call
//! runs. `realloc` (growth of an existing vector) is neither. The instruction
//! constructor models execute their vector operations over a ledger in which
//! each `Vec::with_capacity` or literal `vec![..]` is one fresh slot and a drop
//! retires one; the counts are compared with that ledger.

use conformance_recorder::{bytes, err, ok, variant, Json};
use solana_program_error::ProgramError;
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct Counting;

static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static DEALLOCATIONS: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Ordering::SeqCst);
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Ordering::SeqCst);
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        DEALLOCATIONS.fetch_add(1, Ordering::SeqCst);
        unsafe { System.dealloc(ptr, layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

/// Run `f` and count the fresh allocations and deallocations it performs.
/// The driver is single-threaded, so the global counters see only `f`.
pub fn counted<R>(f: impl FnOnce() -> R) -> (R, usize, usize) {
    let a0 = ALLOCATIONS.load(Ordering::SeqCst);
    let d0 = DEALLOCATIONS.load(Ordering::SeqCst);
    let r = f();
    let a1 = ALLOCATIONS.load(Ordering::SeqCst);
    let d1 = DEALLOCATIONS.load(Ordering::SeqCst);
    (r, a1 - a0, d1 - d0)
}

/// The heap observation recorded as the state after a constructor call.
pub fn heap(allocations: usize, deallocations: usize) -> Json {
    Json::obj([("allocations", allocations.into()), ("deallocations", deallocations.into())])
}

/// A 32-byte key.
pub fn key(k: &[u8]) -> Json {
    assert_eq!(k.len(), 32);
    bytes(k)
}

/// `ProgramError` as `{"variant": name, "fields": []}`, or with the code for
/// `Custom`. Every variant of solana-program-error 2.2.2 is listed, so a new
/// variant is a compile error rather than a silent mis-encoding.
pub fn program_error(e: &ProgramError) -> Json {
    use ProgramError::*;
    let name = match e {
        Custom(code) => return variant("Custom", vec![Json::from(*code)]),
        InvalidArgument => "InvalidArgument",
        InvalidInstructionData => "InvalidInstructionData",
        InvalidAccountData => "InvalidAccountData",
        AccountDataTooSmall => "AccountDataTooSmall",
        InsufficientFunds => "InsufficientFunds",
        IncorrectProgramId => "IncorrectProgramId",
        MissingRequiredSignature => "MissingRequiredSignature",
        AccountAlreadyInitialized => "AccountAlreadyInitialized",
        UninitializedAccount => "UninitializedAccount",
        NotEnoughAccountKeys => "NotEnoughAccountKeys",
        AccountBorrowFailed => "AccountBorrowFailed",
        MaxSeedLengthExceeded => "MaxSeedLengthExceeded",
        InvalidSeeds => "InvalidSeeds",
        BorshIoError(_) => "BorshIoError",
        AccountNotRentExempt => "AccountNotRentExempt",
        UnsupportedSysvar => "UnsupportedSysvar",
        IllegalOwner => "IllegalOwner",
        MaxAccountsDataAllocationsExceeded => "MaxAccountsDataAllocationsExceeded",
        InvalidRealloc => "InvalidRealloc",
        MaxInstructionTraceLengthExceeded => "MaxInstructionTraceLengthExceeded",
        BuiltinProgramsMustConsumeComputeUnits => "BuiltinProgramsMustConsumeComputeUnits",
        InvalidAccountOwner => "InvalidAccountOwner",
        ArithmeticOverflow => "ArithmeticOverflow",
        Immutable => "Immutable",
        IncorrectAuthority => "IncorrectAuthority",
    };
    variant(name, vec![])
}

pub fn result<T>(r: &Result<T, ProgramError>, f: impl Fn(&T) -> Json) -> Json {
    match r {
        Ok(v) => ok(f(v)),
        Err(e) => err(program_error(e)),
    }
}

/// An optional value: `null` or `{"some": v}`.
pub fn opt<T>(v: Option<T>, f: impl Fn(T) -> Json) -> Json {
    match v {
        None => Json::Null,
        Some(x) => Json::obj([("some", f(x))]),
    }
}

/// Deterministic distinct keys: the seed in the first and last byte, zeros
/// between (zero runs keep the corpus compact).
pub fn k(seed: u8) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[0] = seed;
    b[31] = seed.wrapping_mul(31).wrapping_add(7);
    b
}
