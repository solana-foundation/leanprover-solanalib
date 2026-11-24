//! Layout and occurrence controls for the old sizing temporary. This wrapper
//! delegates to the existing counting/failure allocator. Its probe initializes
//! spare bytes before inspecting them, so an incorrect element count or layout
//! is a failed observation rather than an uninitialized read in the control.
use std::alloc::{GlobalAlloc, Layout};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};
use token_api::extension::ExtensionType;
use token_api::state::{Account, Mint};

pub struct Observed;
static ACTIVE: AtomicBool = AtomicBool::new(false);
static READ: AtomicUsize = AtomicUsize::new(0);
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static FREES: AtomicUsize = AtomicUsize::new(0);
static GROWS: AtomicUsize = AtomicUsize::new(0);
static SIZE: AtomicUsize = AtomicUsize::new(0);
static ALIGN: AtomicUsize = AtomicUsize::new(0);
static SLOTS: [AtomicUsize; 8] = [const { AtomicUsize::new(0) }; 8];

unsafe impl GlobalAlloc for Observed {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { crate::allocation::Counter.alloc(layout) };
        if ACTIVE.load(SeqCst) {
            ALLOCS.fetch_add(1, SeqCst);
            if !pointer.is_null() { unsafe { pointer.write_bytes(0xff, layout.size()) }; }
        }
        pointer
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { crate::allocation::Counter.alloc_zeroed(layout) };
        if ACTIVE.load(SeqCst) { ALLOCS.fetch_add(1, SeqCst); }
        pointer
    }
    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let next = unsafe { crate::allocation::Counter.realloc(pointer, layout, size) };
        if ACTIVE.load(SeqCst) {
            GROWS.fetch_add(1, SeqCst);
            if !next.is_null() && size > layout.size() {
                unsafe { next.add(layout.size()).write_bytes(0xff, size - layout.size()) };
            }
        }
        next
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        if ACTIVE.load(SeqCst) {
            FREES.fetch_add(1, SeqCst);
            SIZE.store(layout.size(), SeqCst);
            ALIGN.store(layout.align(), SeqCst);
            let count = READ.load(SeqCst);
            if layout.align() == 8 && layout.size() >= count * 8 {
                for (index, slot) in SLOTS.iter().enumerate().take(count) {
                    // All bytes were initialized by the wrapper above; only
                    // numeric pointer bits are read, never dereferenced here.
                    slot.store(unsafe { pointer.add(index * 8).cast::<usize>().read() }, SeqCst);
                }
            }
        }
        unsafe { crate::allocation::Counter.dealloc(pointer, layout) };
    }
}

#[derive(Clone, Copy, Debug)]
struct Trace { allocs: usize, frees: usize, grows: usize, size: usize, align: usize, slots: [usize; 8] }

fn probe<R>(count: usize, call: impl FnOnce() -> R) -> (R, Trace) {
    assert!(count <= 8);
    assert!(!ACTIVE.load(SeqCst));
    READ.store(count, SeqCst);
    for counter in [&ALLOCS, &FREES, &GROWS, &SIZE, &ALIGN] { counter.store(0, SeqCst); }
    for slot in &SLOTS { slot.store(0, SeqCst); }
    ACTIVE.store(true, SeqCst);
    let result = call();
    ACTIVE.store(false, SeqCst);
    (result, Trace { allocs: ALLOCS.load(SeqCst), frees: FREES.load(SeqCst),
        grows: GROWS.load(SeqCst), size: SIZE.load(SeqCst), align: ALIGN.load(SeqCst),
        slots: std::array::from_fn(|i| SLOTS[i].load(SeqCst)) })
}

fn accepts(trace: Trace, source: &[ExtensionType], first: &[usize], capacity: usize, grows: usize) -> bool {
    if first.is_empty() { return trace.allocs == 0 && trace.frees == 0 && trace.grows == 0; }
    trace.allocs == 1 && trace.frees == 1 && trace.grows == grows &&
        trace.size == capacity * 8 && trace.align == 8 &&
        first.iter().enumerate().all(|(slot, index)|
            source.get(*index).is_some_and(|value| trace.slots[slot] == value as *const _ as usize))
}

/// These assertions run in each fresh native recording, in addition to the
/// normal scalar corpus. They do not replace or patch either SDK body.
pub fn check_sdk() {
    use ExtensionType::*;
    assert_eq!(std::mem::size_of::<ExtensionType>(), 2);
    assert_eq!(std::mem::size_of::<&ExtensionType>(), 8);
    assert_eq!(std::mem::align_of::<&ExtensionType>(), 8);
    assert_eq!(Vec::<&ExtensionType>::new().as_ptr() as usize, 8);
    let empty = [];
    let (result, trace) = probe(0, || ExtensionType::try_calculate_account_len::<Mint>(&empty));
    assert_eq!(result, Ok(82));
    assert!(accepts(trace, &empty, &[], 0, 0), "empty sizing allocated: {trace:?}");
    let (result, trace) = probe(0, || ExtensionType::try_calculate_account_len::<Account>(&empty));
    assert_eq!(result, Ok(165));
    assert!(accepts(trace, &empty, &[], 0, 0), "empty account sizing allocated: {trace:?}");
    let duplicates = [ImmutableOwner, TransferFeeConfig, ImmutableOwner, TransferHook, TransferFeeConfig];
    let (result, trace) = probe(3, || ExtensionType::try_calculate_account_len::<Mint>(&duplicates));
    assert_eq!(result, Ok(350));
    assert!(accepts(trace, &duplicates, &[0, 1, 3], 4, 0), "wrong first-occurrence references: {trace:?}");
    let (result, trace) = probe(3, || ExtensionType::try_calculate_account_len::<Account>(&duplicates));
    assert_eq!(result, Ok(350));
    assert!(accepts(trace, &duplicates, &[0, 1, 3], 4, 0), "wrong account first-occurrence references: {trace:?}");
    let variable = [TokenMetadata, ImmutableOwner, TokenMetadata];
    let (result, trace) = probe(2, || ExtensionType::try_calculate_account_len::<Mint>(&variable));
    assert_eq!(result, Err(solana_program_error::ProgramError::InvalidArgument));
    assert!(accepts(trace, &variable, &[0, 1], 4, 0), "error skipped full reference construction/drop: {trace:?}");
    let growing = [ImmutableOwner, TransferFeeConfig, TransferHook, MintCloseAuthority,
        PermanentDelegate, NonTransferable];
    let (result, trace) = probe(6, || ExtensionType::try_calculate_account_len::<Mint>(&growing));
    assert_eq!(result, Ok(426));
    assert!(accepts(trace, &growing, &[0, 1, 2, 3, 4, 5], 8, 1), "reference reallocation lost occurrences: {trace:?}");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_sdk_reference_layout_and_occurrences() { check_sdk(); }

    #[test]
    fn rejects_actual_value_vector_substitute() {
        let source = [ExtensionType::ImmutableOwner];
        let (_, trace) = probe(1, || {
            let mut values = Vec::new();
            values.push(std::hint::black_box(source[0]));
            std::hint::black_box(&values);
        });
        assert!(!accepts(trace, &source, &[0], 4, 0));
        assert_eq!((trace.size, trace.align), (8, 2));
    }

    #[test]
    fn rejects_equal_value_at_later_occurrence() {
        let source = [ExtensionType::ImmutableOwner, ExtensionType::ImmutableOwner];
        let (_, trace) = probe(1, || {
            let mut references = Vec::new();
            references.push(std::hint::black_box(&source[1]));
            std::hint::black_box(&references);
        });
        assert!(!accepts(trace, &source, &[0], 4, 0));
        assert!(accepts(trace, &source, &[1], 4, 0));
    }

    #[test]
    fn rejects_skipped_temporary_cleanup() {
        let source = [ExtensionType::ImmutableOwner];
        let (live, trace) = probe(1, || {
            let mut references = Vec::new();
            references.push(std::hint::black_box(&source[0]));
            references
        });
        assert!(!accepts(trace, &source, &[0], 4, 0));
        assert_eq!(trace.frees, 0);
        drop(live);
    }
}
