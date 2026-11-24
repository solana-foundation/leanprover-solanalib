//! Regression against the published, pinned Borsh 0.10.4 implementation.
//! From the repository root, first resolve and record the driver with
//! `just test-native-library codecs-borsh-0-10-4-bytemuck-1-25-2 EVIDENCE`.
//! Then run `cargo test --locked --release --test cautious_truncation` in the
//! driver directory; EVIDENCE must name a fresh evidence directory.
//! No value of the huge element type is ever constructed. Optimization avoids
//! reserving its unused return slot on the stack in the generic decoder.

#![cfg(target_pointer_width = "64")]

use borsh::{maybestd::io, BorshDeserialize};
use std::alloc::{GlobalAlloc, Layout, System};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};

const HUGE: usize = 1usize << 32;
static ELEMENT_CALLS: AtomicUsize = AtomicUsize::new(0);
static LARGE_ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);

// Observe vector-sized requests without changing allocation behavior or
// suppressing the small allocations made by panic/error construction.
struct ObserveLargeAllocations;

#[global_allocator]
static ALLOCATOR: ObserveLargeAllocations = ObserveLargeAllocations;

unsafe impl GlobalAlloc for ObserveLargeAllocations {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if layout.size() >= HUGE {
            LARGE_ALLOCATIONS.fetch_add(1, SeqCst);
        }
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if layout.size() >= HUGE {
            LARGE_ALLOCATIONS.fetch_add(1, SeqCst);
        }
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        if size >= HUGE {
            LARGE_ALLOCATIONS.fetch_add(1, SeqCst);
        }
        unsafe { System.realloc(ptr, layout, size) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[allow(dead_code)]
struct Huge([u8; HUGE]);

impl BorshDeserialize for Huge {
    fn deserialize_reader<R: io::Read>(_reader: &mut R) -> io::Result<Self> {
        ELEMENT_CALLS.fetch_add(1, SeqCst);
        panic!("element callback reached")
    }
}

fn panic_text(value: &(dyn std::any::Any + Send)) -> &str {
    if let Some(text) = value.downcast_ref::<&str>() {
        text
    } else if let Some(text) = value.downcast_ref::<String>() {
        text
    } else {
        "non-string panic"
    }
}

#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "run --release to avoid unused huge return slots"
)]
fn truncated_size_panics_after_length_before_allocation_or_element() {
    assert_eq!(Layout::new::<Huge>().size(), HUGE);
    assert_eq!(Layout::new::<Huge>().align(), 1);
    assert!(HUGE <= isize::MAX as usize);

    for length in [1u32, 2, u32::MAX] {
        let mut bytes = length.to_le_bytes().to_vec();
        bytes.push(99);
        let mut input = bytes.as_slice();
        let result = catch_unwind(AssertUnwindSafe(|| {
            Vec::<Huge>::deserialize_reader(&mut input)
        }));
        let Err(reason) = result else {
            panic!("expected the division-by-zero panic")
        };
        assert!(panic_text(reason.as_ref()).contains("divide by zero"));
        assert_eq!(input, &[99]);
        assert_eq!(ELEMENT_CALLS.load(SeqCst), 0);
        assert_eq!(LARGE_ALLOCATIONS.load(SeqCst), 0);
    }

    // A zero length returns before evaluating the hint.
    let mut empty: &[u8] = &[0, 0, 0, 0, 99];
    assert!(Vec::<Huge>::deserialize_reader(&mut empty)
        .unwrap()
        .is_empty());
    assert_eq!(empty, &[99]);

    // An incomplete header errors before evaluating the hint.
    let mut short: &[u8] = &[1, 0, 0];
    let Err(error) = Vec::<Huge>::deserialize_reader(&mut short) else {
        panic!("expected short input")
    };
    assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
    assert_eq!(error.to_string(), "Unexpected length of input");
    assert!(short.is_empty());

    // The original zero-size rejection precedes even the length read.
    let mut zero_sized: &[u8] = &[1, 0, 0, 0, 99];
    let error = Vec::<()>::deserialize_reader(&mut zero_sized).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
    assert_eq!(error.to_string(), "Vectors of zero-sized types are not allowed due to deny-of-service concerns on deserialization.");
    assert_eq!(zero_sized, &[1, 0, 0, 0, 99]);

    // u8 keeps its specialized reader path.
    let mut bytes: &[u8] = &[2, 0, 0, 0, 7, 8, 9];
    assert_eq!(Vec::<u8>::deserialize_reader(&mut bytes).unwrap(), [7, 8]);
    assert_eq!(bytes, &[9]);
    assert_eq!(ELEMENT_CALLS.load(SeqCst), 0);
    assert_eq!(LARGE_ALLOCATIONS.load(SeqCst), 0);
}
