//! Local allocation observer. No shared recorder/shim behavior is changed.
//!
//! A selected allocation returns null in an isolated child; the unmodified
//! standard allocation error handler aborts. The parent requires SIGABRT and
//! this allocator marker. Allocation/deallocation never unwind.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};

pub struct ObservedAllocator;
static ACTIVE: AtomicBool = AtomicBool::new(false);
static COUNT: AtomicUsize = AtomicUsize::new(0);
static FAIL_AT: AtomicUsize = AtomicUsize::new(0);

unsafe extern "C" {
    fn write(fd: i32, bytes: *const u8, len: usize) -> isize;
}

fn reject() -> bool {
    if !ACTIVE.load(SeqCst) {
        return false;
    }
    let ordinal = COUNT.fetch_add(1, SeqCst) + 1;
    if ordinal != FAIL_AT.load(SeqCst) {
        return false;
    }
    let marker = b"instruction-extensions-allocation-failure\n";
    unsafe {
        write(2, marker.as_ptr(), marker.len());
    }
    true
}

unsafe impl GlobalAlloc for ObservedAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if reject() {
            std::ptr::null_mut()
        } else {
            System.alloc(layout)
        }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if reject() {
            std::ptr::null_mut()
        } else {
            System.alloc_zeroed(layout)
        }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        if reject() {
            std::ptr::null_mut()
        } else {
            System.realloc(ptr, layout, size)
        }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }
}

pub fn measure<T>(fail_at: usize, call: impl FnOnce() -> T) -> (T, usize) {
    COUNT.store(0, SeqCst);
    FAIL_AT.store(fail_at, SeqCst);
    ACTIVE.store(true, SeqCst);
    let result = std::hint::black_box(call());
    ACTIVE.store(false, SeqCst);
    (result, COUNT.load(SeqCst))
}
