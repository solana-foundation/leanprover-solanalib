//! Allocation observations for native state/extension calls. Recording excludes
//! JSON construction and fixture setup. Allocation-failure controls fork before
//! enabling the one-shot failure, so an expected abort cannot skip a parent check.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

pub struct Counter;
static ALLOC: AtomicUsize = AtomicUsize::new(0);
static FREE: AtomicUsize = AtomicUsize::new(0);
static GROW: AtomicUsize = AtomicUsize::new(0);
static FAIL: AtomicBool = AtomicBool::new(false);

unsafe impl GlobalAlloc for Counter {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOC.fetch_add(1, Ordering::SeqCst);
        if FAIL.swap(false, Ordering::SeqCst) { return std::ptr::null_mut(); }
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        ALLOC.fetch_add(1, Ordering::SeqCst);
        if FAIL.swap(false, Ordering::SeqCst) { return std::ptr::null_mut(); }
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        FREE.fetch_add(1, Ordering::SeqCst);
        unsafe { System.dealloc(pointer, layout) }
    }
    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        GROW.fetch_add(1, Ordering::SeqCst);
        if FAIL.swap(false, Ordering::SeqCst) { return std::ptr::null_mut(); }
        unsafe { System.realloc(pointer, layout, size) }
    }
}

pub fn counted<R>(call: impl FnOnce() -> R) -> (R, [usize; 3]) {
    let start = [ALLOC.load(Ordering::SeqCst), FREE.load(Ordering::SeqCst), GROW.load(Ordering::SeqCst)];
    let result = call();
    let end = [ALLOC.load(Ordering::SeqCst), FREE.load(Ordering::SeqCst), GROW.load(Ordering::SeqCst)];
    (result, [end[0] - start[0], end[1] - start[1], end[2] - start[2]])
}

#[cfg(test)]
unsafe extern "C" { fn fork() -> i32; fn waitpid(pid: i32, status: *mut i32, flags: i32) -> i32; fn _exit(code: i32) -> !; }

/// The child returns 42 only if the call returned instead of hitting its
/// allocation abort. No fallthrough path is accepted by the parent.
#[cfg(test)]
pub fn aborts_on_next_allocation(call: impl FnOnce()) -> bool {
    let pid = unsafe { fork() };
    assert!(pid >= 0, "fork failed");
    if pid == 0 {
        FAIL.store(true, Ordering::SeqCst);
        call();
        FAIL.store(false, Ordering::SeqCst);
        unsafe { _exit(42) }
    }
    let mut status = 0;
    assert_eq!(unsafe { waitpid(pid, &mut status, 0) }, pid);
    allocation_outcome(status)
}

#[cfg(test)]
fn allocation_outcome(status: i32) -> bool {
    let signal = status & 0x7f;
    if signal == 6 { return true; }
    assert_eq!(signal, 0, "child terminated by unexpected signal: {status:#x}");
    assert_eq!((status >> 8) & 0xff, 42, "child returned unexpectedly: {status:#x}");
    false
}

#[cfg(test)]
mod tests {
    use super::allocation_outcome;

    #[test]
    fn distinguishes_return_from_expected_abort() {
        assert!(!allocation_outcome(42 << 8));
        assert!(allocation_outcome(6));
        assert!(allocation_outcome(6 | 0x80));
    }

    #[test]
    #[should_panic(expected = "unexpected signal")]
    fn rejects_unexpected_signal() { allocation_outcome(11); }

    #[test]
    #[should_panic(expected = "returned unexpectedly")]
    fn rejects_unexpected_exit() { allocation_outcome(0); }
}
