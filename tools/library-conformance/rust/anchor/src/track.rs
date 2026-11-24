//! A global allocator that logs the addresses allocated and freed while
//! tracking is on. Native String and Box identities are their addresses: the
//! log tells a resource allocated during a call (fresh) from an input one, and
//! whether an input resource was freed. Every case runs in its own forked
//! child (`shim::case`), so the log is per case.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

pub struct Tracking;

const CAP: usize = 4096;
static ON: AtomicBool = AtomicBool::new(false);
static ALLOCS: [AtomicUsize; CAP] = [const { AtomicUsize::new(0) }; CAP];
static FREES: [AtomicUsize; CAP] = [const { AtomicUsize::new(0) }; CAP];
static N_ALLOCS: AtomicUsize = AtomicUsize::new(0);
static N_FREES: AtomicUsize = AtomicUsize::new(0);
/// Allocations and frees in call order (address, allocation?).
static EVENTS: [AtomicUsize; CAP] = [const { AtomicUsize::new(0) }; CAP];
static KINDS: [AtomicBool; CAP] = [const { AtomicBool::new(false) }; CAP];
static N_EVENTS: AtomicUsize = AtomicUsize::new(0);

fn event(addr: usize, alloc: bool) {
    let i = N_EVENTS.fetch_add(1, Ordering::SeqCst);
    assert!(i < CAP, "allocation log overflow");
    EVENTS[i].store(addr, Ordering::SeqCst);
    KINDS[i].store(alloc, Ordering::SeqCst);
}

fn push(log: &[AtomicUsize; CAP], n: &AtomicUsize, addr: usize) {
    let i = n.fetch_add(1, Ordering::SeqCst);
    assert!(i < CAP, "allocation log overflow");
    log[i].store(addr, Ordering::SeqCst);
}

unsafe impl GlobalAlloc for Tracking {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let p = System.alloc(layout);
        if ON.load(Ordering::SeqCst) {
            push(&ALLOCS, &N_ALLOCS, p as usize);
            event(p as usize, true);
        }
        p
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if ON.load(Ordering::SeqCst) {
            push(&FREES, &N_FREES, ptr as usize);
            event(ptr as usize, false);
        }
        System.dealloc(ptr, layout)
    }
}

/// Run `f` (driver bookkeeping, such as callback logs) untracked.
pub fn untracked<R>(f: impl FnOnce() -> R) -> R {
    let was = ON.swap(false, Ordering::SeqCst);
    let r = f();
    ON.store(was, Ordering::SeqCst);
    r
}

/// Addresses allocated and freed during one tracked call.
#[derive(Default, Clone)]
pub struct Log {
    pub allocs: Vec<usize>,
    pub frees: Vec<usize>,
    /// Allocations made during the call and still live after it, in call order.
    pub fresh_live: Vec<usize>,
}

pub fn start() {
    N_ALLOCS.store(0, Ordering::SeqCst);
    N_FREES.store(0, Ordering::SeqCst);
    N_EVENTS.store(0, Ordering::SeqCst);
    ON.store(true, Ordering::SeqCst);
}

pub fn stop() -> Log {
    ON.store(false, Ordering::SeqCst);
    let read = |log: &[AtomicUsize; CAP], n: &AtomicUsize| {
        (0..n.load(Ordering::SeqCst)).map(|i| log[i].load(Ordering::SeqCst)).collect()
    };
    let mut live: Vec<usize> = vec![];
    for i in 0..N_EVENTS.load(Ordering::SeqCst) {
        let a = EVENTS[i].load(Ordering::SeqCst);
        if KINDS[i].load(Ordering::SeqCst) {
            live.push(a);
        } else if let Some(j) = live.iter().position(|x| *x == a) {
            live.remove(j);
        }
    }
    Log { allocs: read(&ALLOCS, &N_ALLOCS), frees: read(&FREES, &N_FREES), fresh_live: live }
}

/// Run `f` with tracking on; tracking stops on unwind too. The copy of a
/// panic reason produced by `catch` is not one of the call allocations.
pub fn tracked<R>(f: impl FnOnce() -> R) -> (Result<R, String>, Log) {
    // A first panic initializes per-thread panic state lazily (one allocation
    // that lives on); warm it up outside the tracked call.
    let _ = conformance_recorder::catch(|| panic!("warm-up {}", 0));
    // The installed panic hook (provided by the shim) keeps the last panic text: its
    // allocations belong to the harness, not to the call.
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| untracked(|| hook(info))));
    start();
    let r = conformance_recorder::catch(f);
    let mut log = stop();
    if let Err(reason) = &r {
        if reason.capacity() > 0 {
            let a = reason.as_ptr() as usize;
            if let Some(j) = log.fresh_live.iter().position(|x| *x == a) {
                log.fresh_live.remove(j);
            }
        }
    }
    (r, log)
}
