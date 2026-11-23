//! Allocation observations for the native codec fixtures. The hook itself
//! allocates nothing; each measured operation runs synchronously on this thread.
use conformance_recorder::Json;
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};

const LIMIT: usize = 128;
static ENABLED: AtomicBool = AtomicBool::new(false);
static COUNT: AtomicUsize = AtomicUsize::new(0);
static EVENTS: [[AtomicUsize; 4]; LIMIT] =
    [const { [const { AtomicUsize::new(0) }; 4] }; LIMIT];

pub struct Traced;
#[global_allocator]
static ALLOCATOR: Traced = Traced;

fn event(kind: usize, layout: Layout, new_size: usize) {
    if ENABLED.load(SeqCst) {
        let index = COUNT.fetch_add(1, SeqCst);
        if index < LIMIT {
            for (cell, value) in EVENTS[index].iter().zip([kind, layout.size(), layout.align(), new_size]) {
                cell.store(value, SeqCst);
            }
        }
    }
}

unsafe impl GlobalAlloc for Traced {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc(layout) };
        event(0, layout, 0);
        pointer
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc_zeroed(layout) };
        event(1, layout, 0);
        pointer
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        event(2, layout, 0);
        unsafe { System.dealloc(pointer, layout) };
    }
    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let result = unsafe { System.realloc(pointer, layout, new_size) };
        event(3, layout, new_size);
        result
    }
}

pub fn measure<T>(operation: impl FnOnce() -> T) -> (T, Vec<String>) {
    assert!(!ENABLED.load(SeqCst), "nested allocation measurement");
    COUNT.store(0, SeqCst);
    ENABLED.store(true, SeqCst);
    let result = std::hint::black_box(operation());
    ENABLED.store(false, SeqCst);
    let count = COUNT.load(SeqCst);
    assert!(count <= LIMIT, "allocation trace capacity exceeded");
    let trace = EVENTS[..count].iter().map(|row| {
        let [kind, size, align, new_size] = row.each_ref().map(|cell| cell.load(SeqCst));
        let name = ["alloc", "zeroed", "dealloc", "realloc"][kind];
        format!("{name}:{size}:{align}:{new_size}")
    }).collect();
    (result, trace)
}

pub fn json(trace: &[String]) -> Json { Json::arr(trace.iter(), |s| s.as_str().into()) }
