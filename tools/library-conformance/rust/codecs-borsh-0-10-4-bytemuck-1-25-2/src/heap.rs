//! A global allocator that logs heap requests while a call is tracked: every
//! `alloc`, `alloc_zeroed`, `realloc` and `dealloc` with its size and alignment
//! (and the new realloc size), in call order. Blocks are numbered in allocation
//! order within the call; a realloc keeps its block number even when the
//! address moves; a request on memory allocated before the call has no block.
//! Addresses are never recorded, so the log does not depend on address-space
//! randomisation. The allocator itself never allocates: the log lives in
//! fixed static arrays, and an overflow fails the recording after the call.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};

use conformance_recorder::Json;

pub struct Tracking;

const EVENTS: usize = 256;
const BLOCKS: usize = 256;
const NO_BLOCK: usize = usize::MAX;

const ALLOC: usize = 0;
const ALLOC_ZEROED: usize = 1;
const REALLOC: usize = 2;
const DEALLOC: usize = 3;

static ON: AtomicBool = AtomicBool::new(false);
static OVERFLOW: AtomicBool = AtomicBool::new(false);
static N_EVENTS: AtomicUsize = AtomicUsize::new(0);
static OP: [AtomicUsize; EVENTS] = [const { AtomicUsize::new(0) }; EVENTS];
static BLOCK: [AtomicUsize; EVENTS] = [const { AtomicUsize::new(0) }; EVENTS];
static SIZE: [AtomicUsize; EVENTS] = [const { AtomicUsize::new(0) }; EVENTS];
static ALIGN: [AtomicUsize; EVENTS] = [const { AtomicUsize::new(0) }; EVENTS];
static NEW_SIZE: [AtomicUsize; EVENTS] = [const { AtomicUsize::new(0) }; EVENTS];
/// Current address of each block allocated during the call (0 once freed).
static N_BLOCKS: AtomicUsize = AtomicUsize::new(0);
static ADDRESS: [AtomicUsize; BLOCKS] = [const { AtomicUsize::new(0) }; BLOCKS];

fn log(op: usize, block: usize, layout: Layout, new_size: usize) {
    let i = N_EVENTS.fetch_add(1, SeqCst);
    if i >= EVENTS {
        OVERFLOW.store(true, SeqCst);
        return;
    }
    OP[i].store(op, SeqCst);
    BLOCK[i].store(block, SeqCst);
    SIZE[i].store(layout.size(), SeqCst);
    ALIGN[i].store(layout.align(), SeqCst);
    NEW_SIZE[i].store(new_size, SeqCst);
}

fn new_block(address: *mut u8) -> usize {
    let id = N_BLOCKS.fetch_add(1, SeqCst);
    if id >= BLOCKS {
        OVERFLOW.store(true, SeqCst);
        return NO_BLOCK;
    }
    ADDRESS[id].store(address as usize, SeqCst);
    id
}

fn find_block(address: *mut u8) -> usize {
    let n = N_BLOCKS.load(SeqCst).min(BLOCKS);
    (0..n).find(|&i| ADDRESS[i].load(SeqCst) == address as usize).unwrap_or(NO_BLOCK)
}

unsafe impl GlobalAlloc for Tracking {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(layout) };
        if ON.load(SeqCst) && !p.is_null() {
            log(ALLOC, new_block(p), layout, 0);
        }
        p
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { System.alloc_zeroed(layout) };
        if ON.load(SeqCst) && !p.is_null() {
            log(ALLOC_ZEROED, new_block(p), layout, 0);
        }
        p
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let q = unsafe { System.realloc(ptr, layout, new_size) };
        if ON.load(SeqCst) {
            let block = find_block(ptr);
            if block != NO_BLOCK && !q.is_null() {
                ADDRESS[block].store(q as usize, SeqCst);
            }
            log(REALLOC, block, layout, new_size);
        }
        q
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if ON.load(SeqCst) {
            let block = find_block(ptr);
            if block != NO_BLOCK {
                ADDRESS[block].store(0, SeqCst);
            }
            log(DEALLOC, block, layout, 0);
        }
        unsafe { System.dealloc(ptr, layout) }
    }
}

/// One logged heap request.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Event {
    pub op: &'static str,
    /// Allocation order within the call; `None` for memory allocated before it.
    pub block: Option<usize>,
    pub size: usize,
    pub align: usize,
    /// The requested size of a `realloc`.
    pub new_size: Option<usize>,
}

impl Event {
    /// `{"op", "block", "size", "align"}`, and `"new_size"` for a `realloc`.
    pub fn to_json(&self) -> Json {
        let mut fields = vec![
            ("op".to_string(), Json::from(self.op)),
            ("block".to_string(), self.block.map_or(Json::Null, Json::from)),
            ("size".to_string(), Json::from(self.size)),
            ("align".to_string(), Json::from(self.align)),
        ];
        if let Some(n) = self.new_size {
            fields.push(("new_size".to_string(), Json::from(n)));
        }
        Json::Obj(fields)
    }
}

pub fn events_json(events: &[Event]) -> Json {
    Json::arr(events.iter(), Event::to_json)
}

/// Run `f` with tracking on and return its result with the heap requests it
/// made. The result is returned, not dropped, so its destructor is not part of
/// the log.
pub fn tracked<R>(f: impl FnOnce() -> R) -> (R, Vec<Event>) {
    N_EVENTS.store(0, SeqCst);
    N_BLOCKS.store(0, SeqCst);
    OVERFLOW.store(false, SeqCst);
    ON.store(true, SeqCst);
    let r = f();
    ON.store(false, SeqCst);
    assert!(!OVERFLOW.load(SeqCst), "heap log overflow");
    let events = (0..N_EVENTS.load(SeqCst))
        .map(|i| {
            let op = match OP[i].load(SeqCst) {
                ALLOC => "alloc",
                ALLOC_ZEROED => "alloc_zeroed",
                REALLOC => "realloc",
                _ => "dealloc",
            };
            let block = BLOCK[i].load(SeqCst);
            Event {
                op,
                block: (block != NO_BLOCK).then_some(block),
                size: SIZE[i].load(SeqCst),
                align: ALIGN[i].load(SeqCst),
                new_size: (op == "realloc").then(|| NEW_SIZE[i].load(SeqCst)),
            }
        })
        .collect();
    (r, events)
}
