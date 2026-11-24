//! Native calls to the exact Anchor 0.32.1 SDK.
#[path = "../../anchor-loader-shared/enc.rs"] mod enc;
#[path = "../../anchor-account-world/world.rs"] mod world;
#[path = "../../anchor-loader-shared/script.rs"] mod script;
#[path = "../../anchor-loader-shared/cases.rs"] mod cases;

fn main() {
    conformance_recorder::init();
    let mut corpus = conformance_recorder::Corpus::new("anchor_loader_0_32_1", &[("anchor-lang", "0.32.1")]);
    cases::record(&mut corpus, false);
    corpus.write(&conformance_recorder::out_dir()).expect("write loader corpus");
}

// Observe successful diagnostic allocations and their cleanup before guard release.
// The ordinary recorder binary is unchanged: this module is compiled only by cargo test.
#[cfg(test)]
mod write_zero_effects {
    use anchor_lang::__private::BpfWriter;
    use anchor_lang::prelude::*;
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::cell::{Cell, RefCell};
    use std::io::Write;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    #[derive(Clone, Copy, Debug)]
    struct Stats {
        active: bool,
        target: usize,
        allocations: usize,
        deallocations: usize,
        first: [usize; 3],
        allocated_held: u8,
        freed: u8,
        freed_held: u8,
        diagnostic_reallocated: bool,
    }

    impl Stats {
        const fn empty() -> Self {
            Self { active: false, target: 0, allocations: 0, deallocations: 0,
                first: [0; 3], allocated_held: 0, freed: 0, freed_held: 0,
                diagnostic_reallocated: false }
        }
    }

    thread_local! {
        // A const, non-dropping Cell does not allocate during allocator observation.
        static STATS: Cell<Stats> = const { Cell::new(Stats::empty()) };
    }

    // The Tracking value keeps this exact RefCell alive while active. This read
    // examines only its borrow flag; a held exclusive guard makes try_borrow fail.
    unsafe fn exclusive_guard_held(target: usize) -> bool {
        let cell = unsafe { &*(target as *const RefCell<&mut [u8]>) };
        cell.try_borrow().is_err()
    }

    fn allocated(ptr: *mut u8) {
        if ptr.is_null() { return; }
        let _ = STATS.try_with(|cell| {
            let mut stats = cell.get();
            if !stats.active { return; }
            let index = stats.allocations;
            stats.allocations = stats.allocations.saturating_add(1);
            if index < 3 {
                stats.first[index] = ptr as usize;
                if unsafe { exclusive_guard_held(stats.target) } {
                    stats.allocated_held |= 1 << index;
                }
            }
            cell.set(stats);
        });
    }

    fn deallocated(ptr: *mut u8) {
        let _ = STATS.try_with(|cell| {
            let mut stats = cell.get();
            if !stats.active { return; }
            stats.deallocations = stats.deallocations.saturating_add(1);
            for index in 0..3 {
                let bit = 1 << index;
                if stats.first[index] == ptr as usize && stats.freed & bit == 0 {
                    stats.freed |= bit;
                    if unsafe { exclusive_guard_held(stats.target) } {
                        stats.freed_held |= bit;
                    }
                }
            }
            cell.set(stats);
        });
    }

    fn reallocated(ptr: *mut u8) {
        let _ = STATS.try_with(|cell| {
            let mut stats = cell.get();
            if !stats.active { return; }
            for index in 0..3 {
                if stats.first[index] == ptr as usize && stats.freed & (1 << index) == 0 {
                    stats.diagnostic_reallocated = true;
                }
            }
            cell.set(stats);
        });
    }

    struct ObservingSystem;
    unsafe impl GlobalAlloc for ObservingSystem {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let ptr = unsafe { System.alloc(layout) };
            allocated(ptr);
            ptr
        }
        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            let ptr = unsafe { System.alloc_zeroed(layout) };
            allocated(ptr);
            ptr
        }
        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            deallocated(ptr);
            unsafe { System.dealloc(ptr, layout) };
        }
        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
            reallocated(ptr);
            unsafe { System.realloc(ptr, layout, size) }
        }
    }

    #[global_allocator]
    static ALLOCATOR: ObservingSystem = ObservingSystem;

    // Drop turns observation off even if an unexpected panic bypasses finish.
    // No raw target address is retained after the borrowed RefCell can expire.
    struct Tracking<'cell, 'data> { _target: &'cell RefCell<&'data mut [u8]> }
    impl Tracking<'_, '_> {
        fn finish(self) -> Stats {
            let result = STATS.with(|cell| {
                let result = cell.get();
                cell.set(Stats::empty());
                result
            });
            drop(self);
            result
        }
    }
    impl Drop for Tracking<'_, '_> {
        fn drop(&mut self) { let _ = STATS.try_with(|cell| cell.set(Stats::empty())); }
    }
    fn begin<'cell, 'data>(target: &'cell RefCell<&'data mut [u8]>) -> Tracking<'cell, 'data> {
        STATS.with(|cell| {
            assert!(!cell.get().active, "nested allocation probe");
            cell.set(Stats { active: true, target: target as *const _ as usize, ..Stats::empty() });
        });
        Tracking { _target: target }
    }

    fn assert_diagnostic_lifetime(stats: Stats) {
        assert!(stats.allocations >= 3, "three diagnostic allocations must have completed: {stats:?}");
        assert_eq!(stats.allocated_held, 0b111, "diagnostic allocations precede guard release");
        assert_eq!(stats.freed, 0b111, "the same three allocation identities were freed");
        assert_eq!(stats.freed_held, 0b111, "diagnostic frees precede guard release");
        assert!(!stats.diagnostic_reallocated, "unexpected diagnostic reallocation");
    }

    #[test]
    fn short_writer_constructs_and_drops_diagnostic_while_guard_is_held() {
        let mut data = [];
        let cell = RefCell::new(&mut data[..]);
        let mut held = cell.borrow_mut();
        let tracking = begin(&cell);
        // Empty storage reaches WriteZero without the recorder memcpy shim.
        let result = BpfWriter::new(&mut **held).write_all(&[1]);
        let kind = result.as_ref().err().map(std::io::Error::kind);
        drop(result);
        let stats = tracking.finish();
        assert_eq!(kind, Some(std::io::ErrorKind::WriteZero));
        assert_eq!(stats.allocations, 3);
        assert_eq!(stats.deallocations, 3);
        assert_diagnostic_lifetime(stats);
        assert!(cell.try_borrow().is_err());
        drop(held);
        assert!(cell.try_borrow_mut().is_ok());
        eprintln!("write_zero_direct allocations={} deallocations={} allocated_held={} freed_held={}",
            stats.allocations, stats.deallocations, stats.allocated_held, stats.freed_held);
    }

    #[derive(Clone, Copy)]
    #[repr(C)]
    struct QuietZc { value: u64 }
    unsafe impl anchor_lang::__private::bytemuck::Zeroable for QuietZc {}
    unsafe impl anchor_lang::__private::bytemuck::Pod for QuietZc {}
    impl Discriminator for QuietZc { const DISCRIMINATOR: &'static [u8] = &[1]; }
    impl anchor_lang::ZeroCopy for QuietZc {}
    impl Owner for QuietZc {
        fn owner() -> Pubkey { Pubkey::new_from_array([0x77; 32]) }
    }

    #[test]
    fn loader_exit_drops_diagnostic_before_releasing_guard() {
        let key = Pubkey::new_from_array([1; 32]);
        let owner = QuietZc::owner();
        let mut lamports = 40;
        let mut data = [];
        let info = AccountInfo::new(&key, false, true, &mut lamports, &mut data, &owner, false, 0);
        let loader = AccountLoader::<QuietZc>::try_from_unchecked(&owner, &info).unwrap();
        // Suppress hook output before recording; formatting inside unwrap is
        // still real. Quiet Owner and empty storage avoid scripted log allocations.
        let previous_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let tracking = begin(info.data.as_ref());
        let result = catch_unwind(AssertUnwindSafe(|| loader.exit(&owner)));
        let stats = tracking.finish();
        std::panic::set_hook(previous_hook);
        assert!(result.is_err(), "the nonclosed empty account must reach short write unwrap");
        assert_diagnostic_lifetime(stats);
        assert!(info.try_borrow_mut_data().is_ok(), "caller guard releases after diagnostic cleanup");
        eprintln!("write_zero_exit allocations={} deallocations={} allocated_held={} freed_held={}",
            stats.allocations, stats.deallocations, stats.allocated_held, stats.freed_held);
        // The caught panic payload is caller-owned and dropped outside observation.
        drop(result);
    }
}
