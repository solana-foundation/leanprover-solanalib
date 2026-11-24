//! Exact SDK calls on independently serialized, aligned input buffers.
//! The allocator observes allocation sizes and the first original-length word without
//! allocating while active. Failure cases return null from GlobalAlloc in a forked child;
//! the parent requires SIGABRT, so an accidental return or unrelated fault is rejected.

use conformance_accounts::{Account, Entry, Input, Region};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use core::mem::MaybeUninit;
use std::alloc::{GlobalAlloc, Layout, System};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};

const SDK: &str = "solana_program_entrypoint_2_3_0_deserialize";
const PIN: &str = "pinocchio_0_9_2_deserialize";
const SDK_FN: &str = "solana_program_entrypoint::deserialize";
const PIN_FN: &str = "pinocchio::entrypoint::deserialize";

static ACTIVE: AtomicBool = AtomicBool::new(false);
static CALLS: AtomicUsize = AtomicUsize::new(0);
static FAIL_AT: AtomicUsize = AtomicUsize::new(usize::MAX);
static INPUT: AtomicUsize = AtomicUsize::new(0);
static SIZES: [AtomicUsize; 1024] = [const { AtomicUsize::new(0) }; 1024];
static ALIGNS: [AtomicUsize; 1024] = [const { AtomicUsize::new(0) }; 1024];
static ORIGINALS: [AtomicUsize; 1024] = [const { AtomicUsize::new(0) }; 1024];

struct RecorderAllocator;

unsafe impl GlobalAlloc for RecorderAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if ACTIVE.load(SeqCst) {
            let i = CALLS.fetch_add(1, SeqCst);
            if i < SIZES.len() {
                SIZES[i].store(layout.size(), SeqCst);
                ALIGNS[i].store(layout.align(), SeqCst);
                // Enabled only for a nonempty, loader-backed fixture. Reading these raw
                // bytes does not manufacture a Rust reference to the input buffer.
                let input = INPUT.load(SeqCst) as *const u8;
                let mut b = [0u8; 4];
                for (j, byte) in b.iter_mut().enumerate() {
                    *byte = input.add(12 + j).read();
                }
                ORIGINALS[i].store(u32::from_le_bytes(b) as usize, SeqCst);
            }
            if i == FAIL_AT.load(SeqCst) {
                return core::ptr::null_mut();
            }
        }
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }
}

#[global_allocator]
static ALLOCATOR: RecorderAllocator = RecorderAllocator;

fn begin(input: *mut u8, fail_at: Option<usize>) {
    CALLS.store(0, SeqCst);
    INPUT.store(input as usize, SeqCst);
    FAIL_AT.store(fail_at.unwrap_or(usize::MAX), SeqCst);
    ACTIVE.store(true, SeqCst);
}

fn end() -> Json {
    ACTIVE.store(false, SeqCst);
    let n = CALLS.load(SeqCst);
    assert!(n <= SIZES.len(), "allocator trace overflow");
    Json::arr(0..n, |i| Json::obj([
        ("size", SIZES[i].load(SeqCst).into()),
        ("align", ALIGNS[i].load(SeqCst).into()),
        ("first_original_length", ORIGINALS[i].load(SeqCst).into()),
    ]))
}

fn account(i: usize, length: usize) -> Account {
    Account {
        // Deliberately equal keys for distinct unique records.
        key: [7; 32],
        owner: [8 + i as u8; 32],
        lamports: if i % 2 == 0 { u64::MAX } else { 42 },
        data: (0..length).map(|j| (10 + j) as u8).collect(),
        is_signer: true,
        is_writable: i % 2 == 0,
        executable: i % 2 != 0,
        rent_epoch: if i % 2 == 0 { 19 } else { u64::MAX },
    }
}

fn fixture(count: usize, length: usize, unique: bool) -> Input {
    let entries = (0..count).map(|i| {
        if i == 0 || unique || i == 2 {
            Entry::Account(account(i, if i == 0 { length } else { i % 9 }))
        } else if i == 1 {
            Entry::Duplicate(0)
        } else {
            Entry::Duplicate(1) // duplicate of a duplicate, retaining the original storage.
        }
    }).collect();
    Input { entries, instruction_data: vec![0, 255, 3, 7, 11], program_id: [99; 32] }
}

fn prepare(input: &Input) -> Region {
    let mut region = input.serialize();
    for (i, entry) in input.entries.iter().enumerate() {
        let offset = region.account_offset(i);
        unsafe {
            let at = region.as_mut_ptr().add(offset);
            match entry {
                Entry::Account(account) => {
                    // Every nonzero flag is true; no bool is read directly from these bytes.
                    at.add(1).write(2);
                    at.add(2).write(if account.is_writable { 7 } else { 0 });
                    at.add(3).write(if account.executable { 9 } else { 0 });
                    let spare = at.add(88 + account.data.len());
                    for j in 0..8 { spare.add(j).write(0xa0 + j as u8); }
                    spare.add(10239).write(0xee);
                    let padding = (8 - account.data.len() % 8) % 8;
                    for j in 0..padding { spare.add(10240 + j).write(0x80 + j as u8); }
                }
                Entry::Duplicate(_) => {
                    for j in 1..8 { at.add(j).write(j as u8); }
                }
            }
        }
    }
    region
}

fn state(region: &Region, outputs: Json) -> Json {
    Json::obj([
        ("input", region.read_back()),
        ("bytes", rec::bytes(region.bytes())),
        ("outputs", outputs),
    ])
}

fn views(program: &[u8], data: &[u8], base: usize) -> Json {
    Json::obj([
        ("program_offset", (program.as_ptr() as usize - base).into()),
        ("program_id", rec::bytes(program)),
        ("instruction_offset", (data.as_ptr() as usize - base).into()),
        ("instruction_data", rec::bytes(data)),
    ])
}

fn intern(pointers: &mut Vec<usize>, pointer: usize) -> usize {
    if let Some(index) = pointers.iter().position(|p| *p == pointer) { return index; }
    let index = pointers.len();
    pointers.push(pointer);
    index
}

fn sdk_record(input: &Input, id: &str) -> Record {
    let mut region = prepare(input);
    let before = state(&region, Json::Null);
    let base = region.as_mut_ptr();
    begin(base, None);
    let (program, accounts, data) = unsafe { solana_program_entrypoint::deserialize(base) };
    let allocations = end();
    let mut cells = Vec::new();
    let mut owners = Vec::new();
    let infos = Json::Arr(accounts.iter().map(|info| {
        let lamports = info.lamports.borrow();
        let data = info.data.borrow();
        Json::obj([
            ("header_offset", (info.key.as_ref().as_ptr() as usize - base as usize - 8).into()),
            ("key", rec::bytes(info.key.as_ref())),
            ("owner", rec::bytes(info.owner.as_ref())),
            ("owner_ref", intern(&mut owners, info.owner.as_ref().as_ptr() as usize).into()),
            ("lamports_cell", intern(&mut cells, Rc::as_ptr(&info.lamports) as usize).into()),
            ("data_cell", intern(&mut cells, Rc::as_ptr(&info.data) as usize).into()),
            ("lamports", (**lamports).into()),
            ("data", rec::bytes(&data)),
            ("lamports_offset", (&**lamports as *const u64 as usize - base as usize).into()),
            ("data_offset", (data.as_ptr() as usize - base as usize).into()),
            ("lamports_strong", Rc::strong_count(&info.lamports).into()),
            ("data_strong", Rc::strong_count(&info.data).into()),
            ("rent_epoch", info.rent_epoch.into()),
            ("signer", info.is_signer.into()),
            ("writable", info.is_writable.into()),
            ("executable", info.executable.into()),
        ])
    }).collect());
    let result = Json::obj([
        ("views", views(program.as_ref(), data, base as usize)),
        ("accounts", infos),
        ("capacity", accounts.capacity().into()),
        ("allocations", allocations),
    ]);
    // Input readback occurs after all borrowed values have been observed. Dropping these
    // owners does not write input bytes. Recorded Rc counts describe the return observation.
    drop(accounts);
    let after = state(&region, Json::Null);
    Record { id: id.into(), function: SDK_FN, generics: vec![], layout: None,
        state: before, args: Json::obj([("fail_at", Json::Null)]),
        outcome: rec::returned(result, after), observed: None }
}

extern "C" {
    fn fork() -> i32;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
    fn _exit(status: i32) -> !;
}

fn sdk_failure(input: &Input, fail_at: usize) -> Record {
    let mut region = prepare(input);
    let before = state(&region, Json::Null);
    let pid = unsafe { fork() };
    assert!(pid >= 0, "fork failed");
    if pid == 0 {
        begin(region.as_mut_ptr(), Some(fail_at));
        let _returned = unsafe { solana_program_entrypoint::deserialize(region.as_mut_ptr()) };
        unsafe { _exit(71) }
    }
    let mut status = 0;
    assert_eq!(unsafe { waitpid(pid, &mut status, 0) }, pid, "waitpid failed");
    assert_eq!(status & 0x7f, 6, "allocation failure must terminate with SIGABRT");
    Record { id: format!("allocation_failure/{fail_at}"), function: SDK_FN, generics: vec![],
        layout: None, state: before, args: Json::obj([("fail_at", fail_at.into())]),
        outcome: Json::obj([("exit", "terminated".into()), ("reason", "allocation-failure".into())]),
        observed: None }
}

fn pin_record<const MAX: usize>(input: &Input, id: &str) -> Record {
    assert!(input.entries.is_empty() || MAX > 0);
    let mut region = prepare(input);
    let base = region.as_mut_ptr();
    assert_eq!(core::mem::size_of::<pinocchio::account_info::AccountInfo>(), 8);
    // A fully initialized raw-pointer sentinel makes the untouched output suffix observable.
    // It is never dereferenced. The source receives its actual MaybeUninit array type.
    let sentinel: pinocchio::account_info::AccountInfo = unsafe { core::mem::transmute(base) };
    let mut output = [MaybeUninit::new(sentinel); MAX];
    let before = state(&region, Json::arr(0..MAX, |_| Json::from(0usize)));
    begin(base, None);
    let (program, count, data) = unsafe { pinocchio::entrypoint::deserialize::<MAX>(base, &mut output) };
    let allocations = end();
    assert_eq!(CALLS.load(SeqCst), 0, "Pinocchio deserialize must not allocate");
    let offsets: Vec<usize> = output.iter().map(|slot| {
        let raw: *mut u8 = unsafe { core::mem::transmute(slot.assume_init()) };
        raw as usize - base as usize
    }).collect();
    let infos = Json::arr(0..count, |i| {
        let info = unsafe { output[i].assume_init() };
        let data = info.try_borrow_data().unwrap();
        Json::obj([
            ("header_offset", offsets[i].into()),
            ("key", rec::bytes(info.key())),
            ("owner", rec::bytes(info.owner())),
            ("lamports", info.lamports().into()),
            ("data", rec::bytes(&data)),
            ("data_offset", (data.as_ptr() as usize - base as usize).into()),
            ("signer", info.is_signer().into()),
            ("writable", info.is_writable().into()),
            ("executable", info.executable().into()),
        ])
    });
    let result = Json::obj([
        ("views", views(program, data, base as usize)),
        ("count", count.into()),
        ("accounts", infos),
        ("allocations", allocations),
    ]);
    let after = state(&region, Json::arr(offsets, Json::from));
    Record { id: format!("{id}/capacity_{MAX}"), function: PIN_FN,
        generics: vec![("MAX_ACCOUNTS", MAX.to_string())], layout: None, state: before,
        args: Json::empty(), outcome: rec::returned(result, after), observed: None }
}

fn main() {
    rec::init();
    let out = std::env::args_os().nth(1).expect("corpus output directory");
    let mut sdk = Corpus::new(SDK, &[("solana-program-entrypoint", "2.3.0")]);
    let mut pin = Corpus::new(PIN, &[("pinocchio", "0.9.2")]);
    for (id, count, length, unique) in [
        ("empty", 0, 0, false), ("one_empty", 1, 0, false), ("one_3", 1, 3, false),
        ("one_8", 1, 8, false), ("pair", 2, 7, false), ("aliases", 4, 3, false),
        ("five", 5, 1, false), ("six", 6, 9, false), ("eleven", 11, 8, false),
        ("equal_keys_unique", 7, 2, true), ("maximum", 254, 0, false),
    ] {
        let input = fixture(count, length, unique);
        sdk.push(sdk_record(&input, id));
        pin.push(pin_record::<64>(&input, id));
        if count == 0 { pin.push(pin_record::<0>(&input, id)); }
        if count > 0 {
            pin.push(pin_record::<1>(&input, id));
            pin.push(pin_record::<2>(&input, id));
            pin.push(pin_record::<5>(&input, id));
        }
        if count == 254 { pin.push(pin_record::<254>(&input, id)); }
    }
    // The SDK has no Pinocchio MAX_TX_ACCOUNTS gate.
    sdk.push(sdk_record(&fixture(255, 3, false), "sdk_255"));
    for fail_at in 0..5 { sdk.push(sdk_failure(&fixture(4, 3, false), fail_at)); }
    sdk.write(std::path::Path::new(&out)).unwrap();
    pin.write(std::path::Path::new(&out)).unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_aliasing_and_capacity_edges() {
        let input = fixture(4, 3, false);
        let sdk = sdk_record(&input, "aliases").outcome.to_text();
        assert!(sdk.contains("\"lamports_cell\":0,\"data_cell\":1"));
        assert!(sdk.contains("\"lamports_strong\":3,\"data_strong\":3"));
        let pin = pin_record::<2>(&input, "skip").outcome.to_text();
        assert!(pin.contains("\"count\":2"));
        assert!(pin.contains("\"outputs\":[8,8]"));
    }

    #[test]
    fn nonempty_zero_capacity_is_never_invoked() {
        assert!(rec::catch(|| pin_record::<0>(&fixture(1, 0, false), "invalid")).is_err());
        let empty = pin_record::<0>(&fixture(0, 0, false), "empty").outcome.to_text();
        assert!(empty.contains("\"count\":0"));
    }

    #[test]
    fn allocation_failure_is_terminal() {
        for fail_at in 0..3 {
            let record = sdk_failure(&fixture(4, 3, false), fail_at);
            assert!(record.outcome.to_text().contains("allocation-failure"));
        }
    }
}
