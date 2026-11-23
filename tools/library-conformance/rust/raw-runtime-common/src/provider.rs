//! Native test provider for ordinary C syscall declarations. Its fixed symbolic
//! digest/curve result is a fixture, not cryptography or an Agave implementation.
//! Forked cases preserve terminal exits and reject native faults as harness errors.

use conformance_recorder::{self as rec, Corpus, Json, Record};
use std::cell::RefCell;

#[derive(Clone)]
pub struct Script {
    pub on_curve: bool,
    pub height: u64,
    pub return_program: [u8; 32],
    pub return_data: Vec<u8>,
}
impl Default for Script {
    fn default() -> Self {
        let mut program = [0; 32]; program[0] = 9;
        Self { on_curve: false, height: 1, return_program: program, return_data: vec![2, 3] }
    }
}
impl Script {
    pub fn state(&self) -> Json {
        self.state_with_input(&[5, 6])
    }
    pub fn state_with_input(&self, input: &[u8]) -> Json {
        Json::obj([
            ("return_program", rec::bytes(&self.return_program)),
            ("return_data", rec::bytes(&self.return_data)), ("height", self.height.into()),
            ("input", rec::bytes(input)), ("heap_pos", 17u64.into()),
            ("logs", Json::arr([vec![99]], |b| rec::bytes(&b))),
        ])
    }
}
struct State { script: Script, pipe: i32, trace: Vec<Json>, capture: bool, captured: Vec<Record> }
thread_local! { static STATE: RefCell<State> = RefCell::new(State {
    script: Script::default(), pipe: -1, trace: vec![], capture: false, captured: vec![],
}); }
extern "C" {
    fn pipe(fds: *mut i32) -> i32;
    fn fork() -> i32;
    fn close(fd: i32) -> i32;
    fn read(fd: i32, buf: *mut u8, count: usize) -> isize;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
    fn _exit(status: i32) -> !;
}
pub fn state() -> Json { STATE.with(|s| s.borrow().script.state()) }
pub fn state_with_input(input: &[u8]) -> Json {
    STATE.with(|s| s.borrow().script.state_with_input(input))
}
pub fn trace() -> Json { STATE.with(|s| Json::Arr(s.borrow().trace.clone())) }
fn event(event: Json) { STATE.with(|s| s.borrow_mut().trace.push(event)); }
fn stage(name: &str) { event(name.into()); }
fn finish(outcome: Json) -> ! {
    let fd = STATE.with(|s| s.borrow().pipe);
    let text = outcome.to_text();
    let mut sent = 0;
    while sent < text.len() {
        let count = unsafe { write(fd, text.as_ptr().add(sent), text.len() - sent) };
        if count <= 0 { unsafe { _exit(125) } }
        sent += count as usize;
    }
    unsafe { _exit(0) }
}
fn terminal() -> ! {
    finish(Json::obj([("exit", "terminated".into()),
        ("reason", "ProgramFailedToComplete".into()), ("trace", trace())]))
}
fn fault() -> ! {
    finish(Json::obj([("exit", "terminated".into()), ("reason", "shim-fault".into())]))
}
pub fn case(script: &Script, f: impl FnOnce() -> Json) -> Json {
    let mut fds = [0; 2];
    assert_eq!(unsafe { pipe(fds.as_mut_ptr()) }, 0);
    let pid = unsafe { fork() }; assert!(pid >= 0);
    if pid == 0 {
        unsafe { close(fds[0]); }
        STATE.with(|s| *s.borrow_mut() = State { script: script.clone(), pipe: fds[1], trace: vec![], capture: false, captured: vec![] });
        std::panic::set_hook(Box::new(|_| fault()));
        finish(f());
    }
    unsafe { close(fds[1]); }
    let mut result = vec![]; let mut buffer = [0; 65536];
    loop {
        let count = unsafe { read(fds[0], buffer.as_mut_ptr(), buffer.len()) };
        assert!(count >= 0);
        if count == 0 { break; }
        result.extend_from_slice(&buffer[..count as usize]);
    }
    unsafe { close(fds[0]); }
    let mut status = 0;
    assert_eq!(unsafe { waitpid(pid, &mut status, 0) }, pid);
    assert_eq!(status, 0, "native provider child died without a recorded outcome");
    assert!(!result.is_empty());
    Json::Raw(String::from_utf8(result).unwrap())
}
unsafe fn bytes(pointer: *const u8, count: usize) -> Vec<u8> {
    if count == 0 { vec![] } else { core::slice::from_raw_parts(pointer, count).to_vec() }
}
fn overlap(a: usize, an: usize, b: usize, bn: usize) -> bool {
    an != 0 && bn != 0 && a < b.saturating_add(bn) && b < a.saturating_add(an)
}
#[no_mangle]
pub unsafe extern "C" fn sol_memcpy_(dst: *mut u8, src: *const u8, n: u64) {
    let capture = begin_memory("copy", dst, src, n as usize, 0);
    stage("copy");
    if overlap(dst as usize, n as usize, src as usize, n as usize) { terminal(); }
    if n != 0 {
        // The provider captures input before writing, as ptr::copy permits host aliases.
        let data = bytes(src, n as usize);
        event(Json::obj([("read", rec::bytes(&data))]));
        core::ptr::copy(data.as_ptr(), dst, n as usize);
        stage("write-data");
    }
    end_memory(capture, dst, n as usize);
}
#[no_mangle]
pub unsafe extern "C" fn sol_memset_(dst: *mut u8, c: u8, n: u64) {
    let capture = begin_memory("set", dst, core::ptr::null(), n as usize, c);
    stage("set");
    if n != 0 { core::ptr::write_bytes(dst, c, n as usize); stage("write-data"); }
    end_memory(capture, dst, n as usize);
}
#[repr(C)]
#[derive(Clone, Copy)]
struct Slice { pointer: *const u8, length: u64 }
unsafe fn seeds(vals: *const u8, count: u64, bounded: bool) -> Vec<Vec<u8>> {
    stage("descriptors");
    let descriptors = if count == 0 { vec![] }
        else { core::slice::from_raw_parts(vals.cast::<Slice>(), count as usize).to_vec() };
    if bounded && count > 16 { terminal(); }
    descriptors.into_iter().map(|s| {
        if bounded && s.length > 32 { terminal(); }
        let data = bytes(s.pointer, s.length as usize);
        event(Json::obj([("seed", rec::bytes(&data))])); data
    }).collect()
}
unsafe fn program(pointer: *const u8) {
    event(Json::obj([("program", rec::bytes(&bytes(pointer, 32)))]));
}
#[no_mangle]
pub unsafe extern "C" fn sol_create_program_address(
    vals: *const u8, count: u64, id: *const u8, output: *mut u8,
) -> u64 {
    stage("create"); let _ = seeds(vals, count, true); program(id); stage("derive");
    if STATE.with(|s| s.borrow().script.on_curve) { return 1; }
    core::ptr::copy_nonoverlapping([7u8; 32].as_ptr(), output, 32);
    stage("write-address"); 0
}
#[no_mangle]
pub unsafe extern "C" fn sol_try_find_program_address(
    vals: *const u8, count: u64, id: *const u8, output: *mut u8, bump: *mut u8,
) -> u64 {
    stage("find"); let _ = seeds(vals, count, true); program(id); stage("derive");
    if count == 16 || STATE.with(|s| s.borrow().script.on_curve) { return 1; }
    if overlap(output as usize, 32, bump as usize, 1) { terminal(); }
    *bump = 255; stage("write-bump");
    core::ptr::copy_nonoverlapping([7u8; 32].as_ptr(), output, 32);
    stage("write-address"); 0
}
#[no_mangle]
pub unsafe extern "C" fn sol_sha256(vals: *const u8, count: u64, output: *mut u8) -> u64 {
    stage("sha256");
    if count > 20000 { terminal(); }
    let _ = seeds(vals, count, false);
    core::ptr::copy_nonoverlapping([7u8; 32].as_ptr(), output, 32);
    stage("write-data"); 0
}
fn words(values: &[u64]) -> Vec<u8> { values.iter().flat_map(|v| v.to_le_bytes()).collect() }
unsafe fn typed(name: &str, dst: *mut u8, data: &[u8]) -> u64 {
    stage(name); core::ptr::copy_nonoverlapping(data.as_ptr(), dst, data.len());
    stage("write-data"); 0
}
#[no_mangle]
pub unsafe extern "C" fn sol_get_clock_sysvar(dst: *mut u8) -> u64 {
    typed("clock", dst, &words(&[17, (-3i64) as u64, 2, 3, 41]))
}
#[no_mangle]
pub unsafe extern "C" fn sol_get_rent_sysvar(dst: *mut u8) -> u64 {
    // Solanalib.Runtime.mainnetRent in the pinned runtime: 5080 and threshold 1.
    let mut data = words(&[5080, 1f64.to_bits()]);
    data.push(50); data.extend([0; 7]); typed("rent", dst, &data)
}
#[no_mangle]
pub unsafe extern "C" fn sol_get_epoch_schedule_sysvar(dst: *mut u8) -> u64 {
    let mut data = words(&[432000, 432000]); data.push(1); data.extend([0; 7]);
    data.extend(words(&[14, 524256])); typed("epoch", dst, &data)
}
#[no_mangle]
pub unsafe extern "C" fn sol_get_stack_height() -> u64 {
    stage("stack"); STATE.with(|s| s.borrow().script.height)
}
#[no_mangle]
pub unsafe extern "C" fn sol_set_return_data(data: *const u8, length: u64) {
    stage("set-return"); if length > 1024 { terminal(); }
    let data = bytes(data, length as usize);
    event(Json::obj([("read", rec::bytes(&data))]));
    STATE.with(|s| { let mut s = s.borrow_mut();
        s.script.return_program = [0; 32]; s.script.return_program[31] = 7;
        s.script.return_data = data;
    });
}
#[no_mangle]
pub unsafe extern "C" fn sol_get_return_data(data: *mut u8, capacity: u64, id: *mut u8) -> u64 {
    stage("get-return");
    let script = STATE.with(|s| s.borrow().script.clone());
    let n = usize::min(capacity as usize, script.return_data.len());
    if n != 0 {
        if overlap(data as usize, n, id as usize, 32) { terminal(); }
        core::ptr::copy_nonoverlapping(script.return_data.as_ptr(), data, n); stage("write-data");
        core::ptr::copy_nonoverlapping(script.return_program.as_ptr(), id, 32); stage("write-program");
    }
    script.return_data.len() as u64
}

// Capture actual calls of a private SDK declaration from its public formatting API.
// The driver supplies initialized destination storage plus eight valid guard bytes on
// each side of every write. Capturing is disabled in all other drivers.
pub fn capture_memory_calls() { STATE.with(|s| s.borrow_mut().capture = true); }
struct MemoryCapture { operation: &'static str, args: Json, before: Json, trace_start: usize }
unsafe fn memory_guards(dst: *const u8, n: usize) -> Vec<u8> {
    [bytes(dst.sub(8), 8), bytes(dst.add(n), 8)].concat()
}
unsafe fn begin_memory(operation: &'static str, dst: *mut u8, src: *const u8, n: usize, byte: u8) -> Option<MemoryCapture> {
    if !STATE.with(|s| s.borrow().capture) { return None; }
    let mut program = [0; 32]; program[0] = 7;
    let input = if operation == "copy" { bytes(src, n) } else { vec![] };
    let args = Json::obj([
        ("input", rec::bytes(&input)), ("seeds", Json::Arr(vec![])),
        ("program", rec::bytes(&program)), ("count", n.into()), ("byte", byte.into()),
        ("capacity", 0usize.into()), ("on_curve", false.into()), ("overlap", false.into()),
        ("input_region", false.into()),
        ("output", rec::bytes(&bytes(dst, n))), ("guards", rec::bytes(&memory_guards(dst, n))),
        ("program_output", rec::bytes(&[0xa5; 32])),
        ("program_guards", rec::bytes(&[[0x3c; 8], [0xc3; 8]].concat())), ("bump", 94u8.into()),
    ]);
    Some(MemoryCapture { operation, args, before: state(), trace_start: STATE.with(|s| s.borrow().trace.len()) })
}
unsafe fn end_memory(capture: Option<MemoryCapture>, dst: *mut u8, n: usize) {
    let Some(capture) = capture else { return; };
    let result = Json::obj([
        ("status", 0u64.into()), ("output", rec::bytes(&bytes(dst, n))),
        ("guards", rec::bytes(&memory_guards(dst, n))), ("program_output", rec::bytes(&[0xa5; 32])),
        ("program_guards", rec::bytes(&[[0x3c; 8], [0xc3; 8]].concat())), ("bump", 94u8.into()),
    ]);
    let after = state();
    STATE.with(|s| { let mut s = s.borrow_mut();
        let trace = Json::Arr(s.trace[capture.trace_start..].to_vec());
        let id = format!("{}/{}", capture.operation, s.captured.len());
        let function = if capture.operation == "copy" { "pinocchio_log::logger::syscalls::sol_memcpy_" }
            else { "pinocchio_log::logger::syscalls::sol_memset_" };
        s.captured.push(Record { id, function, generics: vec![], layout: None, state: capture.before,
            args: capture.args, outcome: Json::obj([("exit", "returned".into()), ("result", result),
                ("state", after), ("trace", trace)]), observed: None });
    });
}
pub fn write_memory_corpus() {
    let mut corpus = Corpus::new("raw_runtime_pinocchio_log_0_5_1", &[("pinocchio-log", "0.5.1")]);
    let records = STATE.with(|s| std::mem::take(&mut s.borrow_mut().captured));
    assert!(records.iter().any(|r| r.function.ends_with("sol_memset_")));
    assert!(records.iter().any(|r| r.function.ends_with("sol_memcpy_")));
    for record in records { corpus.push(record); }
    corpus.write(&rec::out_dir()).expect("write captured private declaration calls");
}
