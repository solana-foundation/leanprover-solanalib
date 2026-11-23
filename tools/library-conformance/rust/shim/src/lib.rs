//! Test definitions of the Solana `sol_*` syscalls.
//!
//! Built with `--cfg target_os="solana"`, the Solana crates declare the
//! syscalls as `extern "C"` functions (`solana-define-syscall` 3.x to 5.x);
//! this crate defines them. Each call is appended to a request log; a call
//! that returns data consumes the next scripted reply, which the case chose.
//! The shim therefore tests the program side only: what the library asks the
//! runtime, and what it does with the answer.
//!
//! Every case runs in a forked child process (`case`), so a syscall that does
//! not return (`sol_panic_`, `abort`, a reply marked `terminate`) ends the
//! child after reporting a terminated outcome, and cases cannot affect each
//! other. The record shape is documented in the suite README ("Syscalls").

#![feature(panic_can_unwind)]

use conformance_recorder::{self as rec, Json};
use std::cell::RefCell;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicI32, Ordering};

// ---------------------------------------------------------------------------
// Scripts and replies
// ---------------------------------------------------------------------------

/// A memory effect of a CPI on one account of the C ABI account-info array,
/// applied before `sol_invoke_signed_c` returns (the callee effects).
#[derive(Clone, Debug, Default)]
pub struct AccountWrite {
    pub account: usize,
    pub lamports: Option<u64>,
    /// Overwrites the first `data.len()` bytes (at most the current length).
    pub data: Option<Vec<u8>>,
    pub owner: Option<[u8; 32]>,
}

impl AccountWrite {
    fn to_json(&self) -> Json {
        let mut fields = vec![("account".to_string(), Json::from(self.account))];
        if let Some(l) = self.lamports {
            fields.push(("lamports".into(), Json::from(l)));
        }
        if let Some(d) = &self.data {
            fields.push(("data".into(), rec::bytes(d)));
        }
        if let Some(o) = &self.owner {
            fields.push(("owner".into(), rec::bytes(o)));
        }
        Json::Obj(fields)
    }
}

/// One scripted reply, consumed by the next call of `syscall`.
#[derive(Clone, Debug)]
pub struct Reply {
    pub syscall: String,
    /// The syscall return value (`u64`), where it has one.
    pub ret: u64,
    /// Bytes written to the call output buffer (sysvar, hash, address, return data).
    pub data: Vec<u8>,
    /// `sol_get_return_data`: the program id written with the data.
    pub program_id: Option<[u8; 32]>,
    /// `sol_try_find_program_address`: the bump seed.
    pub bump: Option<u8>,
    /// The call does not return: the case ends with a terminated outcome
    /// whose reason is the syscall name and whose detail is this text.
    pub terminate: Option<String>,
    /// `sol_invoke_signed_c`: account memory effects of the callee.
    pub writes: Vec<AccountWrite>,
}

impl Reply {
    pub fn new(syscall: &str, ret: u64) -> Self {
        Reply { syscall: syscall.to_string(), ret, data: Vec::new(), program_id: None, bump: None,
                terminate: None, writes: Vec::new() }
    }

    pub fn data(mut self, data: &[u8]) -> Self {
        self.data = data.to_vec();
        self
    }

    pub fn program_id(mut self, id: [u8; 32]) -> Self {
        self.program_id = Some(id);
        self
    }

    pub fn bump(mut self, bump: u8) -> Self {
        self.bump = Some(bump);
        self
    }

    pub fn terminate(mut self, detail: &str) -> Self {
        self.terminate = Some(detail.to_string());
        self
    }

    pub fn write(mut self, write: AccountWrite) -> Self {
        self.writes.push(write);
        self
    }

    pub fn to_json(&self) -> Json {
        let mut fields = vec![
            ("syscall".to_string(), Json::from(self.syscall.as_str())),
            ("return".to_string(), Json::from(self.ret)),
            ("data".to_string(), rec::bytes(&self.data)),
        ];
        if let Some(p) = &self.program_id {
            fields.push(("program_id".into(), rec::bytes(p)));
        }
        if let Some(b) = self.bump {
            fields.push(("bump".into(), Json::from(b)));
        }
        if let Some(t) = &self.terminate {
            fields.push(("terminate".into(), Json::from(t.as_str())));
        }
        if !self.writes.is_empty() {
            fields.push(("writes".into(), Json::arr(self.writes.iter(), |w| w.to_json())));
        }
        Json::Obj(fields)
    }
}

/// The replies of one case, in the order the calls consume them.
#[derive(Clone, Debug, Default)]
pub struct Script(pub Vec<Reply>);

impl Script {
    pub fn new(replies: Vec<Reply>) -> Self {
        Script(replies)
    }

    /// The syscall state before the call: `{"replies": [...], "log": []}`.
    pub fn state_before(&self) -> Json {
        Json::obj([("replies", Json::arr(self.0.iter(), |r| r.to_json())), ("log", Json::Arr(vec![]))])
    }
}

/// Decodes the arguments of `sol_invoke_signed_rust`, whose instruction and
/// account-info layouts belong to the caller crate versions. A driver that
/// records Rust-ABI CPI registers one with `set_invoke_rust_decoder`.
pub type InvokeRustDecoder = fn(instruction: *const u8, infos: *const u8, infos_len: u64,
                                seeds: *const u8, seeds_len: u64) -> Json;

#[derive(Default)]
struct State {
    replies: VecDeque<Reply>,
    log: Vec<Json>,
    invoke_rust: Option<InvokeRustDecoder>,
    raw_header: bool,
}

thread_local! {
    static STATE: RefCell<State> = RefCell::new(State::default());
}

/// The pipe to the parent while a case runs in a child; -1 otherwise.
static CHILD_FD: AtomicI32 = AtomicI32::new(-1);

thread_local! {
    /// The message of the last panic, and set when a panic could not unwind
    /// (a panic inside a syscall or a failed `unsafe` precondition check): such
    /// a panic aborts, and `abort` then reports a shim fault, not a program exit.
    static LAST_PANIC: RefCell<String> = const { RefCell::new(String::new()) };
    static NOUNWIND: RefCell<Option<String>> = const { RefCell::new(None) };
}

fn install_panic_hook() {
    std::panic::set_hook(Box::new(|info| {
        let payload = info.payload();
        let message = payload.downcast_ref::<&str>().map(|s| s.to_string())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "<non-string panic payload>".to_string());
        let location = info.location().map_or(String::new(), |l| format!(" at {}:{}", l.file(), l.line()));
        let text = format!("{message}{location}");
        if !info.can_unwind() {
            let previous = LAST_PANIC.with(|p| p.borrow().clone());
            NOUNWIND.with(|n| *n.borrow_mut() = Some(if previous.is_empty() { text.clone() } else { format!("{previous}; then {text}") }));
        }
        LAST_PANIC.with(|p| *p.borrow_mut() = text);
    }));
}

/// A fault of the shim or the test, not a program behavior: the case ends
/// with reason `shim-fault`, and `shim::case` fails the recording.
fn fault(message: String) -> ! {
    terminate("shim-fault", Json::from(message))
}

pub fn set_invoke_rust_decoder(decoder: InvokeRustDecoder) {
    STATE.with(|s| s.borrow_mut().invoke_rust = Some(decoder));
}

/// Also log, for each `sol_invoke_signed_c` account info, `"header"`: the raw
/// bytes `[is_signer, is_writable, executable, padding]` at offsets 48..52 of
/// the `SolAccountInfo`. Off by default: the fourth byte is struct padding,
/// uninitialized (and so not deterministic) for callers that build the struct
/// field by field; turn it on only for callers that copy the four header bytes
/// as one word, such as `CpiAccount` in solana-instruction-view 2.1.0.
pub fn log_cpi_raw_header(on: bool) {
    STATE.with(|s| s.borrow_mut().raw_header = on);
}

/// The syscall state now: unconsumed replies and every request so far.
/// Call it inside `case` to build the state after the call.
pub fn state() -> Json {
    STATE.with(|s| {
        let s = s.borrow();
        Json::obj([
            ("replies", Json::arr(s.replies.iter(), |r| r.to_json())),
            ("log", Json::Arr(s.log.clone())),
        ])
    })
}

fn log(entry: Json) {
    STATE.with(|s| s.borrow_mut().log.push(entry));
}

fn request(syscall: &str, mut args: Vec<(&str, Json)>) -> Json {
    let mut fields = vec![("syscall".to_string(), Json::from(syscall))];
    fields.extend(args.drain(..).map(|(k, v)| (k.to_string(), v)));
    Json::Obj(fields)
}

/// Pop the next reply, which must answer `syscall`; a missing or mismatched
/// reply ends the case as a recorder error (terminated, reason `shim`).
fn next_reply(syscall: &str) -> Reply {
    let reply = STATE.with(|s| s.borrow_mut().replies.pop_front());
    match reply {
        Some(r) if r.syscall == syscall => {
            if let Some(detail) = &r.terminate {
                terminate(syscall, Json::from(detail.as_str()));
            }
            r
        }
        Some(r) => terminate("shim", Json::from(format!("script error: {syscall} called, next reply is for {}", r.syscall))),
        None => terminate("shim", Json::from(format!("script error: {syscall} called, no reply left"))),
    }
}

// ---------------------------------------------------------------------------
// Process isolation
// ---------------------------------------------------------------------------

extern "C" {
    fn pipe(fds: *mut i32) -> i32;
    fn fork() -> i32;
    fn _exit(status: i32) -> !;
    fn close(fd: i32) -> i32;
    fn read(fd: i32, buf: *mut u8, n: usize) -> isize;
    fn write(fd: i32, buf: *const u8, n: usize) -> isize;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
}

fn send_and_exit(outcome: Json) -> ! {
    let fd = CHILD_FD.load(Ordering::SeqCst);
    let text = outcome.to_text();
    let mut sent = 0;
    while sent < text.len() {
        let n = unsafe { write(fd, text.as_ptr().add(sent), text.len() - sent) };
        if n <= 0 {
            break;
        }
        sent += n as usize;
    }
    unsafe { _exit(0) }
}

/// End the case: `{"exit": "terminated", "reason", "detail", "syscalls"}`.
/// Outside a case (no child), a terminal syscall is a recorder error.
fn terminate(reason: &str, detail: Json) -> ! {
    if CHILD_FD.load(Ordering::SeqCst) < 0 {
        eprintln!("conformance-shim: {reason} outside shim::case: {}", detail.to_text());
        unsafe { _exit(134) }
    }
    send_and_exit(Json::obj([
        ("exit", "terminated".into()),
        ("reason", reason.into()),
        ("detail", detail),
        ("syscalls", state()),
    ]))
}

/// Run one case in a forked child with `script` installed and an empty log.
/// `f` returns the case outcome (`rec::returned(result, state)` or
/// `rec::unwound(..)`), normally with `"syscalls": shim::state()` in its
/// state. A panic escaping `f` becomes an unwound outcome with the syscall
/// state. A terminal syscall yields its terminated outcome instead; a child
/// that dies otherwise yields `{"exit": "terminated", "reason": "process"}`.
pub fn case(script: &Script, f: impl FnOnce() -> Json) -> Json {
    let mut fds = [0i32; 2];
    assert_eq!(unsafe { pipe(fds.as_mut_ptr()) }, 0, "pipe failed");
    let pid = unsafe { fork() };
    assert!(pid >= 0, "fork failed");
    if pid == 0 {
        unsafe { close(fds[0]) };
        CHILD_FD.store(fds[1], Ordering::SeqCst);
        install_panic_hook();
        STATE.with(|s| {
            let mut s = s.borrow_mut();
            s.replies = script.0.iter().cloned().collect();
            s.log.clear();
        });
        let outcome = match rec::catch(f) {
            Ok(outcome) => outcome,
            Err(reason) => rec::unwound(reason, Json::obj([("syscalls", state())])),
        };
        send_and_exit(outcome);
    }
    unsafe { close(fds[1]) };
    let mut text = Vec::new();
    let mut buf = [0u8; 65536];
    loop {
        let n = unsafe { read(fds[0], buf.as_mut_ptr(), buf.len()) };
        if n <= 0 {
            break;
        }
        text.extend_from_slice(&buf[..n as usize]);
    }
    unsafe { close(fds[0]) };
    let mut status = 0i32;
    unsafe { waitpid(pid, &mut status, 0) };
    let text = String::from_utf8(text).expect("child output is UTF-8");
    if text.is_empty() || status != 0 {
        return Json::obj([
            ("exit", "terminated".into()),
            ("reason", "process".into()),
            ("detail", Json::obj([("status", Json::Int(status as i128))])),
        ]);
    }
    assert!(!text.contains("\"reason\":\"shim\"") && !text.contains("\"reason\":\"shim-fault\""),
            "shim script error or fault in a case: {text}");
    Json::Raw(text)
}

// ---------------------------------------------------------------------------
// Memory readers
// ---------------------------------------------------------------------------

unsafe fn slice<'a>(ptr: *const u8, len: u64) -> &'a [u8] {
    if len == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(ptr, len as usize)
    }
}

unsafe fn key(ptr: *const u8) -> Json {
    rec::bytes(slice(ptr, 32))
}

/// `&[&[u8]]` passed as (pointer, count): fat pointers (address, length).
pub unsafe fn byte_slices(ptr: *const u8, count: u64) -> Vec<Vec<u8>> {
    let pairs = ptr as *const (*const u8, u64);
    (0..count as usize).map(|i| { let (p, n) = *pairs.add(i); slice(p, n).to_vec() }).collect()
}

fn slices_json(v: &[Vec<u8>]) -> Json {
    Json::arr(v.iter(), |b| rec::bytes(b))
}

/// Rust-ABI signer seeds `&[&[&[u8]]]` (also the C ABI `SolSignerSeeds`
/// layout: pointer and length pairs at each level).
pub unsafe fn signer_seeds(ptr: *const u8, count: u64) -> Json {
    let signers = ptr as *const (*const u8, u64);
    Json::arr(0..count as usize, |i| { let (p, n) = *signers.add(i); slices_json(&byte_slices(p, n)) })
}

// Flag fields are read as bytes, never as `bool`: a caller may copy raw
// header bytes, and a byte other than 0 or 1 read as `bool` is undefined
// behavior. The logged booleans mean "byte is nonzero".
#[repr(C)]
struct CAccountMeta {
    pubkey: *const u8,
    is_writable: u8,
    is_signer: u8,
}

#[repr(C)]
struct CInstruction {
    program_id: *const u8,
    accounts: *const CAccountMeta,
    accounts_len: u64,
    data: *const u8,
    data_len: u64,
}

#[repr(C)]
struct CAccountInfo {
    key: *const u8,
    lamports: *mut u64,
    data_len: u64,
    data: *mut u8,
    owner: *mut u8,
    rent_epoch: u64,
    is_signer: u8,
    is_writable: u8,
    executable: u8,
    /// Struct padding in the C ABI; see `log_cpi_raw_header`.
    header_padding: u8,
}

// ---------------------------------------------------------------------------
// The syscalls
// ---------------------------------------------------------------------------

/// Copy the reply bytes to the caller buffer of `max` bytes, bounded by
/// that size (the runtime never writes past it).
macro_rules! out_data {
    ($reply:expr, $dst:expr, $max:expr) => {{
        let n = $reply.data.len().min($max as usize);
        core::ptr::copy_nonoverlapping($reply.data.as_ptr(), $dst, n);
    }};
}

#[no_mangle]
pub unsafe extern "C" fn sol_log_(message: *const u8, len: u64) {
    log(request("sol_log_", vec![("bytes", rec::bytes(slice(message, len)))]));
}

#[no_mangle]
pub unsafe extern "C" fn sol_log_64_(a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) {
    log(request("sol_log_64_", vec![("args", Json::arr([a1, a2, a3, a4, a5], Json::from))]));
}

#[no_mangle]
pub unsafe extern "C" fn sol_log_compute_units_() {
    log(request("sol_log_compute_units_", vec![]));
}

#[no_mangle]
pub unsafe extern "C" fn sol_log_data(data: *const u8, data_len: u64) {
    log(request("sol_log_data", vec![("fields", slices_json(&byte_slices(data, data_len)))]));
}

#[no_mangle]
pub unsafe extern "C" fn sol_log_pubkey(pubkey_addr: *const u8) {
    log(request("sol_log_pubkey", vec![("address", key(pubkey_addr))]));
}

#[no_mangle]
pub unsafe extern "C" fn sol_set_return_data(data: *const u8, length: u64) {
    log(request("sol_set_return_data", vec![("bytes", rec::bytes(slice(data, length)))]));
}

/// As agave: the reply data is the transaction return data and its value
/// is the data length `len` (a reply whose value differs is a shim fault).
/// Copies `min(length, len)` bytes and the program id when that is nonzero,
/// and returns `len`.
#[no_mangle]
pub unsafe extern "C" fn sol_get_return_data(data: *mut u8, length: u64, program_id: *mut u8) -> u64 {
    log(request("sol_get_return_data", vec![("length", Json::from(length))]));
    let reply = next_reply("sol_get_return_data");
    let len = reply.data.len() as u64;
    if reply.ret != len {
        fault(format!("sol_get_return_data: the reply's value {} differs from its data length {len}", reply.ret));
    }
    let n = length.min(len) as usize;
    if n != 0 {
        core::ptr::copy_nonoverlapping(reply.data.as_ptr(), data, n);
        match reply.program_id {
            Some(id) => core::ptr::copy_nonoverlapping(id.as_ptr(), program_id, 32),
            None => fault("sol_get_return_data: a reply with data needs a program_id".to_string()),
        }
    }
    len
}

macro_rules! sysvar_getter {
    ($name:ident, $size:expr) => {
        /// On status 0, copies the reply bytes, bounded by `size_of` the
        /// sysvar struct the runtime writes, to `addr`; on any other status
        /// writes nothing.
        #[no_mangle]
        pub unsafe extern "C" fn $name(addr: *mut u8) -> u64 {
            log(request(stringify!($name), vec![]));
            let reply = next_reply(stringify!($name));
            if reply.ret == 0 {
                out_data!(reply, addr, $size);
            }
            reply.ret
        }
    };
}
// `size_of` of the in-memory sysvar structs the getters fill (repr(C), x86-64).
sysvar_getter!(sol_get_clock_sysvar, 40);
sysvar_getter!(sol_get_rent_sysvar, 24);
sysvar_getter!(sol_get_epoch_schedule_sysvar, 40);
sysvar_getter!(sol_get_epoch_rewards_sysvar, 96);
sysvar_getter!(sol_get_last_restart_slot, 8);
sysvar_getter!(sol_get_fees_sysvar, 8);

#[no_mangle]
pub unsafe extern "C" fn sol_get_sysvar(sysvar_id_addr: *const u8, result: *mut u8, offset: u64, length: u64) -> u64 {
    log(request("sol_get_sysvar", vec![("sysvar_id", key(sysvar_id_addr)),
        ("offset", Json::from(offset)), ("length", Json::from(length))]));
    let reply = next_reply("sol_get_sysvar");
    // On status 0 the runtime fills the requested bytes; otherwise nothing.
    if reply.ret == 0 {
        out_data!(reply, result, length);
    }
    reply.ret
}

macro_rules! hasher {
    ($name:ident) => {
        /// Logs the input slices; writes the 32 reply bytes.
        #[no_mangle]
        pub unsafe extern "C" fn $name(vals: *const u8, val_len: u64, hash_result: *mut u8) -> u64 {
            log(request(stringify!($name), vec![("fields", slices_json(&byte_slices(vals, val_len)))]));
            let reply = next_reply(stringify!($name));
            out_data!(reply, hash_result, 32);
            reply.ret
        }
    };
}
hasher!(sol_sha256);
hasher!(sol_keccak256);
hasher!(sol_blake3);

/// These calls promise a complete result on success and no write on failure.
/// Reject inconsistent scripts before touching the output pointer, which may
/// be null when the call fails.
unsafe fn checked_output(reply: &Reply, result: *mut u8, width: usize) {
    if (reply.ret == 0 && reply.data.len() != width) || (reply.ret != 0 && !reply.data.is_empty()) {
        fault("reply outside the output shape".to_string());
    }
    if reply.ret == 0 {
        out_data!(reply, result, width);
    }
}

#[no_mangle]
pub unsafe extern "C" fn sol_sha512(vals: *const u8, count: u64, result: *mut u8) -> u64 {
    log(request("sol_sha512", vec![("fields", slices_json(&byte_slices(vals, count)))]));
    let reply = next_reply("sol_sha512");
    checked_output(&reply, result, 64);
    reply.ret
}

#[no_mangle]
pub unsafe extern "C" fn sol_create_program_address(seeds_addr: *const u8, seeds_len: u64,
                                                    program_id_addr: *const u8, address_bytes_addr: *mut u8) -> u64 {
    log(request("sol_create_program_address", vec![("seeds", slices_json(&byte_slices(seeds_addr, seeds_len))),
        ("program_id", key(program_id_addr))]));
    let reply = next_reply("sol_create_program_address");
    out_data!(reply, address_bytes_addr, 32);
    reply.ret
}

#[no_mangle]
pub unsafe extern "C" fn sol_try_find_program_address(seeds_addr: *const u8, seeds_len: u64,
                                                      program_id_addr: *const u8, address_bytes_addr: *mut u8,
                                                      bump_seed_addr: *mut u8) -> u64 {
    // The bump byte the caller left in its output slot before the call.
    let initial_bump = if bump_seed_addr.is_null() { Json::Null } else { Json::from(*bump_seed_addr) };
    log(request("sol_try_find_program_address", vec![("seeds", slices_json(&byte_slices(seeds_addr, seeds_len))),
        ("program_id", key(program_id_addr)), ("bump", initial_bump)]));
    let reply = next_reply("sol_try_find_program_address");
    out_data!(reply, address_bytes_addr, 32);
    if let Some(b) = reply.bump {
        *bump_seed_addr = b;
    }
    reply.ret
}

#[no_mangle]
pub unsafe extern "C" fn sol_curve_validate_point(curve_id: u64, point_addr: *const u8, result: *mut u8) -> u64 {
    // The byte behind a non-null result pointer, read before the call (the
    // initial scratch byte in the models); null for a null pointer.
    let initial = if result.is_null() { Json::Null } else { Json::from(core::ptr::read_volatile(result)) };
    log(request("sol_curve_validate_point", vec![("curve_id", Json::from(curve_id)), ("point", key(point_addr)),
        ("result_null", result.is_null().into()), ("result_initial", initial)]));
    next_reply("sol_curve_validate_point").ret
}

#[no_mangle]
pub unsafe extern "C" fn sol_curve_group_op(curve_id: u64, group_op: u64, left: *const u8, right: *const u8,
                                            result: *mut u8) -> u64 {
    log(request("sol_curve_group_op", vec![("curve_id", Json::from(curve_id)), ("group_op", Json::from(group_op)),
        ("left", key(left)), ("right", key(right))]));
    let reply = next_reply("sol_curve_group_op");
    out_data!(reply, result, 32);
    reply.ret
}

#[no_mangle]
pub unsafe extern "C" fn sol_curve_multiscalar_mul(
    curve: u64, scalars: *const u8, points: *const u8, count: u64, result: *mut u8,
) -> u64 {
    // Agave checks the count before the curve and every pointer. Invalid
    // curves also skip the input reads; the script selects failure or exit.
    if count > 512 {
        terminate("abort", Json::Null);
    }
    let valid = curve == 0 || curve == 1;
    let elements = |ptr: *const u8| {
        if valid { Json::arr(0..count as usize, |i| key(ptr.add(i * 32))) }
        else { Json::Arr(vec![]) }
    };
    log(request("sol_curve_multiscalar_mul", vec![
        ("curve_id", curve.into()), ("count", count.into()),
        ("scalars", elements(scalars)), ("points", elements(points)),
    ]));
    let reply = next_reply("sol_curve_multiscalar_mul");
    if reply.ret > 1 || (!valid && reply.ret == 0) {
        fault("reply outside the output shape".to_string());
    }
    checked_output(&reply, result, 32);
    reply.ret
}

#[no_mangle]
pub unsafe extern "C" fn sol_get_stack_height() -> u64 {
    log(request("sol_get_stack_height", vec![]));
    next_reply("sol_get_stack_height").ret
}

#[no_mangle]
pub unsafe extern "C" fn sol_remaining_compute_units() -> u64 {
    log(request("sol_remaining_compute_units", vec![]));
    next_reply("sol_remaining_compute_units").ret
}

#[no_mangle]
pub unsafe extern "C" fn sol_get_epoch_stake(vote_address: *const u8) -> u64 {
    let address = if vote_address.is_null() { Json::Null } else { key(vote_address) };
    log(request("sol_get_epoch_stake", vec![("vote_address", address)]));
    next_reply("sol_get_epoch_stake").ret
}

/// The C ABI: `SolInstruction`, `SolAccountInfo[]`, `SolSignerSeeds[]`.
/// Logs the prepared instruction, account infos and seeds; applies the
/// reply account writes; returns its value (or terminates, if marked).
#[no_mangle]
pub unsafe extern "C" fn sol_invoke_signed_c(instruction_addr: *const u8, account_infos_addr: *const u8,
                                             account_infos_len: u64, signers_seeds_addr: *const u8,
                                             signers_seeds_len: u64) -> u64 {
    let ix = &*(instruction_addr as *const CInstruction);
    let metas = (0..ix.accounts_len as usize).map(|i| &*ix.accounts.add(i));
    let instruction = Json::obj([
        ("program_id", key(ix.program_id)),
        ("accounts", Json::Arr(metas.map(|m| Json::obj([("pubkey", key(m.pubkey)),
            ("is_signer", (m.is_signer != 0).into()), ("is_writable", (m.is_writable != 0).into())])).collect())),
        ("data", rec::bytes(slice(ix.data, ix.data_len))),
    ]);
    let infos = account_infos_addr as *mut CAccountInfo;
    let raw_header = STATE.with(|s| s.borrow().raw_header);
    let account_infos = Json::arr(0..account_infos_len as usize, |i| {
        let a = &*infos.add(i);
        let mut fields = vec![
            ("key".to_string(), key(a.key)),
            ("lamports".to_string(), Json::from(*a.lamports)),
            ("data".to_string(), rec::bytes(slice(a.data, a.data_len))),
            ("owner".to_string(), key(a.owner)),
            ("rent_epoch".to_string(), Json::from(a.rent_epoch)),
            ("is_signer".to_string(), (a.is_signer != 0).into()),
            ("is_writable".to_string(), (a.is_writable != 0).into()),
            ("executable".to_string(), (a.executable != 0).into()),
        ];
        if raw_header {
            let header = (infos.add(i) as *const u8).add(48);
            fields.push(("header".to_string(), Json::arr(0..4, |k| Json::from(core::ptr::read_volatile(header.add(k))))));
        }
        Json::Obj(fields)
    });
    log(request("sol_invoke_signed_c", vec![("instruction", instruction), ("account_infos", account_infos),
        ("signers_seeds", signer_seeds(signers_seeds_addr, signers_seeds_len))]));
    let reply = next_reply("sol_invoke_signed_c");
    for w in &reply.writes {
        if (w.account as u64) >= account_infos_len {
            fault(format!("CPI write to account {} of {}", w.account, account_infos_len));
        }
        let a = &mut *infos.add(w.account);
        if let Some(l) = w.lamports {
            *a.lamports = l;
        }
        if let Some(d) = &w.data {
            if d.len() as u64 > a.data_len {
                fault(format!("CPI data write of {} bytes into {} bytes of account data", d.len(), a.data_len));
            }
            core::ptr::copy_nonoverlapping(d.as_ptr(), a.data, d.len());
        }
        if let Some(o) = &w.owner {
            core::ptr::copy_nonoverlapping(o.as_ptr(), a.owner, 32);
        }
    }
    reply.ret
}

/// The Rust ABI: decoded by the decoder registered by the driver (its crate
/// versions fix the layouts), then answered like `sol_invoke_signed_c`
/// without account writes.
#[no_mangle]
pub unsafe extern "C" fn sol_invoke_signed_rust(instruction_addr: *const u8, account_infos_addr: *const u8,
                                                account_infos_len: u64, signers_seeds_addr: *const u8,
                                                signers_seeds_len: u64) -> u64 {
    let decoder = STATE.with(|s| s.borrow().invoke_rust);
    let decoded = match decoder {
        Some(d) => d(instruction_addr, account_infos_addr, account_infos_len, signers_seeds_addr, signers_seeds_len),
        None => terminate("shim", Json::from("sol_invoke_signed_rust without a registered decoder")),
    };
    log(request("sol_invoke_signed_rust", vec![("call", decoded)]));
    let reply = next_reply("sol_invoke_signed_rust");
    if !reply.writes.is_empty() {
        fault("account writes are only supported for sol_invoke_signed_c".to_string());
    }
    reply.ret
}

/// Memory syscalls perform the operation and log its size and inputs.
#[no_mangle]
pub unsafe extern "C" fn sol_memcpy_(dst: *mut u8, src: *const u8, n: u64) {
    log(request("sol_memcpy_", vec![("bytes", rec::bytes(slice(src, n)))]));
    core::ptr::copy_nonoverlapping(src, dst, n as usize);
}

#[no_mangle]
pub unsafe extern "C" fn sol_memmove_(dst: *mut u8, src: *const u8, n: u64) {
    log(request("sol_memmove_", vec![("bytes", rec::bytes(slice(src, n)))]));
    core::ptr::copy(src, dst, n as usize);
}

#[no_mangle]
pub unsafe extern "C" fn sol_memset_(s: *mut u8, c: u8, n: u64) {
    log(request("sol_memset_", vec![("byte", Json::from(c)), ("n", Json::from(n))]));
    core::ptr::write_bytes(s, c, n as usize);
}

/// Writes the difference of the first differing byte pair, as the runtime
/// does (`a[i] as i32 - b[i] as i32`, 0 if equal).
#[no_mangle]
pub unsafe extern "C" fn sol_memcmp_(s1: *const u8, s2: *const u8, n: u64, result: *mut i32) {
    let (a, b) = (slice(s1, n), slice(s2, n));
    let r = a.iter().zip(b).find(|(x, y)| x != y).map_or(0, |(x, y)| *x as i32 - *y as i32);
    log(request("sol_memcmp_", vec![("left", rec::bytes(a)), ("right", rec::bytes(b)), ("result", Json::Int(r as i128))]));
    *result = r;
}

/// `sol_panic_(file, len, line, column)`: terminated, reason `sol_panic_`.
#[no_mangle]
pub unsafe extern "C" fn sol_panic_(filename: *const u8, filename_len: u64, line: u64, column: u64) -> ! {
    terminate("sol_panic_", Json::obj([
        ("file", rec::bytes(slice(filename, filename_len))),
        ("line", Json::from(line)),
        ("column", Json::from(column)),
    ]))
}

/// `abort()`: terminated, reason `abort`. This definition also receives the
/// process aborts. One that follows a panic that cannot unwind (for
/// example a failed `unsafe` precondition check in a debug build, which the
/// panic hook notes in `NOUNWIND`) is a shim fault, which fails `--record`.
#[no_mangle]
pub unsafe extern "C" fn abort() -> ! {
    if let Some(message) = NOUNWIND.with(|n| n.borrow_mut().take()) {
        fault(format!("panic without unwinding: {message}"));
    }
    terminate("abort", Json::Null)
}
