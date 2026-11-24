//! Host-target cases: the libraries built without `--cfg target_os="solana"` select their host
//! branches. Getters in solana-sysvar and `sol_log_data` and `set_return_data` in solana-program
//! call the overridable `program_stubs`; this harness installs `RecordingStubs`, which logs
//! each stub call and answers getters from a script (status, bytes copied to the destination,
//! or a panic). `sol_log` in solana-msg prints a line; the harness captures standard output.
//!
//! The driver crate root must `use solana_sysvar::program_stubs` (or the solana-program
//! re-export) as `program_stubs`. Every case runs in a forked child (`conformance_shim::case`),
//! since a panicking stub poisons the stub lock. The record state is
//! `{"stubs": {"replies": [...], "log": [...]}, "stdout": hex}`.

use crate::program_stubs::{self, SyscallStubs};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::Script;
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

#[derive(Clone)]
pub struct StubReply {
    pub syscall: &'static str,
    pub ret: u64,
    pub data: Vec<u8>,
    pub panic: Option<&'static str>,
}

impl StubReply {
    pub fn new(syscall: &'static str, ret: u64) -> Self {
        StubReply { syscall, ret, data: vec![], panic: None }
    }
    pub fn data(mut self, d: &[u8]) -> Self {
        self.data = d.to_vec();
        self
    }
    pub fn panic(mut self, message: &'static str) -> Self {
        self.panic = Some(message);
        self
    }
    fn json(&self) -> Json {
        let mut f = vec![
            ("syscall".to_string(), Json::from(self.syscall)),
            ("return".to_string(), Json::from(self.ret)),
            ("data".to_string(), rec::bytes(&self.data)),
        ];
        if let Some(p) = self.panic {
            f.push(("panic".to_string(), Json::from(p)));
        }
        Json::Obj(f)
    }
}

static STATE: Mutex<(VecDeque<StubReply>, Vec<Json>)> = Mutex::new((VecDeque::new(), Vec::new()));

fn log(entry: Json) {
    STATE.lock().unwrap().1.push(entry);
}

fn request(syscall: &str, fields: Vec<(&str, Json)>) -> Json {
    let mut f = vec![("syscall".to_string(), Json::from(syscall)), ("target".to_string(), Json::from("host_stub"))];
    f.extend(fields.into_iter().map(|(k, v)| (k.to_string(), v)));
    Json::Obj(f)
}

unsafe fn getter(syscall: &'static str, var_addr: *mut u8) -> u64 {
    log(request(syscall, vec![]));
    let reply = STATE.lock().unwrap().0.pop_front().expect("a scripted stub reply");
    assert_eq!(reply.syscall, syscall, "stub script error");
    if let Some(m) = reply.panic {
        panic!("{}", m);
    }
    core::ptr::copy_nonoverlapping(reply.data.as_ptr(), var_addr, reply.data.len());
    reply.ret
}

pub struct RecordingStubs;

impl SyscallStubs for RecordingStubs {
    fn sol_get_clock_sysvar(&self, var_addr: *mut u8) -> u64 {
        unsafe { getter("sol_get_clock_sysvar", var_addr) }
    }
    fn sol_get_rent_sysvar(&self, var_addr: *mut u8) -> u64 {
        unsafe { getter("sol_get_rent_sysvar", var_addr) }
    }
    fn sol_log_data(&self, fields: &[&[u8]]) {
        log(request("sol_log_data", vec![("fields", Json::arr(fields.iter(), |f| rec::bytes(f)))]));
    }
    fn sol_set_return_data(&self, data: &[u8]) {
        log(request("sol_set_return_data", vec![("bytes", rec::bytes(data))]));
    }
}

fn state(stdout: &[u8]) -> Json {
    let s = STATE.lock().unwrap();
    Json::obj([
        ("stubs", Json::obj([("replies", Json::arr(s.0.iter(), |r| r.json())), ("log", Json::Arr(s.1.clone()))])),
        ("stdout", rec::bytes(stdout)),
    ])
}

/// One host case: install the stubs and the script, capture standard output, run `f`.
pub fn host_case<T>(
    c: &mut Corpus,
    id: String,
    function: &'static str,
    args: Json,
    replies: Vec<StubReply>,
    f: impl FnOnce() -> T,
    enc: impl Fn(&T) -> Json,
) {
    let before = Json::obj([
        ("stubs", Json::obj([("replies", Json::arr(replies.iter(), |r| r.json())), ("log", Json::Arr(vec![]))])),
        ("stdout", rec::bytes(&[])),
    ]);
    let outcome = conformance_shim::case(&Script::new(vec![]), move || {
        program_stubs::set_syscall_stubs(Box::new(RecordingStubs));
        *STATE.lock().unwrap() = (replies.into_iter().collect(), Vec::new());
        let buf = Arc::new(Mutex::new(Vec::new()));
        let old = std::io::set_output_capture(Some(buf.clone()));
        let result = rec::catch(f);
        std::io::set_output_capture(old);
        let out = buf.lock().unwrap().clone();
        match result {
            Ok(v) => rec::returned(enc(&v), state(&out)),
            Err(reason) => rec::unwound(reason, state(&out)),
        }
    });
    c.push(Record { id, function, generics: vec![], layout: None, state: before, args, outcome, observed: None });
}
