//! Observable callback and owner identities for the SDK value conformance cases.
use conformance_recorder::{self as rec, Json};
use std::cell::RefCell;

#[derive(Clone, Copy)]
pub struct Plan {
    pub comparison: u8,
    pub default: u8,
    pub query: u8,
    pub is_null: bool,
}
impl Plan {
    pub const NORMAL: Self = Self { comparison: 0, default: 0, query: 0, is_null: false };
}
thread_local! {
    static EVENTS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
    static LIVE: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    static PLAN: RefCell<Plan> = const { RefCell::new(Plan::NORMAL) };
}
pub fn reset(plan: Plan) {
    EVENTS.with(|s| s.borrow_mut().clear());
    LIVE.with(|s| s.borrow_mut().clear());
    PLAN.with(|s| *s.borrow_mut() = plan);
}
pub fn event(text: String) { EVENTS.with(|s| s.borrow_mut().push(text)); }
pub fn state() -> Json {
    Json::obj([
        ("events", Json::Arr(EVENTS.with(|s| s.borrow().iter().map(|x| Json::from(x.as_str())).collect()))),
        ("live", Json::Arr(LIVE.with(|s| s.borrow().iter().copied().map(Json::from).collect()))),
    ])
}
pub fn initial(ids: &[u64]) -> Json {
    Json::obj([("events", Json::Arr(vec![])), ("live", Json::Arr(ids.iter().copied().map(Json::from).collect()))])
}
pub fn assert_initial(ids: &[u64]) { assert_eq!(state().to_text(), initial(ids).to_text()); }
pub fn mode(mode: u8, message: String) {
    match mode { 0 => (), 1 => panic!("{message}"), 2 => std::process::exit(73), _ => panic!("invalid script") }
}
#[derive(Debug)]
pub struct Tracked { pub id: u64, pub value: u64, pub drop_mode: u8 }
impl Tracked {
    pub fn new(id: u64, value: u64, drop_mode: u8) -> Self {
        LIVE.with(|s| { let mut s = s.borrow_mut(); assert!(!s.contains(&id)); s.push(id); s.sort_unstable(); });
        Self { id, value, drop_mode }
    }
    pub fn json(&self) -> Json { tracked_json(self.id, self.value, self.drop_mode) }
    pub fn query(&self) -> bool {
        event(format!("query:{}", self.id));
        let plan = PLAN.with(|s| *s.borrow());
        mode(plan.query, "query".into());
        plan.is_null
    }
}
pub fn tracked_json(id: u64, value: u64, drop_mode: u8) -> Json {
    Json::obj([("id", id.into()), ("value", value.into()), ("drop_mode", (drop_mode as u64).into())])
}
impl Drop for Tracked {
    fn drop(&mut self) {
        event(format!("drop:{}", self.id));
        LIVE.with(|s| { let mut s = s.borrow_mut(); let i = s.iter().position(|x| *x == self.id).expect("one live owner"); s.remove(i); });
        mode(self.drop_mode, format!("drop {}", self.id));
    }
}
impl PartialEq for Tracked {
    fn eq(&self, other: &Self) -> bool {
        event(format!("eq:{}:{}", self.id, other.id));
        mode(PLAN.with(|s| s.borrow().comparison), "eq".into());
        self.value == other.value
    }
}
impl Default for Tracked {
    fn default() -> Self {
        event("default".into());
        mode(PLAN.with(|s| s.borrow().default), "default".into());
        Self::new(4, 42, 0)
    }
}
pub struct Query { pub id: u64, pub value: u64 }
impl PartialEq<Tracked> for Query {
    fn eq(&self, other: &Tracked) -> bool {
        event(format!("contains:{}:{}", self.id, other.id));
        mode(PLAN.with(|s| s.borrow().comparison), "contains".into());
        self.value < other.value
    }
}
pub fn finish<T>(result: Result<T, String>, encode: impl FnOnce(&T) -> Json) -> Json {
    match result {
        Ok(value) => { let j = encode(&value); let s = state(); std::mem::forget(value); rec::returned(j, s) }
        Err(reason) => rec::unwound(reason, state()),
    }
}
pub fn some(value: Json) -> Json { Json::obj([("some", value)]) }

// Isolate actual panic-abort and callback process exits without interposing
// the `abort` symbol of the Solana syscall shim. A double unwind is therefore the
// native Rust runtime process exit, not a synthetic successful observation.
unsafe extern "C" {
    fn pipe(fds: *mut i32) -> i32;
    fn fork() -> i32;
    fn close(fd: i32) -> i32;
    fn read(fd: i32, buf: *mut u8, len: usize) -> isize;
    fn write(fd: i32, buf: *const u8, len: usize) -> isize;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
    fn _exit(code: i32) -> !;
}
pub fn case(f: impl FnOnce() -> Json) -> Json {
    let mut fds=[0;2];assert_eq!(unsafe {pipe(fds.as_mut_ptr())},0);
    let pid=unsafe {fork()};assert!(pid>=0);
    if pid==0 {
        unsafe {close(fds[0]);}
        std::panic::set_hook(Box::new(|_|{}));
        let value=match rec::catch(f) {Ok(x)=>x,Err(e)=>rec::unwound(e,state())};
        let text=value.to_text();let mut sent=0;
        while sent<text.len() {
            let n=unsafe {write(fds[1],text.as_ptr().add(sent),text.len()-sent)};
            if n<=0 {unsafe {_exit(120)}}
            sent+=n as usize;
        }
        unsafe {_exit(0)}
    }
    unsafe {close(fds[1]);}
    let mut bytes=Vec::new();let mut buf=[0;4096];
    loop {let n=unsafe {read(fds[0],buf.as_mut_ptr(),buf.len())};if n<=0 {break;}bytes.extend_from_slice(&buf[..n as usize]);}
    unsafe {close(fds[0]);}
    let mut status=0;assert_eq!(unsafe {waitpid(pid,&mut status,0)},pid);
    if status==0 && !bytes.is_empty() {Json::Raw(String::from_utf8(bytes).expect("child JSON"))}
    else {Json::obj([("exit","terminated".into()),("reason","process".into()),("detail",Json::obj([("status",(status as u64).into())]))])}
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn child_returns_exact_json() {
        assert_eq!(case(||rec::returned(17u64.into(),Json::Null)).to_text(),rec::returned(17u64.into(),Json::Null).to_text());
    }
    #[test]
    fn deliberate_process_exit_is_terminal() {
        assert_eq!(case(||std::process::exit(73)).to_text(),Json::obj([("exit","terminated".into()),("reason","process".into()),("detail",Json::obj([("status",18688u64.into())]))]).to_text());
    }
}
