use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, Script};
use pinocchio_log::logger::{Logger, Log, Argument};
use std::{cell::RefCell, rc::Rc};
use core::mem::MaybeUninit;
const DEFAULT: &str = "<pinocchio_log::logger::Logger<BUFFER> as core::default::Default>::default";
const APPEND: &str = "pinocchio_log::logger::Logger::<BUFFER>::append";
const LOG: &str = "pinocchio_log::logger::Logger::<BUFFER>::log";
fn state<const N: usize>(logger: &Logger<N>, events: &[&str], syscalls: Json) -> Json {
    Json::obj([("bytes", rec::bytes(logger)), ("len", logger.len().into()), ("capacity", N.into()),
        ("events", Json::arr(events.iter(), |s| (*s).into())), ("syscalls", syscalls)])
}
fn push<const N: usize>(c: &mut Corpus, id: String, function: &'static str, target: Option<&str>, before: Json, args: Json, outcome: Json) {
    let mut generics = vec![("BUFFER", N.to_string())]; if let Some(ty) = target { generics.push(("T", ty.into())); }
    c.push(Record { id, function, generics, layout: None, state: before, args, outcome, observed: None });
}
fn default<const N: usize>(c: &mut Corpus) {
    let script = Script::default();
    let outcome = shim::case(&script, || { let value = Logger::<N>::default();
        rec::returned(state(&value, &[], shim::state()), Json::Null) });
    push::<N>(c, format!("default/{N}"), DEFAULT, None, Json::Null, Json::Null, outcome);
}
fn text<const N: usize>(c: &mut Corpus, label: &str, prefix: &str, value: &str) {
    let mut logger = Logger::<N>::default(); logger.append(prefix);
    let script = Script::default(); let before = state(&logger, &[], script.state_before());
    let outcome = shim::case(&script, || { let ptr = &logger as *const _ as usize;
        let next = logger.append(value); let same = next as *const _ as usize == ptr;
        rec::returned(Json::from(if same { 17usize } else { 0 }), state(&logger, &[], shim::state())) });
    push::<N>(c, format!("append/str/{N}/{label}"), APPEND, Some("&str"), before,
        Json::obj([("receiver", 17usize.into()), ("kind", "str".into()), ("value", rec::bytes(value.as_bytes()))]), outcome);
}
fn number<const N: usize>(c: &mut Corpus, value: u64) {
    let mut logger = Logger::<N>::default(); let script = Script::default(); let before = state(&logger, &[], script.state_before());
    let outcome = shim::case(&script, || { let ptr = &logger as *const _ as usize;
        let same = logger.append(value) as *const _ as usize == ptr;
        rec::returned(Json::from(if same { 17usize } else { 0 }), state(&logger, &[], shim::state())) });
    push::<N>(c, format!("append/u64/{N}/{value}"), APPEND, Some("u64"), before,
        Json::obj([("receiver", 17usize.into()), ("kind", "u64".into()), ("value", value.into())]), outcome);
}
struct Probe { events: Rc<RefCell<Vec<&'static str>>>, write_panics: bool, drop_panics: bool, terminal: bool }
unsafe impl Log for Probe {
    fn write_with_args(&self, buffer: &mut [MaybeUninit<u8>], args: &[Argument]) -> usize {
        assert!(args.is_empty()); self.events.borrow_mut().push("write");
        if let Some(first) = buffer.first_mut() { first.write(42); }
        if self.terminal { unsafe { shim::sol_panic_(b"formatter".as_ptr(), 9, 7, 3) } }
        if self.write_panics { panic!("formatter panic"); }
        usize::from(!buffer.is_empty())
    }
}
impl Drop for Probe { fn drop(&mut self) { self.events.borrow_mut().push("drop"); if self.drop_panics { panic!("operand drop"); } } }
fn probe<const N: usize>(c: &mut Corpus, label: &str, full: bool, write_panics: bool, drop_panics: bool, terminal: bool) {
    let mut logger = Logger::<N>::default(); if full { logger.append("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"); }
    let events = Rc::new(RefCell::new(vec![])); let script = Script::default(); let before = state(&logger, &events.borrow(), script.state_before());
    let outcome = shim::case(&script, || {
        let value = Probe { events: events.clone(), write_panics, drop_panics, terminal };
        let ptr = &logger as *const _ as usize;
        let result = rec::catch(|| logger.append(value) as *const _ as usize == ptr);
        match result {
            Ok(same) => rec::returned(Json::from(if same { 17usize } else { 0 }), state(&logger, &events.borrow(), shim::state())),
            Err(reason) => rec::unwound(reason, state(&logger, &events.borrow(), shim::state()))
        }
    });
    push::<N>(c, format!("append/probe/{N}/{label}"), APPEND, Some("Probe"), before,
        Json::obj([("receiver", 17usize.into()), ("kind", "probe".into()), ("write_panics", write_panics.into()),
            ("drop_panics", drop_panics.into()), ("terminal", terminal.into())]), outcome);
}
fn log<const N: usize>(c: &mut Corpus, label: &str, value: &str) {
    let mut logger = Logger::<N>::default(); logger.append(value);
    let script = Script::default(); let before = state(&logger, &[], script.state_before());
    let outcome = shim::case(&script, || { logger.log(); rec::returned(Json::Null, state(&logger, &[], shim::state())) });
    push::<N>(c, format!("log/{N}/{label}"), LOG, None, before, Json::Null, outcome);
}
pub fn corpus() -> Corpus {
    let mut c = Corpus::new("pinocchio_log_0_5_1", &[("pinocchio-log", "0.5.1")]);
    default::<0>(&mut c); default::<3>(&mut c); default::<200>(&mut c);
    text::<0>(&mut c,"empty_capacity","","ignored"); text::<1>(&mut c,"truncates","","abc");
    text::<3>(&mut c,"exact","","abc"); text::<4>(&mut c,"spare","","abc");
    text::<4>(&mut c,"prefix","ab","cd"); text::<4>(&mut c,"prefix_truncated","ab","cdef");
    text::<4>(&mut c,"full","abcd","anything"); text::<2>(&mut c,"utf8_split","","€");
    text::<200>(&mut c,"ordinary","amount=","ok");
    for n in [0, 1, 9, 10, 999, u64::MAX] { number::<5>(&mut c,n); number::<200>(&mut c,n); }
    number::<0>(&mut c,10); number::<1>(&mut c,10);
    probe::<0>(&mut c,"skipped",false,true,false,false); probe::<3>(&mut c,"full_drops",true,true,false,false);
    probe::<3>(&mut c,"ordinary",false,false,false,false); probe::<3>(&mut c,"write_unwind",false,true,false,false);
    probe::<3>(&mut c,"drop_unwind",false,false,true,false); probe::<3>(&mut c,"write_terminal",false,false,false,true);
    log::<0>(&mut c,"empty",""); log::<200>(&mut c,"ascii","hello"); log::<2>(&mut c,"non_utf8_prefix","€");
    c
}
