use borsh::BorshSerialize;
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, Script};
use std::{cell::RefCell, io::{self, Write}};
use crate::{get_instance_packed_len, PACKED_LEN_FUNCTION, SERIALIZER_NAME};

thread_local! { static EVENTS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) }; }
fn event(s: String) { EVENTS.with(|e| e.borrow_mut().push(s)); }
fn events() -> Json { EVENTS.with(|e| Json::arr(e.borrow().iter(), |s| s.clone().into())) }
#[derive(Clone)]
enum Op { Write(Vec<u8>), WriteAll(Vec<u8>), Flush, Fail, Panic, Abort }
fn op_json(op: &Op) -> Json { match op {
    Op::Write(b) => Json::obj([("write", rec::bytes(b))]),
    Op::WriteAll(b) => Json::obj([("write_all", rec::bytes(b))]),
    Op::Flush => "flush".into(), Op::Fail => "fail".into(), Op::Panic => "panic".into(), Op::Abort => "abort".into(),
} }
struct Guard;
impl Drop for Guard { fn drop(&mut self) { event("drop".into()); } }
pub struct Probe(Vec<Op>);
impl BorshSerialize for Probe {
    fn serialize<W: Write>(&self, w: &mut W) -> io::Result<()> {
        event("enter".into());
        let _guard = Guard;
        for op in &self.0 { match op {
            Op::Write(b) => { let n = w.write(b)?; event(format!("write:{n}")); }
            Op::WriteAll(b) => { w.write_all(b)?; event(format!("write_all:{}", b.len())); }
            Op::Flush => { w.flush()?; event("flush".into()); }
            Op::Fail => { event("fail".into()); return Err(io::Error::new(io::ErrorKind::Other, "serializer-error")); }
            Op::Panic => { event("panic".into()); panic!("serializer-panic"); }
            Op::Abort => { event("abort".into()); std::process::abort(); }
        } }
        Ok(())
    }
}
pub fn record(c: &mut Corpus) {
    let cases = vec![vec![], vec![Op::Flush], vec![Op::Write(vec![])], vec![Op::WriteAll(vec![])],
        vec![Op::Write(vec![1, 2]), Op::WriteAll(vec![3; 33]), Op::Flush, Op::Write(vec![4])],
        vec![Op::Fail], vec![Op::Write(vec![9; 17]), Op::Fail, Op::Write(vec![5])],
        vec![Op::Panic], vec![Op::WriteAll(vec![9; 17]), Op::Panic], vec![Op::Abort],
        vec![Op::Write(vec![9; 17]), Op::Abort]];
    for (i, ops) in cases.into_iter().enumerate() {
        let args = Json::arr(&ops, op_json);
        let p = Probe(ops);
        let outcome = shim::case(&Script::default(), || {
            EVENTS.with(|e| e.borrow_mut().clear());
            match rec::catch(|| get_instance_packed_len(&p)) {
                Ok(result) => rec::returned(match result { Ok(n) => rec::ok(n.into()), Err(e) => rec::err(rec::io_error(&e)) }, events()),
                Err(reason) => rec::unwound(reason, events()),
            }
        });
        c.push(Record { id: format!("packed-len-{i}"), function: PACKED_LEN_FUNCTION,
            generics: vec![("T", SERIALIZER_NAME.into())], layout: None, state: Json::Arr(vec![]), args, outcome, observed: None });
    }
}
