//! `anchor_lang::error`: `From<AnchorError>`, `with_pubkeys`, `with_values`.
//!
//! Inputs own their Strings and Box; identities and liveness come from the
//! tracking allocator (`track`). `with_values` takes two scripted operands
//! whose `Display` and `Drop` log and may panic.

use std::cell::RefCell;
use std::fmt;

use anchor_lang::error::{AnchorError, ComparedValues, Error, ErrorOrigin, ProgramErrorWithOrigin, Source};
use anchor_lang::prelude::Pubkey;
use anchor_lang::solana_program::program_error::ProgramError;
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim as shim;

use crate::enc::{self, Heap};
use crate::track;

fn s(t: &str) -> String {
    t.to_string()
}

fn anchor(name: &str, code: u32, msg: &str, origin: Option<ErrorOrigin>, compared: Option<ComparedValues>) -> AnchorError {
    AnchorError { error_name: s(name), error_code_number: code, error_msg: s(msg), error_origin: origin, compared_values: compared }
}

fn program(e: ProgramError, origin: Option<ErrorOrigin>, compared: Option<ComparedValues>) -> Error {
    Error::ProgramError(Box::new(ProgramErrorWithOrigin { program_error: e, error_origin: origin, compared_values: compared }))
}

fn pk(n: u8) -> Pubkey {
    Pubkey::new_from_array([n; 32])
}

fn src(line: u32) -> Option<ErrorOrigin> {
    Some(ErrorOrigin::Source(Source { filename: "programs/vault/src/lib.rs", line }))
}

fn account_name(n: &str) -> Option<ErrorOrigin> {
    Some(ErrorOrigin::AccountName(s(n)))
}

fn values(l: &str, r: &str) -> Option<ComparedValues> {
    Some(ComparedValues::Values((s(l), s(r))))
}

fn pubkeys(l: u8, r: u8) -> Option<ComparedValues> {
    Some(ComparedValues::Pubkeys((pk(l), pk(r))))
}

const FROM: &str = "<anchor_lang::error::Error as core::convert::From<anchor_lang::error::AnchorError>>::from";
const WITH_PUBKEYS: &str = "anchor_lang::error::Error::with_pubkeys";
const WITH_VALUES: &str = "anchor_lang::error::Error::with_values";
const OPERAND: &str = "conformance_anchor::errors::Operand";

fn record(c: &mut Corpus, id: String, function: &'static str, generics: Vec<(&'static str, String)>, state: Json, args: Json, outcome: Json) {
    c.push(Record { id, function, generics, layout: None, state, args, outcome, observed: None });
}

fn from_anchor_cases() -> Vec<(&'static str, AnchorError)> {
    vec![
        ("plain", anchor("ConstraintRaw", 2003, "A raw constraint was violated", None, None)),
        ("source+pubkeys", anchor("AccountOwnedByWrongProgram", 3007, "The given account is owned by a different program than expected", src(42), pubkeys(1, 2))),
        ("account_name+values", anchor("ConstraintHasOne", 2001, "A has one constraint was violated", account_name("vault"), values("left side", "right side"))),
        ("account_name", anchor("RequireViolated", 2500, "A require expression was violated", account_name("authority"), None)),
        ("code_zero+unicode", anchor("InstructionMissing", 0, "8 byte instruction identifier not provided — ü", None, values("x", "yy"))),
        ("code_max", anchor("Custom", u32::MAX, "custom error", src(u32::MAX), None)),
    ]
}

fn record_from_anchor(c: &mut Corpus) {
    for (label, ae) in from_anchor_cases() {
        let mut heap = Heap::default();
        heap.add_anchor_error(&ae);
        let mut state: Vec<(&str, Json)> = heap.state_before();
        let args = Json::obj([("error", heap.anchor_payload(&ae, &track::Log::default()))]);
        let ae = std::mem::ManuallyDrop::new(ae);
        let outcome = shim::case(&shim::Script::new(vec![]), || {
            let ae = std::mem::ManuallyDrop::into_inner(ae);
            let (r, log) = track::tracked(|| Error::from(ae));
            let e = r.expect("From<AnchorError> panicked");
            let obs = heap.error_obs(&e, &log);
            let mut after = heap.state_after(&log);
            after.push(("syscalls", shim::state()));
            std::mem::forget(e);
            rec::returned(obs, Json::Obj(after.into_iter().map(|(k, v)| (k.to_string(), v)).collect()))
        });
        state.push(("syscalls", shim::Script::new(vec![]).state_before()));
        record(c, format!("from_anchor/{label}"), FROM, vec![], Json::Obj(state.into_iter().map(|(k, v)| (k.to_string(), v)).collect()), args, outcome);
    }
}

fn input_errors() -> Vec<(&'static str, Error)> {
    vec![
        ("anchor", Error::from(anchor("ConstraintSeeds", 2006, "A seeds constraint was violated", None, None))),
        ("anchor+values", Error::from(anchor("ConstraintRaw", 2003, "A raw constraint was violated", None, values("10", "20")))),
        ("anchor+pubkeys", Error::from(anchor("ConstraintAddress", 2012, "An address constraint was violated", src(7), pubkeys(3, 4)))),
        ("anchor+account_name+values", Error::from(anchor("ConstraintMut", 2000, "A mut constraint was violated", account_name("pool"), values("a", "b")))),
        ("program", program(ProgramError::InvalidArgument, None, None)),
        ("program_custom+source+values", program(ProgramError::Custom(7), src(99), values("lhs", "rhs"))),
        ("program+account_name+pubkeys", program(ProgramError::AccountBorrowFailed, account_name("mint"), pubkeys(5, 6))),
    ]
}

fn obj(fields: Vec<(&str, Json)>) -> Json {
    Json::Obj(fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
}

fn record_with_pubkeys(c: &mut Corpus) {
    for (label, e) in input_errors() {
        for (kl, kr) in [(8u8, 9u8), (0, 0)] {
            let mut heap = Heap::default();
            let b = heap.add_error(&e, true);
            let mut state = heap.state_before();
            state.push(("syscalls", shim::Script::new(vec![]).state_before()));
            let args = Json::obj([("error", b.into()), ("left", enc::key(&pk(kl))), ("right", enc::key(&pk(kr)))]);
            // A bitwise copy for the child; the parent never drops it.
            let e2 = std::mem::ManuallyDrop::new(unsafe { std::ptr::read(&e) });
            let outcome = shim::case(&shim::Script::new(vec![]), || {
                let e2 = std::mem::ManuallyDrop::into_inner(e2);
                let (r, log) = track::tracked(|| e2.with_pubkeys((pk(kl), pk(kr))));
                let e = r.expect("with_pubkeys panicked");
                let obs = heap.error_obs(&e, &log);
                let mut after = heap.state_after(&log);
                after.push(("syscalls", shim::state()));
                rec::returned(obs, obj(after))
            });
            record(c, format!("with_pubkeys/{label}/{kl}_{kr}"), WITH_PUBKEYS, vec![], obj(state), args, outcome);
        }
        std::mem::forget(e);
    }
}

// ---------------------------------------------------------------------------
// with_values: scripted operands
// ---------------------------------------------------------------------------

thread_local! {
    static LOG: RefCell<Vec<Json>> = const { RefCell::new(Vec::new()) };
}

fn log_event(kind: &str, tag: &str) {
    track::untracked(|| LOG.with(|l| l.borrow_mut().push(Json::Obj(vec![(kind.to_string(), tag.into())]))));
}

fn log_state() -> Json {
    LOG.with(|l| Json::Arr(l.borrow().clone()))
}

/// `Display` writes `text`, or panics with `"display <tag>"` if it is `None`;
/// `Drop` panics with `"drop <tag>"` if `drop_panics`. Both are logged.
pub struct Operand {
    tag: &'static str,
    text: Option<&'static str>,
    drop_panics: bool,
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        log_event("display", self.tag);
        match self.text {
            Some(t) => f.write_str(t),
            None => panic!("display {}", self.tag),
        }
    }
}

impl Drop for Operand {
    fn drop(&mut self) {
        log_event("drop", self.tag);
        if self.drop_panics {
            panic!("drop {}", self.tag);
        }
    }
}

impl Operand {
    fn json(&self) -> Json {
        Json::obj([
            ("tag", self.tag.into()),
            ("text", match self.text { Some(t) => t.into(), None => Json::Null }),
            ("drop_panics", self.drop_panics.into()),
        ])
    }
}

fn op(tag: &'static str, text: Option<&'static str>, drop_panics: bool) -> Operand {
    Operand { tag, text, drop_panics }
}

fn record_with_values(c: &mut Corpus) {
    let scripts: Vec<(&str, fn() -> (Operand, Operand))> = vec![
        ("ok", || (op("L", Some("12"), false), op("R", Some("34"), false))),
        ("ok_long", || (op("L", Some("a much longer left operand text"), false), op("R", Some("-1"), false))),
        ("empty_left", || (op("L", Some(""), false), op("R", Some("right"), false))),
        ("left_display_panics", || (op("L", None, false), op("R", Some("34"), false))),
        ("right_display_panics", || (op("L", Some("12"), false), op("R", None, false))),
        ("left_drop_panics", || (op("L", Some("12"), true), op("R", Some("34"), false))),
        ("right_drop_panics", || (op("L", Some("12"), false), op("R", Some("34"), true))),
    ];
    let generics = vec![("impl ToString (0)", OPERAND.to_string()), ("impl ToString (1)", OPERAND.to_string())];
    for (elabel, e) in input_errors() {
        for (slabel, script) in &scripts {
            let mut heap = Heap::default();
            let b = heap.add_error(&e, true);
            let (l, r) = script();
            let mut state = heap.state_before();
            state.push(("log", Json::Arr(vec![])));
            state.push(("syscalls", shim::Script::new(vec![]).state_before()));
            let args = Json::obj([("error", b.into()), ("left", l.json()), ("right", r.json())]);
            // Bitwise copies for the child; the parent never drops them.
            let e2 = std::mem::ManuallyDrop::new(unsafe { std::ptr::read(&e) });
            let operands = std::mem::ManuallyDrop::new((l, r));
            let outcome = shim::case(&shim::Script::new(vec![]), || {
                let e2 = std::mem::ManuallyDrop::into_inner(e2);
                let (l, r) = std::mem::ManuallyDrop::into_inner(operands);
                let (res, log) = track::tracked(|| e2.with_values((l, r)));
                let mut after = heap.state_after(&log);
                after.push(("log", log_state()));
                after.push(("syscalls", shim::state()));
                match res {
                    Ok(e) => {
                        let obs = heap.error_obs(&e, &log);
                        rec::returned(obs, obj(after))
                    }
                    Err(reason) => rec::unwound(reason, obj(after)),
                }
            });
            record(c, format!("with_values/{elabel}/{slabel}"), WITH_VALUES, generics.clone(), obj(state), args, outcome);
        }
        std::mem::forget(e);
    }
}

pub fn record_all(c: &mut Corpus) {
    record_from_anchor(c);
    record_with_pubkeys(c);
    record_with_values(c);
}
