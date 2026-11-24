//! Actual owned-error conversions and diagnostics, including consuming callbacks.
use crate::{
    enc::{self, Heap},
    identities, track,
};
use anchor_lang::error::{
    AnchorError, ComparedValues, Error, ErrorOrigin, ProgramErrorWithOrigin, Source,
};
use anchor_lang::prelude::Pubkey;
use anchor_lang::solana_program::program_error::ProgramError;
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim as shim;
use std::{cell::RefCell, fmt};

#[cfg(feature = "v112")]
macro_rules! item {
    ($tail:literal) => {
        concat!("anchor_lang_error::", $tail)
    };
}
#[cfg(not(feature = "v112"))]
macro_rules! item {
    ($tail:literal) => {
        concat!("anchor_lang::error::", $tail)
    };
}

thread_local! { static EVENTS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) }; }
pub fn event(text: &str) {
    track::untracked(|| EVENTS.with(|e| e.borrow_mut().push(text.to_string())));
}
pub fn events() -> Json {
    EVENTS.with(|e| Json::arr(e.borrow().iter(), |s| s.as_str().into()))
}
pub fn reset() {
    EVENTS.with(|e| e.borrow_mut().clear());
}
/// The three deliberate double-panic cases exercise the Rust cleanup abort.
/// Only the exact synthetic cleanup-abort message from the compiler is exempted
/// from the shim unsafe-precondition fault classification. All originating
/// user panics and all other non-unwinding panics reach the original hook.
fn cleanup_abort_allowed(expected: &[&str], actual: &[String], message: Option<&str>) -> bool {
    message == Some("panic in a destructor during cleanup")
        && expected.len() == actual.len()
        && expected
            .iter()
            .zip(actual)
            .all(|(left, right)| *left == right)
}
fn expected_cleanup_abort(expected: &'static [&'static str]) {
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let payload = info.payload();
        let text = payload
            .downcast_ref::<&str>()
            .copied()
            .or_else(|| payload.downcast_ref::<String>().map(String::as_str));
        let expected_abort =
            EVENTS.with(|events| cleanup_abort_allowed(expected, &events.borrow(), text));
        if expected_abort {
            return;
        }
        previous(info);
    }));
}
fn cleanup_hook_controls() {
    let expected = ["display left", "display right", "drop left", "drop right"];
    let full: Vec<String> = expected.iter().map(|s| (*s).to_string()).collect();
    let message = Some("panic in a destructor during cleanup");
    assert!(cleanup_abort_allowed(&expected, &full, message));
    assert!(!cleanup_abort_allowed(&expected, &[], message));
    assert!(!cleanup_abort_allowed(&expected, &full[..3], message));
    assert!(!cleanup_abort_allowed(
        &expected,
        &full,
        Some("panic in a function that cannot unwind")
    ));
}

pub fn obj(fields: Vec<(&str, Json)>) -> Json {
    Json::Obj(
        fields
            .into_iter()
            .map(|(k, v)| (k.to_string(), v))
            .collect(),
    )
}
pub fn record(
    c: &mut Corpus,
    id: String,
    function: &'static str,
    state: Json,
    args: Json,
    outcome: Json,
) {
    if !crate::identities::FUNCTIONS.contains(&function) {
        return;
    }
    if std::env::var_os("CONFORMANCE_DEBUG").is_some() {
        eprintln!("recorded {id}");
    }
    c.push(Record {
        id,
        function,
        generics: vec![],
        layout: None,
        state,
        args,
        outcome,
        observed: None,
    });
}
pub fn empty_before() -> Json {
    obj(vec![
        ("strings", Json::Arr(vec![])),
        ("boxes", Json::Arr(vec![])),
        ("callbacks", Json::Arr(vec![])),
        ("syscalls", shim::Script::new(vec![]).state_before()),
    ])
}
pub fn before(heap: &Heap) -> Json {
    let mut state = heap.state_before();
    state.extend([
        ("callbacks", Json::Arr(vec![])),
        ("syscalls", shim::Script::new(vec![]).state_before()),
    ]);
    obj(state)
}
pub fn after(heap: &Heap, log: &track::Log) -> Json {
    let mut state = heap.state_after(log);
    state.extend([("callbacks", events()), ("syscalls", shim::state())]);
    obj(state)
}
pub fn pk(byte: u8) -> Pubkey {
    Pubkey::new_from_array([byte; 32])
}
pub fn anchor(code: u32, compared: bool, origin: bool) -> AnchorError {
    AnchorError {
        error_name: "ExampleName".to_string(),
        error_code_number: code,
        error_msg: "diagnostic ü".to_string(),
        error_origin: if origin {
            Some(ErrorOrigin::AccountName("original account".to_string()))
        } else {
            None
        },
        compared_values: if compared {
            Some(ComparedValues::Values((
                "old left".to_string(),
                "old right".to_string(),
            )))
        } else {
            None
        },
    }
}
pub fn error(program: bool, compared: bool, origin: bool) -> Error {
    if !program {
        return Error::from(anchor(2003, compared, origin));
    }
    #[cfg(feature = "legacy")]
    let program_error = ProgramError::BorshIoError("original IO diagnostic".to_string());
    #[cfg(not(feature = "legacy"))]
    let program_error = ProgramError::Custom(17);
    let payload = ProgramErrorWithOrigin {
        program_error,
        error_origin: if origin {
            Some(ErrorOrigin::AccountName("original account".to_string()))
        } else {
            None
        },
        compared_values: if compared {
            Some(ComparedValues::Values((
                "old left".to_string(),
                "old right".to_string(),
            )))
        } else {
            None
        },
    };
    #[cfg(feature = "v027")]
    {
        Error::ProgramError(payload)
    }
    #[cfg(not(feature = "v027"))]
    {
        Error::ProgramError(Box::new(payload))
    }
}
fn finish(heap: &Heap, r: Result<Error, String>, log: &track::Log) -> Json {
    match r {
        Ok(e) => {
            let result = heap.error_obs(&e, log);
            std::mem::forget(e);
            rec::returned(result, after(heap, log))
        }
        Err(reason) => rec::unwound(reason, after(heap, log)),
    }
}
#[derive(Debug)]
struct Operand {
    label: &'static str,
    text: &'static str,
    display_panic: bool,
    drop_panic: bool,
}
impl fmt::Display for Operand {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        event(&format!("display {}", self.label));
        if self.display_panic {
            panic!("display {}", self.label);
        }
        out.write_str(self.text)
    }
}
impl Drop for Operand {
    fn drop(&mut self) {
        event(&format!("drop {}", self.label));
        if self.drop_panic {
            panic!("drop {}", self.label);
        }
    }
}
impl std::error::Error for Operand {}
#[derive(Debug)]
struct Name {
    panic: bool,
}
impl fmt::Display for Name {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        event("display name");
        if self.panic {
            panic!("display name");
        }
        out.write_str("new account")
    }
}
impl Drop for Name {
    fn drop(&mut self) {
        event("drop name");
    }
}

fn code_cases(c: &mut Corpus) {
    for (index, code) in crate::codes::all().into_iter().enumerate() {
        let output = shim::case(&shim::Script::new(vec![]), || {
            reset();
            let (r, log) = track::tracked(|| code.name());
            let text = r.expect("fixed code name");
            let result = Json::obj([
                ("text", text.as_str().into()),
                ("owned", (text.capacity() > 0).into()),
            ]);
            std::mem::forget(text);
            rec::returned(result, after(&Heap::default(), &log))
        });
        record(
            c,
            format!("code_name/{index}"),
            item!("ErrorCode::name"),
            empty_before(),
            Json::obj([("index", index.into())]),
            output,
        );
    }
    for (index, code) in crate::codes::all().into_iter().enumerate() {
        let output = shim::case(&shim::Script::new(vec![]), || {
            reset();
            let (r, log) = track::tracked(|| Error::from(code));
            finish(&Heap::default(), r, &log)
        });
        record(
            c,
            format!("from_code/{index}"),
            identities::FROM_CODE,
            empty_before(),
            Json::obj([("index", index.into())]),
            output,
        );
    }
}
fn from_cases(c: &mut Corpus) {
    for variant in 0..4 {
        let value = anchor(
            if variant == 3 { u32::MAX } else { 2003 },
            variant & 1 != 0,
            variant & 2 != 0,
        );
        let mut heap = Heap::default();
        heap.add_anchor_error(&value);
        let state = before(&heap);
        let args = Json::obj([("error", heap.anchor_payload(&value, &track::Log::default()))]);
        let output = shim::case(&shim::Script::new(vec![]), || {
            reset();
            let (r, log) = track::tracked(|| Error::from(value));
            finish(&heap, r, &log)
        });
        record(
            c,
            format!("from_anchor/{variant}"),
            identities::FROM_ANCHOR,
            state,
            args,
            output,
        );
    }
    let mut programs = vec![
        ProgramError::Custom(0),
        ProgramError::Custom(u32::MAX),
        ProgramError::InvalidArgument,
    ];
    #[cfg(feature = "legacy")]
    programs.push(ProgramError::BorshIoError("owned input".to_string()));
    #[cfg(not(feature = "legacy"))]
    programs.push(ProgramError::BorshIoError);
    for (index, value) in programs.into_iter().enumerate() {
        let heap = {
            #[cfg(feature = "legacy")]
            {
                let mut heap = Heap::default();
                if let ProgramError::BorshIoError(s) = &value {
                    heap.texts.push(s.clone());
                    heap.strings.push(enc::string_addr(s));
                }
                heap
            }
            #[cfg(not(feature = "legacy"))]
            {
                Heap::default()
            }
        };
        let state = before(&heap);
        let args = Json::obj([("error", enc::program_error(&value))]);
        let output = shim::case(&shim::Script::new(vec![]), || {
            reset();
            let (r, log) = track::tracked(|| Error::from(value));
            finish(&heap, r, &log)
        });
        record(
            c,
            format!("from_program/{index}"),
            identities::FROM_PROGRAM,
            state,
            args,
            output,
        );
    }
}
fn update_cases(c: &mut Corpus) {
    for program in [false, true] {
        for occupied in [false, true] {
            for operation in ["pubkeys", "source", "name", "name_panic"] {
                let input = error(program, occupied, occupied);
                let mut heap = Heap::default();
                heap.add_error(&input, true);
                let state = before(&heap);
                let args = Json::obj([
                    ("error", heap.payload(&input, &track::Log::default())),
                    ("operation", operation.into()),
                ]);
                let output = shim::case(&shim::Script::new(vec![]), || {
                    reset();
                    let (r, log) = track::tracked(|| match operation {
                        "pubkeys" => input.with_pubkeys((pk(3), pk(7))),
                        "source" => input.with_source(Source {
                            filename: "src/example.rs",
                            line: u32::MAX,
                        }),
                        "name" => input.with_account_name(Name { panic: false }),
                        "name_panic" => input.with_account_name(Name { panic: true }),
                        _ => unreachable!(),
                    });
                    finish(&heap, r, &log)
                });
                let function = match operation {
                    "pubkeys" => item!("Error::with_pubkeys"),
                    "source" => item!("Error::with_source"),
                    _ => item!("Error::with_account_name"),
                };
                record(
                    c,
                    format!("update/{program}/{occupied}/{operation}"),
                    function,
                    state,
                    args,
                    output,
                );
            }
        }
    }
    for program in [false, true] {
        for mode in 0..8 {
            let input = error(program, true, true);
            let mut heap = Heap::default();
            heap.add_error(&input, true);
            let state = before(&heap);
            let args = Json::obj([
                ("error", heap.payload(&input, &track::Log::default())),
                ("mode", mode.into()),
            ]);
            let output = shim::case(&shim::Script::new(vec![]), || {
                reset();
                if mode == 5 {
                    expected_cleanup_abort(&["display left", "drop left", "drop right"]);
                }
                if mode == 6 || mode == 7 {
                    expected_cleanup_abort(&[
                        "display left",
                        "display right",
                        "drop left",
                        "drop right",
                    ]);
                }
                let left = Operand {
                    label: "left",
                    text: "11",
                    display_panic: mode == 1 || mode == 5,
                    drop_panic: mode == 4 || mode == 6 || mode == 7,
                };
                let right = Operand {
                    label: "right",
                    text: "22",
                    display_panic: mode == 2 || mode == 6,
                    drop_panic: mode == 3 || mode == 5 || mode == 7,
                };
                let (r, log) = track::tracked(|| input.with_values((left, right)));
                finish(&heap, r, &log)
            });
            record(
                c,
                format!("with_values/{program}/{mode}"),
                item!("Error::with_values"),
                state,
                args,
                output,
            );
        }
    }
}
fn equality_cases(c: &mut Corpus) {
    for mode in 0..5 {
        let left = error(mode >= 2, false, false);
        let right = if mode == 0 {
            Error::from(anchor(2003, true, true))
        } else if mode == 1 {
            Error::from(anchor(2004, false, false))
        } else if mode == 2 {
            error(true, true, true)
        } else if mode == 3 {
            Error::from(anchor(2003, false, false))
        } else {
            #[cfg(feature = "legacy")]
            {
                Error::from(ProgramError::BorshIoError("different text".to_string()))
            }
            #[cfg(not(feature = "legacy"))]
            {
                Error::from(ProgramError::Custom(18))
            }
        };
        let mut heap = Heap::default();
        heap.add_error(&left, true);
        heap.add_error(&right, true);
        let state = before(&heap);
        let args = Json::obj([
            ("left", enc::error_value(&left)),
            ("right", enc::error_value(&right)),
        ]);
        let output = shim::case(&shim::Script::new(vec![]), || {
            reset();
            let (r, log) = track::tracked(|| left == right);
            rec::returned(r.expect("equality").into(), after(&heap, &log))
        });
        record(
            c,
            format!("eq/{mode}"),
            identities::EQUAL,
            state,
            args,
            output,
        );
    }
}
fn io_cases(c: &mut Corpus) {
    for mode in 0..4 {
        let output = shim::case(&shim::Script::new(vec![]), || {
            let input = std::io::Error::new(
                std::io::ErrorKind::Other,
                Operand {
                    label: "io",
                    text: "payload text",
                    display_panic: mode == 1 || mode == 3,
                    drop_panic: mode == 2 || mode == 3,
                },
            );
            reset();
            if mode == 3 {
                expected_cleanup_abort(&["display io", "drop io"]);
            }
            let (r, log) = track::tracked(|| Error::from(input));
            finish(&Heap::default(), r, &log)
        });
        record(
            c,
            format!("from_io/{mode}"),
            identities::FROM_IO,
            empty_before(),
            Json::obj([("mode", mode.into())]),
            output,
        );
    }
}
fn log_cases(c: &mut Corpus) {
    for program in [false, true] {
        for origin in 0..3 {
            for compare in 0..3 {
                let mut input = error(program, compare == 1, origin == 1);
                if origin == 2 {
                    input = input.with_source(Source {
                        filename: "src/example.rs",
                        line: 4294967295,
                    });
                }
                if compare == 2 {
                    input = input.with_pubkeys((pk(3), pk(7)));
                }
                let args = Json::obj([("error", enc::error_value(&input))]);
                let output = shim::case(&shim::Script::new(vec![]), || {
                    input.log();
                    rec::returned(Json::Null, Json::obj([("syscalls", shim::state())]))
                });
                record(
                    c,
                    format!("log/{program}/{origin}/{compare}"),
                    item!("Error::log"),
                    Json::obj([("syscalls", shim::Script::new(vec![]).state_before())]),
                    args,
                    output,
                );
            }
        }
    }
}
pub fn record_all(c: &mut Corpus) {
    cleanup_hook_controls();
    code_cases(c);
    from_cases(c);
    update_cases(c);
    equality_cases(c);
    io_cases(c);
    log_cases(c);
}
