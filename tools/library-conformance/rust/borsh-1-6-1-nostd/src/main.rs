//! Records the provided `Write::write_all` from the borsh 1.6.1 no-std io module
//! (`src/nostd_io.rs` 545-560), the selected no-std implementation:
//! borsh without its `std` feature, where `borsh::io` is `nostd_io`.
//!
//! The writer is `ScriptedWriter`. It implements only the required `write` and
//! `flush`, so `write_all` is the provided method. Its `k`-th `write` call
//! answers the `k`-th scripted response, and every later call takes the whole
//! buffer. It logs each call with the bytes offered and the response. A
//! response is a count, an error, or a panic of the writer.

use borsh::io::{Error, ErrorKind, Write};
use conformance_recorder::{self as rec, Corpus, Json, Record};

/// `borsh::io` is `nostd_io`: its `Error::get_ref` returns the message as a
/// `&str`, where `std::io::Error::get_ref` returns a `dyn Error`, so this does
/// not compile when the borsh io module is `std::io`.
const _: fn(&Error) -> Option<&str> = Error::get_ref;

const FUNCTION: &str = "borsh::nostd_io::Write::write_all";
const WRITER: &str = "conformance_borsh_1_6_1_nostd::ScriptedWriter";

#[derive(Clone, Copy)]
enum Response {
    /// `Ok(n)`.
    Count(usize),
    /// `Err(Error::new(kind, message))`: its message is `message`.
    Custom(ErrorKind, &'static str),
    /// `Err(Error::from(kind))`: its message is the kind description.
    Simple(ErrorKind),
    /// The writer panics with this message.
    Panic(&'static str),
}

/// A no-std io error, as the recorder writes a `std::io::Error`: its kind
/// `Debug` name and its `Display` text.
fn error_json(e: &Error) -> Json {
    Json::obj([("kind", format!("{:?}", e.kind()).into()), ("message", e.to_string().into())])
}

impl Response {
    fn error(self) -> Error {
        match self {
            Response::Custom(kind, message) => Error::new(kind, message),
            Response::Simple(kind) => Error::from(kind),
            Response::Count(_) | Response::Panic(_) => unreachable!("not an error response"),
        }
    }

    fn json(self) -> Json {
        match self {
            Response::Count(n) => rec::ok(Json::from(n)),
            Response::Custom(..) | Response::Simple(_) => rec::err(error_json(&self.error())),
            Response::Panic(message) => Json::obj([("panic", message.into())]),
        }
    }
}

pub struct ScriptedWriter {
    script: Vec<Response>,
    calls: Vec<Json>,
}

impl ScriptedWriter {
    /// The writer state: every call it received, in order.
    fn state(&self) -> Json {
        Json::obj([("calls", Json::Arr(self.calls.clone()))])
    }
}

impl Write for ScriptedWriter {
    fn write(&mut self, buf: &[u8]) -> borsh::io::Result<usize> {
        let response = self.script.get(self.calls.len()).copied().unwrap_or(Response::Count(buf.len()));
        self.calls.push(Json::obj([
            ("op", "write".into()),
            ("bytes", rec::bytes(buf)),
            ("response", response.json()),
        ]));
        match response {
            Response::Count(n) => Ok(n),
            Response::Panic(message) => panic!("{message}"),
            error => Err(error.error()),
        }
    }

    /// Not called by `write_all`; logged so that a call is a mismatch.
    fn flush(&mut self) -> borsh::io::Result<()> {
        self.calls.push(Json::obj([("op", "flush".into())]));
        Ok(())
    }
}

/// Record `writer.write_all(buf)` with a fresh writer on `script`.
fn case(corpus: &mut Corpus, label: &str, script: &[Response], buf: &[u8]) {
    let mut writer = ScriptedWriter { script: script.to_vec(), calls: Vec::new() };
    let before = writer.state();
    let result = rec::catch(|| writer.write_all(buf));
    let after = writer.state();
    let outcome = match result {
        Ok(Ok(())) => rec::returned(rec::ok(Json::Null), after),
        Ok(Err(e)) => rec::returned(rec::err(error_json(&e)), after),
        Err(reason) => rec::unwound(reason, after),
    };
    corpus.push(Record {
        id: format!("write_all/{label}"),
        function: FUNCTION,
        generics: vec![("Self", WRITER.to_string())],
        layout: None,
        state: before,
        args: Json::obj([
            ("buf", rec::bytes(buf)),
            ("writer", Json::obj([("script", Json::arr(script.iter(), |r| r.json()))])),
        ]),
        outcome,
        observed: None,
    });
}

fn main() {
    use ErrorKind::{BrokenPipe, Interrupted, Other, WouldBlock, WriteZero};
    use Response::{Count, Custom, Panic, Simple};
    rec::init();
    let mut c = Corpus::new("borsh_1_6_1_nostd_io", &[("borsh", "1.6.1")]);
    let four = [1u8, 2, 3, 4];
    let thirty_two: Vec<u8> = (0..32).collect();

    // An empty buffer returns Ok(()) without a call, whatever the script says.
    case(&mut c, "empty/no_script", &[], &[]);
    case(&mut c, "empty/would_fail", &[Custom(Other, "never asked")], &[]);
    case(&mut c, "empty/would_zero", &[Count(0)], &[]);
    // One call takes everything.
    case(&mut c, "whole/one_byte", &[], &[0x7f]);
    case(&mut c, "whole/thirty_two", &[], &thirty_two);
    case(&mut c, "whole/exact_count", &[Count(4)], &four);
    // Partial counts continue on the rest of the buffer.
    case(&mut c, "partial/one_then_rest", &[Count(1)], &four);
    case(&mut c, "partial/byte_by_byte", &[Count(1), Count(1), Count(1), Count(1)], &four);
    case(&mut c, "partial/two_at_a_time", &[Count(2), Count(2)], &[1, 2, 3, 4, 5]);
    case(&mut c, "partial/thirty_one_then_one", &[Count(31), Count(1)], &thirty_two);
    // Ok(0) is the WriteZero error.
    case(&mut c, "zero/first", &[Count(0)], &four);
    case(&mut c, "zero/after_partial", &[Count(3), Count(0)], &four);
    // A count above the remaining length panics in `&buf[n..]`.
    case(&mut c, "overrun/by_one", &[Count(5)], &four);
    case(&mut c, "overrun/after_partial", &[Count(1), Count(4)], &four);
    case(&mut c, "overrun/usize_max", &[Count(usize::MAX)], &four);
    // Interrupted retries the same buffer.
    case(&mut c, "interrupted/then_rest", &[Custom(Interrupted, "try again")], &four);
    case(&mut c, "interrupted/simple_twice", &[Simple(Interrupted), Simple(Interrupted), Count(2)], &four);
    case(&mut c, "interrupted/after_partial", &[Count(1), Custom(Interrupted, "try again"), Count(1)], &four);
    case(&mut c, "interrupted/then_zero", &[Simple(Interrupted), Count(0)], &four);
    case(&mut c, "interrupted/then_error", &[Simple(Interrupted), Custom(BrokenPipe, "pipe closed")], &four);
    // Any other error is returned unchanged, including a WriteZero returned by the writer.
    case(&mut c, "error/other", &[Custom(Other, "injected write failure")], &four);
    case(&mut c, "error/writers_write_zero", &[Custom(WriteZero, "the writer's own")], &four);
    case(&mut c, "error/would_block_simple", &[Simple(WouldBlock)], &four);
    case(&mut c, "error/after_partial", &[Count(2), Simple(BrokenPipe)], &four);
    // A panic of `write` unwinds through `write_all`.
    case(&mut c, "panic/first", &[Panic("writer panicked")], &four);
    case(&mut c, "panic/after_partial", &[Count(1), Panic("writer panicked")], &four);

    c.write(&rec::out_dir()).expect("write the corpus");
}
