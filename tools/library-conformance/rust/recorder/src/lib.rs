//! Deterministic call recorder for the Solana library conformance drivers.
//!
//! A driver calls an unmodified library function on chosen inputs and writes
//! one record per call: the function identity, its generic instantiation, the
//! state before the call, the arguments and the observed outcome. The Lean side
//! of the suite evaluates the registered model reference on the same state and
//! arguments and compares outcomes. The encoding is documented in the suite
//! README (section "Corpus format"); this file is its only producer.
//!
//! The recorder has no dependencies, so it cannot change the dependency graph
//! of the library under test.

use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::panic::{self, AssertUnwindSafe};
use std::path::Path;

/// Version tag of the corpus format. The Lean checker and `run.py` reject any
/// other value.
pub const SCHEMA: &str = "solana-library-conformance/corpus/v1";

/// A JSON value with insertion-ordered objects and exact integers.
#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Int(i128),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
    /// Already rendered JSON text, inserted verbatim (outcomes recorded in a
    /// forked child by the shim).
    Raw(String),
}

impl Json {
    pub fn obj<const N: usize>(fields: [(&str, Json); N]) -> Json {
        Json::Obj(fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
    }

    pub fn empty() -> Json {
        Json::Obj(Vec::new())
    }

    pub fn arr<T>(items: impl IntoIterator<Item = T>, f: impl Fn(T) -> Json) -> Json {
        Json::Arr(items.into_iter().map(f).collect())
    }

    pub fn render(&self, out: &mut String) {
        match self {
            Json::Null => out.push_str("null"),
            Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Json::Int(n) => out.push_str(&n.to_string()),
            Json::Str(s) => render_string(s, out),
            Json::Arr(items) => {
                out.push('[');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    item.render(out);
                }
                out.push(']');
            }
            Json::Raw(text) => out.push_str(text),
            Json::Obj(fields) => {
                out.push('{');
                for (i, (key, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    render_string(key, out);
                    out.push(':');
                    value.render(out);
                }
                out.push('}');
            }
        }
    }

    pub fn to_text(&self) -> String {
        let mut out = String::new();
        self.render(&mut out);
        out
    }
}

fn render_string(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

macro_rules! json_from_int {
    ($($t:ty),*) => {$(
        impl From<$t> for Json {
            fn from(n: $t) -> Json { Json::Int(n as i128) }
        }
    )*};
}
json_from_int!(u8, u16, u32, u64, i8, i16, i32, i64, usize);

impl From<bool> for Json {
    fn from(b: bool) -> Json {
        Json::Bool(b)
    }
}

impl From<&str> for Json {
    fn from(s: &str) -> Json {
        Json::Str(s.to_string())
    }
}

impl From<String> for Json {
    fn from(s: String) -> Json {
        Json::Str(s)
    }
}

/// Zero runs at least this long are written as `[N]` in hex strings.
pub const ZERO_RUN: usize = 64;

/// Lower-case hexadecimal, two digits per byte, no prefix, except that every
/// maximal run of at least `ZERO_RUN` zero bytes is written `[N]` (decimal
/// length), e.g. `01[10240]ff`. The form is canonical: shorter zero runs are
/// plain hex. Readers (`run.py`, Lean `parseHex`) expand it.
pub fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    let mut i = 0;
    while i < bytes.len() {
        let zeros = bytes[i..].iter().take_while(|b| **b == 0).count();
        if zeros >= ZERO_RUN {
            s.push_str(&format!("[{zeros}]"));
            i += zeros;
        } else {
            let b = bytes[i];
            s.push(DIGITS[(b >> 4) as usize] as char);
            s.push(DIGITS[(b & 15) as usize] as char);
            i += 1;
        }
    }
    s
}

/// Plain hexadecimal without zero-run compaction (for ids and labels).
pub fn hex_plain(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Every byte sequence (`[u8; N]`, `&[u8]`, `Vec<u8>`, addresses) is a hex string.
pub fn bytes(b: &[u8]) -> Json {
    Json::Str(hex(b))
}

/// An `f64` is the hex string of its 64 IEEE-754 bits, so NaN payloads, signed
/// zeros and infinities are exact.
pub fn f64_bits(x: f64) -> Json {
    Json::Str(format!("{:016x}", x.to_bits()))
}

/// `Option<T>`: `null` for `None`, `{"some": v}` for `Some(v)`.
pub fn option<T>(value: &Option<T>, f: impl Fn(&T) -> Json) -> Json {
    match value {
        None => Json::Null,
        Some(v) => Json::obj([("some", f(v))]),
    }
}

/// An enum value: `{"variant": name, "fields": [...]}`.
pub fn variant(name: &str, fields: Vec<Json>) -> Json {
    Json::obj([("variant", name.into()), ("fields", Json::Arr(fields))])
}

/// A `std::io::Error` is its `ErrorKind` Debug name and its `Display` text.
pub fn io_error(e: &io::Error) -> Json {
    Json::obj([
        ("kind", format!("{:?}", e.kind()).into()),
        ("message", e.to_string().into()),
    ])
}

/// `Result::Ok` and `Result::Err`, both ordinary returns.
pub fn ok(v: Json) -> Json {
    Json::obj([("ok", v)])
}

pub fn err(e: Json) -> Json {
    Json::obj([("err", e)])
}

pub fn io_result<T>(r: &io::Result<T>, f: impl Fn(&T) -> Json) -> Json {
    match r {
        Ok(v) => ok(f(v)),
        Err(e) => err(io_error(e)),
    }
}

/// An ordinary return (including `Result::Err`) with the state after the call.
pub fn returned(result: Json, state: Json) -> Json {
    Json::obj([("exit", "returned".into()), ("result", result), ("state", state)])
}

/// A Rust panic caught by `catch_unwind`, with the state observed after the
/// unwind reached the driver. Maps to the model `Outcome.unwound`.
pub fn unwound(reason: String, state: Json) -> Json {
    Json::obj([("exit", "unwound".into()), ("reason", reason.into()), ("state", state)])
}

/// Silence the default panic hook: panics are recorded, not printed.
pub fn init() {
    panic::set_hook(Box::new(|_| {}));
}

/// Run `f`, mapping a panic to its payload text.
pub fn catch<R>(f: impl FnOnce() -> R) -> Result<R, String> {
    panic::catch_unwind(AssertUnwindSafe(f)).map_err(|payload| {
        if let Some(s) = payload.downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = payload.downcast_ref::<String>() {
            s.clone()
        } else {
            "<non-string panic payload>".to_string()
        }
    })
}

// ---------------------------------------------------------------------------
// Readers: `deserialize(&mut &[u8])` and `deserialize_reader(&mut R)` at
// `R = &[u8]`. The slice is the state; its remaining bytes are recorded after
// the call, whatever the exit.
// ---------------------------------------------------------------------------

pub fn slice_state(remaining: &[u8]) -> Json {
    Json::obj([("slice", bytes(remaining))])
}

/// A call on a mutable slice cursor. Returns (state before, outcome). The
/// remaining slice must be a suffix of the input (same memory, nothing
/// copied); the recording fails otherwise, so this native-only property is
/// checked without being stored.
pub fn slice_call<T>(
    input: &[u8],
    f: impl FnOnce(&mut &[u8]) -> io::Result<T>,
    enc: impl Fn(&T) -> Json,
) -> (Json, Json) {
    let before = slice_state(input);
    let mut cursor: &[u8] = input;
    let result = catch(|| f(&mut cursor));
    let consumed = input.len().wrapping_sub(cursor.len());
    assert!(
        cursor.len() <= input.len() && cursor.as_ptr() as usize == input.as_ptr() as usize + consumed,
        "the remaining slice is not a suffix of the input"
    );
    let after = slice_state(cursor);
    let outcome = match result {
        Ok(r) => returned(io_result(&r, enc), after),
        Err(reason) => unwound(reason, after),
    };
    (before, outcome)
}

/// A call on an immutable slice argument (`try_from_slice`). The state is
/// `()`, recorded as `null`.
pub fn value_call<T>(f: impl FnOnce() -> io::Result<T>, enc: impl Fn(&T) -> Json) -> Json {
    match catch(f) {
        Ok(r) => returned(io_result(&r, enc), Json::Null),
        Err(reason) => unwound(reason, Json::Null),
    }
}

// ---------------------------------------------------------------------------
// Writers: a recording `std::io::Write` whose `write_all` logs each chunk and
// can fail at its k-th call (0-based, counting every writer method call).
// ---------------------------------------------------------------------------

pub const INJECTED_KIND: io::ErrorKind = io::ErrorKind::Other;
pub const INJECTED_MESSAGE: &str = "injected write failure";

#[derive(Default)]
pub struct RecordingWriter {
    pub fail_at: Option<usize>,
    pub calls: usize,
    pub events: Vec<Json>,
}

impl RecordingWriter {
    pub fn new(fail_at: Option<usize>) -> Self {
        RecordingWriter { fail_at, calls: 0, events: Vec::new() }
    }

    fn next_fails(&mut self) -> bool {
        let fails = self.fail_at == Some(self.calls);
        self.calls += 1;
        fails
    }

    fn injected() -> io::Error {
        io::Error::new(INJECTED_KIND, INJECTED_MESSAGE)
    }

    /// The writer argument: its failure plan. Constant during the call.
    pub fn plan(fail_at: Option<usize>) -> Json {
        let e = Self::injected();
        Json::obj([
            ("fail_at", fail_at.map_or(Json::Null, Json::from)),
            ("error", io_error(&e)),
        ])
    }

    /// The writer state: every call it received, in order.
    pub fn state(&self) -> Json {
        Json::obj([("events", Json::Arr(self.events.clone()))])
    }
}

impl io::Write for RecordingWriter {
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        let result = if self.next_fails() { Err(Self::injected()) } else { Ok(()) };
        self.events.push(Json::obj([
            ("op", "write_all".into()),
            ("bytes", bytes(buf)),
            ("result", io_result(&result, |_| Json::Null)),
        ]));
        result
    }

    /// Not used by the modeled serializers; logged so that a call is visible
    /// as a mismatch rather than silently absorbed.
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let result = if self.next_fails() { Err(Self::injected()) } else { Ok(buf.len()) };
        self.events.push(Json::obj([
            ("op", "write".into()),
            ("bytes", bytes(buf)),
            ("result", io_result(&result, |n| Json::from(*n))),
        ]));
        result
    }

    fn flush(&mut self) -> io::Result<()> {
        let result = if self.next_fails() { Err(Self::injected()) } else { Ok(()) };
        self.events.push(Json::obj([
            ("op", "flush".into()),
            ("result", io_result(&result, |_| Json::Null)),
        ]));
        result
    }
}

/// A serializer call. Returns (state before, writer argument, outcome).
pub fn writer_call(
    fail_at: Option<usize>,
    f: impl FnOnce(&mut RecordingWriter) -> io::Result<()>,
) -> (Json, Json, Json) {
    let mut writer = RecordingWriter::new(fail_at);
    let before = writer.state();
    let result = catch(|| f(&mut writer));
    let after = writer.state();
    let outcome = match result {
        Ok(r) => returned(io_result(&r, |_| Json::Null), after),
        Err(reason) => unwound(reason, after),
    };
    (before, RecordingWriter::plan(fail_at), outcome)
}

// ---------------------------------------------------------------------------
// Corpus
// ---------------------------------------------------------------------------

pub struct Record {
    /// Stable case identifier, unique within the corpus file.
    pub id: String,
    /// Rust item path of the function, as rustc prints it in call inventories.
    pub function: &'static str,
    /// Concrete generic arguments, by parameter name, in declaration order.
    pub generics: Vec<(&'static str, String)>,
    /// `size_of`/`align_of` of the instantiation, where the model is indexed
    /// by a layout (bytemuck). The Lean side checks its index against it.
    pub layout: Option<Json>,
    pub state: Json,
    pub args: Json,
    pub outcome: Json,
    /// Native-only observations; never compared.
    pub observed: Option<Json>,
}

impl Record {
    fn to_json(&self) -> Json {
        let mut fields = vec![
            ("id".to_string(), Json::from(self.id.as_str())),
            ("function".to_string(), Json::from(self.function)),
            (
                "generics".to_string(),
                Json::Obj(
                    self.generics
                        .iter()
                        .map(|(k, v)| (k.to_string(), Json::from(v.as_str())))
                        .collect(),
                ),
            ),
        ];
        if let Some(l) = &self.layout {
            fields.push(("layout".to_string(), l.clone()));
        }
        fields.extend([
            ("state".to_string(), self.state.clone()),
            ("args".to_string(), self.args.clone()),
            ("outcome".to_string(), self.outcome.clone()),
        ]);
        if let Some(o) = &self.observed {
            fields.push(("observed".to_string(), o.clone()));
        }
        Json::Obj(fields)
    }
}

pub struct Corpus {
    name: &'static str,
    crates: Vec<(&'static str, &'static str)>,
    records: Vec<Json>,
    ids: BTreeSet<String>,
}

impl Corpus {
    /// `crates`: the (name, version) pairs under test, checked against
    /// `Cargo.lock` by `run.py`.
    pub fn new(name: &'static str, crates: &[(&'static str, &'static str)]) -> Self {
        Corpus { name, crates: crates.to_vec(), records: Vec::new(), ids: BTreeSet::new() }
    }

    /// Ids are unique within their corpus file, which is their namespace: a
    /// leading `"<corpus>/"` is dropped.
    pub fn push(&mut self, mut record: Record) {
        if let Some(rest) = record.id.strip_prefix(&format!("{}/", self.name)) {
            record.id = rest.to_string();
        }
        assert!(self.ids.insert(record.id.clone()), "duplicate case id {}", record.id);
        self.records.push(record.to_json());
    }

    pub fn len(&self) -> usize {
        self.records.len()
    }

    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    /// One record per line, so that corpus diffs are reviewable.
    pub fn write(&self, dir: &Path) -> io::Result<()> {
        let header = Json::obj([
            ("schema", SCHEMA.into()),
            ("corpus", self.name.into()),
            (
                "crates",
                Json::arr(self.crates.iter(), |(n, v)| {
                    Json::obj([("name", (*n).into()), ("version", (*v).into())])
                }),
            ),
        ])
        .to_text();
        let mut out = String::new();
        out.push_str(&header[..header.len() - 1]);
        out.push_str(",\"records\":[\n");
        for (i, r) in self.records.iter().enumerate() {
            r.render(&mut out);
            out.push_str(if i + 1 < self.records.len() { ",\n" } else { "\n" });
        }
        out.push_str("]}\n");
        fs::create_dir_all(dir)?;
        fs::write(dir.join(format!("{}.json", self.name)), out)
    }
}

/// The output directory: the first command-line argument.
pub fn out_dir() -> std::path::PathBuf {
    std::env::args_os()
        .nth(1)
        .map(Into::into)
        .unwrap_or_else(|| panic!("usage: <driver> OUTPUT_DIRECTORY"))
}

// ---------------------------------------------------------------------------
// Case material
// ---------------------------------------------------------------------------

/// Every prefix of `bytes`, from empty up to but excluding the whole.
pub fn proper_prefixes(bytes: &[u8]) -> impl Iterator<Item = &[u8]> {
    (0..bytes.len()).map(move |n| &bytes[..n])
}

/// The trailing bytes appended in "trailing" cases.
pub const TRAILING: [u8; 2] = [0xaa, 0x55];

pub fn with_trailing(bytes: &[u8]) -> Vec<u8> {
    let mut v = bytes.to_vec();
    v.extend_from_slice(&TRAILING);
    v
}

/// IEEE-754 binary64 bit patterns: zeros, subnormals, normals, infinities and
/// NaNs (quiet, signalling, negative, with payloads).
pub const F64_PATTERNS: &[(&str, u64)] = &[
    ("pos_zero", 0x0000_0000_0000_0000),
    ("neg_zero", 0x8000_0000_0000_0000),
    ("min_subnormal", 0x0000_0000_0000_0001),
    ("max_subnormal", 0x000f_ffff_ffff_ffff),
    ("min_normal", 0x0010_0000_0000_0000),
    ("one", 0x3ff0_0000_0000_0000),
    ("neg_one_half", 0xbfe0_0000_0000_0000),
    ("max", 0x7fef_ffff_ffff_ffff),
    ("neg_max", 0xffef_ffff_ffff_ffff),
    ("pos_inf", 0x7ff0_0000_0000_0000),
    ("neg_inf", 0xfff0_0000_0000_0000),
    ("qnan", 0x7ff8_0000_0000_0000),
    ("neg_qnan", 0xfff8_0000_0000_0000),
    ("snan_min_payload", 0x7ff0_0000_0000_0001),
    ("snan_max_payload", 0x7ff7_ffff_ffff_ffff),
    ("qnan_payload", 0x7ff8_dead_beef_0001),
    ("nan_all_ones", 0xffff_ffff_ffff_ffff),
];

/// The writer failure plans used for every serializer value: no failure, then
/// failure at each call index up to `max_calls` (one past the last call is
/// included to confirm it has no effect).
pub fn fail_plans(max_calls: usize) -> Vec<Option<usize>> {
    std::iter::once(None).chain((0..=max_calls).map(Some)).collect()
}
