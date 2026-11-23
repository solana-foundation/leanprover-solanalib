// Borsh decoder cases shared by the borsh 0.10.4 and 1.6.1 drivers.
//
// Included with `#[path]` into each driver, so `borsh` resolves to the version
// pinned by the driver `Cargo.toml` and `Cargo.lock` files. The two versions
// have the same decoder API; their observable errors differ and are recorded.

use borsh::BorshDeserialize;
use conformance_recorder as rec;
use rec::{Corpus, Json, Record};

pub const DESERIALIZE: &str = "borsh::de::BorshDeserialize::deserialize";
pub const TRY_FROM_SLICE: &str = "borsh::de::BorshDeserialize::try_from_slice";

/// A decoded type: its Rust name, the item path of its `deserialize_reader`
/// impl, the generic parameters of that impl and a value encoder.
pub struct Ty<T> {
    pub name: String,
    pub reader_fn: &'static str,
    pub reader_generics: Vec<(&'static str, String)>,
    pub enc: fn(&T) -> Json,
}

/// Which of the three decoding entry points to record.
#[derive(Clone, Copy)]
pub struct Entries {
    pub deserialize: bool,
    pub deserialize_reader: bool,
    pub try_from_slice: bool,
}

pub const ALL: Entries = Entries { deserialize: true, deserialize_reader: true, try_from_slice: true };
/// borsh 1.6.1 registers no `try_from_slice` member (this profile does not select it).
pub const NO_TRY_FROM_SLICE: Entries = Entries { deserialize: true, deserialize_reader: true, try_from_slice: false };

/// The last path segment of a type name, for case ids
/// (`core::option::Option<u8>` gives `Option<u8>`).
pub fn short(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

/// The most wrapper (`deserialize`, `try_from_slice`) cases kept per `Self`.
pub const WRAPPER_CAP: usize = 20;

/// Record `deserialize_reader` on every input, and the wrappers `deserialize`
/// and `try_from_slice` on the representative inputs chosen by `representative`.
pub fn decode_cases<T: BorshDeserialize>(
    corpus: &mut Corpus,
    prefix: &str,
    ty: &Ty<T>,
    entries: Entries,
    inputs: &[(String, Vec<u8>)],
) {
    if entries.deserialize_reader {
        for (label, input) in inputs {
            let (state, outcome) =
                rec::slice_call(input, |buf| T::deserialize_reader(buf), ty.enc);
            let mut generics = ty.reader_generics.clone();
            generics.push(("R", "&[u8]".to_string()));
            corpus.push(Record {
                id: format!("{prefix}/deserialize_reader/{}/{label}", short(&ty.name)),
                function: ty.reader_fn,
                generics,
                layout: None,
                state,
                args: Json::empty(),
                outcome,
                observed: None,
            });
        }
    }
    if !(entries.deserialize || entries.try_from_slice) {
        return;
    }
    for (label, input) in representative::<T>(inputs) {
        if entries.deserialize {
            let (state, outcome) = rec::slice_call(input, |buf| T::deserialize(buf), ty.enc);
            corpus.push(Record {
                id: format!("{prefix}/deserialize/{}/{label}", short(&ty.name)),
                function: DESERIALIZE,
                generics: vec![("Self", ty.name.clone())],
                layout: None,
                state,
                args: Json::empty(),
                outcome,
                observed: None,
            });
        }
        if entries.try_from_slice {
            let outcome = rec::value_call(|| T::try_from_slice(input), ty.enc);
            corpus.push(Record {
                id: format!("{prefix}/try_from_slice/{}/{label}", short(&ty.name)),
                function: TRY_FROM_SLICE,
                generics: vec![("Self", ty.name.clone())],
                layout: None,
                state: Json::Null,
                args: Json::obj([("bytes", rec::bytes(input))]),
                outcome,
                observed: None,
            });
        }
    }
}

/// The outcome class of `deserialize_reader` on an input: `Ok`, or the error
/// kind and message with decimal numbers removed, or a panic; and whether
/// bytes remain after the call.
pub fn outcome_class<T: BorshDeserialize>(input: &[u8]) -> String {
    let mut cursor: &[u8] = input;
    let result = rec::catch(|| T::deserialize_reader(&mut cursor).map(|_| ()));
    let remains = if cursor.is_empty() { "empty" } else { "remaining" };
    match result {
        Ok(Ok(())) => format!("ok/{remains}"),
        Ok(Err(e)) => {
            let message: String = e.to_string().chars().filter(|c| !c.is_ascii_digit()).collect();
            format!("err/{:?}/{message}/{remains}", e.kind())
        }
        Err(_) => format!("unwound/{remains}"),
    }
}

/// The wrapper cases: inputs grouped by `outcome_class`, in order of first
/// appearance, keeping the first and the last input of each class (for
/// truncations, the shortest and the longest prefix), at most `WRAPPER_CAP`.
/// If the cap binds, the first input of every class is kept before any last.
pub fn representative<T: BorshDeserialize>(inputs: &[(String, Vec<u8>)]) -> Vec<(&String, &Vec<u8>)> {
    let mut classes: Vec<(String, usize, usize)> = Vec::new();
    for (i, (_, input)) in inputs.iter().enumerate() {
        let class = outcome_class::<T>(input);
        match classes.iter_mut().find(|(c, _, _)| *c == class) {
            Some(entry) => entry.2 = i,
            None => classes.push((class, i, i)),
        }
    }
    let mut chosen: Vec<usize> = classes.iter().map(|(_, first, _)| *first).collect();
    for (_, first, last) in &classes {
        if chosen.len() >= WRAPPER_CAP {
            break;
        }
        if last != first {
            chosen.push(*last);
        }
    }
    chosen.truncate(WRAPPER_CAP);
    chosen.sort();
    chosen.into_iter().map(|i| (&inputs[i].0, &inputs[i].1)).collect()
}

/// Inputs for a fixed-width value: each full encoding, each with trailing
/// bytes, every proper prefix of the first, and the empty input.
pub fn fixed_inputs(encodings: &[(String, Vec<u8>)]) -> Vec<(String, Vec<u8>)> {
    let mut out: Vec<(String, Vec<u8>)> = encodings.to_vec();
    for (label, bytes) in encodings.iter().take(2) {
        out.push((format!("{label}+trailing"), rec::with_trailing(bytes)));
    }
    if let Some((label, bytes)) = encodings.first() {
        for p in rec::proper_prefixes(bytes) {
            out.push((format!("{label}/truncated{}", p.len()), p.to_vec()));
        }
    }
    dedup(out)
}

pub fn dedup(inputs: Vec<(String, Vec<u8>)>) -> Vec<(String, Vec<u8>)> {
    let mut seen = std::collections::BTreeSet::new();
    inputs.into_iter().filter(|(l, _)| seen.insert(l.clone())).collect()
}

fn prim<T>(name: &str, enc: fn(&T) -> Json) -> Ty<T> {
    Ty {
        name: name.to_string(),
        reader_fn: Box::leak(format!("<{name} as borsh::de::BorshDeserialize>::deserialize_reader").into_boxed_str()),
        reader_generics: vec![],
        enc,
    }
}

fn exhaustive_byte() -> Vec<(String, Vec<u8>)> {
    let mut v: Vec<(String, Vec<u8>)> = (0..=255u8).map(|b| (format!("b{b:02x}"), vec![b])).collect();
    v.push(("empty".into(), vec![]));
    v.push(("b00+trailing".into(), rec::with_trailing(&[0])));
    v.push(("b01+trailing".into(), rec::with_trailing(&[1])));
    v
}

macro_rules! int_inputs {
    ($t:ty, [$($v:expr),* $(,)?]) => {{
        let encs: Vec<(String, Vec<u8>)> = vec![$((format!("{}", $v as $t), ($v as $t).to_le_bytes().to_vec())),*];
        fixed_inputs(&encs)
    }};
}

pub fn u8_ty() -> Ty<u8> { prim("u8", |v| Json::from(*v)) }
pub fn i8_ty() -> Ty<i8> { prim("i8", |v| Json::from(*v)) }
pub fn bool_ty() -> Ty<bool> { prim("bool", |v| Json::from(*v)) }
pub fn u32_ty() -> Ty<u32> { prim("u32", |v| Json::from(*v)) }
pub fn i32_ty() -> Ty<i32> { prim("i32", |v| Json::from(*v)) }
pub fn u64_ty() -> Ty<u64> { prim("u64", |v| Json::from(*v)) }
pub fn i64_ty() -> Ty<i64> { prim("i64", |v| Json::from(*v)) }
pub fn f64_ty() -> Ty<f64> { prim("f64", |v| rec::f64_bits(*v)) }

pub fn u8_inputs() -> Vec<(String, Vec<u8>)> { exhaustive_byte() }
pub fn i8_inputs() -> Vec<(String, Vec<u8>)> { exhaustive_byte() }
pub fn bool_inputs() -> Vec<(String, Vec<u8>)> { exhaustive_byte() }

pub fn u32_inputs() -> Vec<(String, Vec<u8>)> {
    int_inputs!(u32, [0x0102_0304u32, 0u32, 1u32, 0x7fu32, 0x80u32, 0xffu32, 0x100u32,
        0x7fff_ffffu32, 0x8000_0000u32, 0xffff_fffeu32, 0xffff_ffffu32])
}

pub fn i32_inputs() -> Vec<(String, Vec<u8>)> {
    int_inputs!(i32, [0x0102_0304i32, 0i32, 1i32, -1i32, -8i32, 127i32, -128i32,
        i32::MAX, i32::MIN])
}

pub fn u64_inputs() -> Vec<(String, Vec<u8>)> {
    int_inputs!(u64, [0x0102_0304_0506_0708u64, 0u64, 1u64, 0xffu64, 0x100u64,
        u32::MAX as u64, u32::MAX as u64 + 1, i64::MAX as u64, i64::MIN as u64,
        u64::MAX - 1, u64::MAX])
}

pub fn i64_inputs() -> Vec<(String, Vec<u8>)> {
    int_inputs!(i64, [0x0102_0304_0506_0708i64, 0i64, 1i64, -1i64, i32::MIN as i64,
        i32::MAX as i64 + 1, i64::MAX, i64::MIN, i64::MIN + 1])
}

pub fn f64_inputs() -> Vec<(String, Vec<u8>)> {
    let encs: Vec<(String, Vec<u8>)> = rec::F64_PATTERNS
        .iter()
        .map(|(l, bits)| (l.to_string(), bits.to_le_bytes().to_vec()))
        .collect();
    // Trailing bytes after a NaN and after a valid value.
    let mut out = fixed_inputs(&encs);
    out.push(("qnan+trailing".into(), rec::with_trailing(&0x7ff8_0000_0000_0000u64.to_le_bytes())));
    dedup(out)
}

// --- Option<T> -------------------------------------------------------------

/// Option tag bytes: both valid tags and the smallest and largest invalid ones.
pub const OPTION_TAGS: [u8; 4] = [0, 1, 2, 255];

pub fn option_ty<T: 'static>(inner: &Ty<T>, enc: fn(&Option<T>) -> Json) -> Ty<Option<T>> {
    Ty {
        name: format!("core::option::Option<{}>", inner.name),
        reader_fn: "<core::option::Option<T> as borsh::de::BorshDeserialize>::deserialize_reader",
        reader_generics: vec![("T", inner.name.clone())],
        enc,
    }
}

/// `OPTION_TAGS`, each followed by `payload`; the empty input; every proper
/// prefix of the `Some` encoding; trailing bytes after `None` and `Some`.
pub fn option_inputs(payload: &[u8]) -> Vec<(String, Vec<u8>)> {
    let mut out = vec![("empty".to_string(), vec![])];
    for tag in OPTION_TAGS {
        let mut v = vec![tag];
        v.extend_from_slice(payload);
        out.push((format!("tag{tag:02x}+payload"), v));
    }
    out.push(("none".into(), vec![0]));
    let mut some = vec![1];
    some.extend_from_slice(payload);
    for p in rec::proper_prefixes(&some) {
        out.push((format!("some/truncated{}", p.len()), p.to_vec()));
    }
    out.push(("none+trailing".into(), rec::with_trailing(&[0])));
    out.push(("some+trailing".into(), rec::with_trailing(&some)));
    dedup(out)
}

// --- Vec<T> ----------------------------------------------------------------

pub fn vec_ty<T: 'static>(inner: &Ty<T>, enc: fn(&Vec<T>) -> Json) -> Ty<Vec<T>> {
    Ty {
        name: format!("alloc::vec::Vec<{}>", inner.name),
        reader_fn: "<alloc::vec::Vec<T> as borsh::de::BorshDeserialize>::deserialize_reader",
        reader_generics: vec![("T", inner.name.clone())],
        enc,
    }
}

/// `elements[i]` is the encoding of the i-th element. Cases: lengths 0 to
/// `elements.len()` with full bodies; every proper prefix of the longest;
/// a length of `u32::MAX` with a short body; trailing bytes.
pub fn vec_inputs(elements: &[Vec<u8>]) -> Vec<(String, Vec<u8>)> {
    let mut out = vec![("empty".to_string(), vec![])];
    let encode = |n: usize| {
        let mut v = (n as u32).to_le_bytes().to_vec();
        for e in &elements[..n] {
            v.extend_from_slice(e);
        }
        v
    };
    for n in 0..=elements.len() {
        out.push((format!("len{n}"), encode(n)));
    }
    let longest = encode(elements.len());
    for p in rec::proper_prefixes(&longest) {
        out.push((format!("len{}/truncated{}", elements.len(), p.len()), p.to_vec()));
    }
    let mut huge = u32::MAX.to_le_bytes().to_vec();
    huge.extend_from_slice(&elements[0]);
    out.push(("len_u32max/short".into(), huge));
    out.push(("len0+trailing".into(), rec::with_trailing(&encode(0))));
    out.push((format!("len{}+trailing", elements.len()), rec::with_trailing(&longest)));
    dedup(out)
}

// --- [T; N] ----------------------------------------------------------------

pub fn array_ty<T: 'static, const N: usize>(inner: &Ty<T>, enc: fn(&[T; N]) -> Json) -> Ty<[T; N]> {
    Ty {
        name: format!("[{}; {N}]", inner.name),
        reader_fn: "<[T; N] as borsh::de::BorshDeserialize>::deserialize_reader",
        reader_generics: vec![("T", inner.name.clone()), ("N", N.to_string())],
        enc,
    }
}

/// A byte pattern of length `n` that differs from position to position.
pub fn pattern(n: usize, seed: u8) -> Vec<u8> {
    (0..n).map(|i| (i as u8).wrapping_mul(37).wrapping_add(seed)).collect()
}

// --- Hidden trait methods ----------------------------------------------------

/// `<u8 as BorshDeserialize>::array_from_reader::<&[u8], N>`: `Some` of the
/// next `N` bytes. Only borsh 1.6.1 registers it.
pub fn array_from_reader_cases<const N: usize>(corpus: &mut Corpus, prefix: &str, inputs: &[(String, Vec<u8>)]) {
    for (label, input) in inputs {
        let (state, outcome) = rec::slice_call(
            input,
            |buf| u8::array_from_reader::<_, N>(buf),
            |v: &Option<[u8; N]>| rec::option(v, |a| rec::bytes(a)),
        );
        corpus.push(Record {
            id: format!("{prefix}/array_from_reader/u8/{N}/{label}"),
            function: "<u8 as borsh::de::BorshDeserialize>::array_from_reader",
            generics: vec![("R", "&[u8]".to_string()), ("N", N.to_string())],
            layout: None,
            state,
            args: Json::empty(),
            outcome,
            observed: None,
        });
    }
}

/// The trait default `vec_from_reader::<&[u8]>(len, reader)` of a `Self`
/// without the `u8` override: `Ok(None)`, reading nothing.
pub fn vec_from_reader_default_cases<T: BorshDeserialize>(
    corpus: &mut Corpus,
    prefix: &str,
    self_name: &str,
    cases: &[(u32, Vec<u8>)],
) {
    for (len, input) in cases {
        let (state, outcome) = rec::slice_call(
            input,
            |buf| T::vec_from_reader(*len, buf),
            |v: &Option<Vec<T>>| rec::option(v, |_| Json::from("<elements>")),
        );
        corpus.push(Record {
            id: format!("{prefix}/vec_from_reader/{self_name}/len{len}/{}", rec::hex(input)),
            function: "borsh::de::BorshDeserialize::vec_from_reader",
            generics: vec![("Self", self_name.to_string()), ("R", "&[u8]".to_string())],
            layout: None,
            state,
            args: Json::obj([("len", Json::from(*len))]),
            outcome,
            observed: None,
        });
    }
}
