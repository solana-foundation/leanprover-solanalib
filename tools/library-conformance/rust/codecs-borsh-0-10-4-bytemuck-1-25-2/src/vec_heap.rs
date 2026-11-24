//! borsh 0.10.4 `Vec<T>` decoding with its heap requests observed.
//!
//! `<Vec<T> as BorshDeserialize>::deserialize_reader::<&[u8]>` is recorded with
//! the heap requests of the call (`heap.rs`) in its state: `"heap": []` before
//! and the logged requests after. The vector buffer is the first block when
//! the source allocates one: `vec![0u8; len.min(1024 * 1024)]` (`alloc_zeroed`)
//! and its doubling `resize`s (`realloc`) in `u8::vec_from_reader`, or
//! `Vec::with_capacity(hint::cautious::<T>(len))` (`alloc`) and the `push`
//! growth (`realloc`) for other elements. Allocations made by an error and the
//! vector drop on the error path are logged too. The record `layout` is
//! `size_of`/`align_of` of the element `T`.
//!
//! `hint::cautious` is private in borsh 0.10.4. Its records are derived from
//! these runs: wherever the source reaches `Vec::with_capacity(hint::cautious::<T>(len))`
//! (an element without the `u8` override, a nonzero `u32` length read), the
//! first logged request is that allocation, and `cautious::<T>(len)` is its
//! size divided by `size_of::<T>()`. One record per element type and `len`.

use std::mem::{align_of, size_of};

use borsh::BorshDeserialize;
use conformance_recorder::{self as rec, Corpus, Json, Record};

use crate::borsh_de::{short, Ty};
use crate::heap;

pub const CAUTIOUS: &str = "borsh::de::hint::cautious";

pub fn layout<T>() -> Json {
    Json::obj([("size", Json::from(size_of::<T>())), ("align", Json::from(align_of::<T>()))])
}

/// A `cautious::<T>(len)` observation: the length, the capacity requested and
/// the record it was observed in.
pub struct Cautious {
    pub len: u32,
    pub bytes: usize,
    pub capacity: usize,
    pub from: String,
}

/// Record `deserialize_reader` of `Vec<T>` on each input with its heap
/// requests. For an element without the `u8` override (`generic`), collect the
/// `cautious` observations, one per `len`.
pub fn reader_cases<T: BorshDeserialize>(
    corpus: &mut Corpus,
    prefix: &str,
    ty: &Ty<Vec<T>>,
    generic: bool,
    inputs: &[(String, Vec<u8>)],
) -> Vec<Cautious> {
    let mut cautious: Vec<Cautious> = Vec::new();
    for (label, input) in inputs {
        let before = Json::obj([("slice", rec::bytes(input)), ("heap", Json::Arr(vec![]))]);
        let mut cursor: &[u8] = input;
        let (result, events) = heap::tracked(|| rec::catch(|| Vec::<T>::deserialize_reader(&mut cursor)));
        let consumed = input.len().wrapping_sub(cursor.len());
        assert!(
            cursor.len() <= input.len() && cursor.as_ptr() as usize == input.as_ptr() as usize + consumed,
            "the remaining slice is not a suffix of the input"
        );
        let after = Json::obj([("slice", rec::bytes(cursor)), ("heap", heap::events_json(&events))]);
        let outcome = match &result {
            Ok(r) => rec::returned(rec::io_result(r, ty.enc), after),
            Err(reason) => rec::unwound(reason.clone(), after),
        };
        let id = format!("{prefix}/deserialize_reader/Vec<{}>/{label}", short(&ty.reader_generics[0].1));
        let len = (input.len() >= 4).then(|| u32::from_le_bytes(input[..4].try_into().unwrap()));
        if let (true, Some(len)) = (generic, len.filter(|&l| l > 0)) {
            let first = events.first().copied().expect("Vec::with_capacity issued no heap request");
            assert!(
                first.op == "alloc" && first.block == Some(0) && first.align == align_of::<T>()
                    && first.size % size_of::<T>() == 0,
                "{id}: the first heap request {first:?} is not the vector's allocation"
            );
            if !cautious.iter().any(|c| c.len == len) {
                cautious.push(Cautious {
                    len,
                    bytes: first.size,
                    capacity: first.size / size_of::<T>(),
                    from: id.strip_prefix(&format!("{prefix}/")).unwrap_or(&id).to_string(),
                });
            }
        }
        let mut generics = ty.reader_generics.clone();
        generics.push(("R", "&[u8]".to_string()));
        corpus.push(Record {
            id,
            function: ty.reader_fn,
            generics,
            layout: Some(layout::<T>()),
            state: before,
            args: Json::empty(),
            outcome,
            observed: None,
        });
        drop(result);
    }
    cautious
}

/// The `cautious::<T>` records derived from `reader_cases`.
pub fn cautious_cases<T>(corpus: &mut Corpus, prefix: &str, element: &str, observed: &[Cautious]) {
    for c in observed {
        corpus.push(Record {
            id: format!("{prefix}/cautious/{}/hint{}", short(element), c.len),
            function: CAUTIOUS,
            generics: vec![("T", element.to_string())],
            layout: Some(layout::<T>()),
            state: Json::Null,
            args: Json::obj([("hint", Json::from(c.len))]),
            outcome: rec::returned(Json::from(c.capacity), Json::Null),
            observed: Some(Json::obj([
                ("derived_from", Json::from(c.from.as_str())),
                ("with_capacity_bytes", Json::from(c.bytes)),
            ])),
        });
    }
}

/// A `u32` length followed by `body`.
pub fn with_len(len: u32, body: &[u8]) -> Vec<u8> {
    let mut v = len.to_le_bytes().to_vec();
    v.extend_from_slice(body);
    v
}

/// Lengths at the `cautious` bound `4096 / size_of::<T>()` (`limit`): one
/// below and at it with a one-element body (the call fails after one push),
/// and above it with `limit + 1` encoded elements, so the `push` at the full
/// capacity grows the buffer. `above` is the length of the last case; when it
/// is `limit + 1` that case returns `Ok`, otherwise it fails after the growth.
pub fn hint_inputs(limit: u32, one: &[u8], element: &[u8], above: u32) -> Vec<(String, Vec<u8>)> {
    let grown: Vec<u8> = element.repeat(limit as usize + 1);
    vec![
        (format!("hint/len{}/short", limit - 1), with_len(limit - 1, one)),
        (format!("hint/len{limit}/short"), with_len(limit, one)),
        (format!("hint/len{above}/body{}", limit + 1), with_len(above, &grown)),
    ]
}

/// `u8::vec_from_reader` beyond its 1 MiB initial buffer: a full body of
/// 1 MiB + 1 bytes (one `resize`, then `Ok`), and a 3 MiB length with 1 MiB + 5
/// bytes (one `resize`, then the short read fails).
pub fn byte_resize_inputs() -> Vec<(String, Vec<u8>)> {
    const MIB: usize = 1024 * 1024;
    vec![
        ("resize/len1048577".to_string(), with_len(MIB as u32 + 1, &vec![0u8; MIB + 1])),
        ("resize/len3145728/short".to_string(), with_len(3 * MIB as u32, &vec![0u8; MIB + 5])),
    ]
}
