# Borsh 0.10.4 and 1.6.1 codec models

These are mathematical models of selected borsh decoders and serializers. Their
reference and execution witnesses prove consistency of the stated models,
without a Rust implementation, compiler, memory, std io or allocator theorem.
The [source registry](../source-map.json) records the exact models, Rust names
and source anchors.

| Package | Source | Revision | SHA-256 |
| --- | --- | --- | --- |
| borsh 0.10.4 | `borsh/src/de/mod.rs` | `a1fe3631df2306b2991c1fa9142d7bfa17c2419e` | `6d4cb52550aac787186890ba6a0118157f8433d341c79118892bce1959d75fb2` |
| borsh 0.10.4 | `borsh/src/de/hint.rs` | `a1fe3631df2306b2991c1fa9142d7bfa17c2419e` | `dffc6467558f6966206fd7711cb7e366e192bb92b9d6ce33b8a19d087645f768` |
| borsh 1.6.1 | `borsh/src/de/mod.rs` | `f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac` | `de33c4401635c62ba60559014ee9bd69785cf40412c6da84cb2d12a45ead6462` |
| borsh 1.6.1 | `borsh/src/de/hint.rs` | `f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac` | `dffc6467558f6966206fd7711cb7e366e192bb92b9d6ce33b8a19d087645f768` |
| borsh 1.6.1 | `borsh/src/error.rs` | `f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac` | `ee752a75bdf432e4fa435288dc94f4532dd774aeeaa5aa1e9847f253cd07a935` |
| borsh 1.6.1 | `borsh/src/ser/mod.rs` | `f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac` | `f6265842f9a263673766cc7ab7d4add437e3b92681f0933e8bec1a96c29aa666` |
| borsh 1.6.1 | `borsh/src/nostd_io.rs` | `f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac` | `5ec34a946786142ff44f18cfbe692b62e45921e4d7e675da2d9f72496cf6e1bb` |

The repository is `near/borsh-rs`. Each revision is the commit recorded in `.cargo_vcs_info.json` for the crate, and each upstream file equals the published
crate file.

Several functions have the same item and implementation paths in both
versions: `deserialize_reader` of `u8`, `u32`, `u64`, `bool` and `Option<T>`,
and the default `deserialize`. Their models differ in error kinds. The catalog
entry check compares the crate version only with the declaration of the source, so
a binding must establish the linked borsh version from the lockfile of the program.
A program that links both versions can tell them apart only by the
build-specific crate id in the disambiguated description.

## Shared vocabulary

`Solanalib.Specs.Core.BorshWire` holds the wire format, `BorshProgram` a small
request-program type, `BorshCodec` the generic members as programs and
`BorshFamily` the version-independent contracts. `Solanalib.Specs.Core.Borsh`
itself is unchanged.

An `io::Error` is observed as its `ErrorKind` `Debug` name and its
`to_string()`. Every error that these members raise is `io::Error::new(kind,
msg)`, so the string is `msg`. The messages are the exact source constants and
`format!` templates. Decimal `u8` formatting matches `{}`.

The versions differ only in data, which a `Profile` supplies. In 0.10.4 every
decoding error has kind `InvalidInput`: short input, invalid bool and Option
tags, NaN and the `Vec` zero-sized check. In 1.6.1 all of these are
`InvalidData`. Both versions report leftover bytes in `try_from_slice` as
`InvalidData` "Not all bytes read". The zero-sized message is "Vectors of
zero-sized types ..." in 0.10.4 (`de/mod.rs:380-385`) and `ERROR_ZST_FORBIDDEN`
"Collections of zero-sized types ..." in 1.6.1 (`error.rs:3-10`). Apart from
these, the selected bodies match statement for statement.

## Reader and remaining slice

All decoders run at `R = &[u8]`, the reader that the default `deserialize`
passes (`&mut *buf`). A decoder maps the current slice to its result and the
remaining slice. Both versions map `UnexpectedEof` from `read_exact` to
"Unexpected length of input" (0.10.4 `de/mod.rs:128-134`, 1.6.1
`de/mod.rs:138-144`).

With the default `std` feature of borsh, the reader is `<&[u8] as Read>::read_exact` in std. In the toolchain of `rust-toolchain.toml`
(`library/std/src/io/impls.rs:348-353`) a short read empties the slice before
it returns the error. The executable references follow this behavior. The Borsh `nostd_io` reader (1.6.1 `nostd_io.rs:1039`) leaves the slice unchanged.
The `std` feature is a default feature of borsh, and Cargo unifies features
across a program, so a client must establish it from its own lockfile and
feature resolution. `solana-address` alone uses `default-features = false`.

The contracts fix the remaining slice only after success. After an error,
`DecodeMatches` leaves it unconstrained, so the contracts hold for either
reader. The differential tests check the references against the toolchain.
Callers that propagate the error with `?`, and `try_from_slice`, do not observe
the slice after an error.

## Decoders

- Integers read `size_of` bytes in one `read_exact` and decode them little-endian.
  Signed values are binary radix complement (`Int8` ... `Int64`).
- `f64` reads 8 bytes as binary64 bits (`Float64.Bits`). A NaN bit pattern, with
  any payload or sign, is rejected after its 8 bytes. Infinities and signed
  zeros are accepted.
- `bool` reads a `u8`: 0 and 1 are accepted, and any other byte is rejected after
  it is consumed. `Option<T>` reads a flag `u8` and calls `T` only for flag 1.
- `[T; N]` (1.6.1 `de/mod.rs:768-824`) calls `T::array_from_reader` first. The
  `u8` impl overrides that method (`188-194`) with one `read_exact` of N bytes;
  this is the `[u8; 32]` path of every `Address` field. Other impls keep the
  default `Ok(None)`. They then decode N elements in order, and the first error
  returns at once.
- `Vec<T>` (0.10.4 `de/mod.rs:374-401`) rejects a zero-sized `T` before it
  reads anything. It then reads a `u32` length, and length 0 gives `Vec::new()`.
  For `u8` the override `vec_from_reader` (`148-175`) zero-fills a buffer of
  at most 1 MiB. Each time the buffer is full and bytes are still due, it
  doubles the buffer, capped at the length, and calls `read`. A short body
  therefore consumes the whole slice before a zero-length read reports
  "Unexpected length of input". Other impls use `Vec::with_capacity(
  hint::cautious::<T>(len))`, where `cautious` is `max(min(len, 4096 /
  (size_of::<T>() as u32)), 1)` (`hint.rs:1-5`). The cast truncates modulo
  `2^32`: a positive size divisible by `2^32` panics after the length read,
  before allocation or element calls. A size of `2^32 + 1` uses divisor 1.
  After a successful hint, each element is decoded, then pushed.
- The default `deserialize` forwards `Self::deserialize_reader` unchanged.
  `try_from_slice` calls `Self::deserialize` on a local copy. It returns the error of that
  call, or "Not all bytes read" if bytes remain.

The family index records the implementation of the element. It is either `byte`,
the `u8` impl with its hidden overrides, or an impl that keeps the defaults,
together with `size_of::<T>()`. A binding must make the choice that matches the
actual `T`. The two choices give the same bytes but different allocation calls.

The cautious family has no size precondition. Its arithmetic returns a
capacity or selects the division-by-zero panic, even for hint 0; its panic
callback has no ordinary return and retains the unwind state or
terminal reason of the source. The vector family uses the same arithmetic only after its
zero-size check, successful length read and nonzero-length check. Its panic
callback receives the remaining slice at that point. A binding must supply
the actual target layout and panic policy. The pure/returning vector adapters
require a proof that the division panic is unreachable; that adapter proof
does not restrict the full family or `vecDecodeWithPanicFn`.

## Allocation

The `Vec<T>` model follows the owned-dependency convention
([owned dependencies](owned-dependencies.md)). Each source allocation call is
reported to an index provider in source order, with the requested size:
`with_capacity`, every `push`, the zeroed `u8` buffer and every `resize`. The
provider owns allocation, growth and failure. Its terminal or unwind exit ends
the decoder unchanged, and on Solana an allocation failure aborts. `Vec::new()`
cannot fail and is not reported. The closed sample uses an allocator that always
returns. This proves model consistency, not that allocation succeeds.

These parts of the source are not represented:

- the deallocation of a partially built vector;
- the destruction of decoded elements or of `Self` on error paths, including
  `ArrayDropGuard` and the value that `try_from_slice` drops before reporting
  leftover bytes;
- cleanup during unwinding.

The registry records these as assumptions on the affected models. They hold
for drop-glue-free element types and for a provider that does not track
deallocation.

## Serializers

borsh 1.6.1 serializers take the writer `W: Write` as an index callback, its
`write_all`. Each member is a program that issues its exact sequence of
`write_all` chunks. Interpreting it sequentially stops at the first error and
keeps every writer or element exit, including partial effects.

- `u8` and `bool` write one byte. `u32`, `u64` and `i64` write their
  little-endian bytes in a single chunk.
- `f64` returns `InvalidData` "For portability reasons we do not allow to
  serialize NaNs." before any write (`ser/mod.rs:136-151`).
- `Option<T>` writes `[0]`, or writes `[1]` and then calls `T::serialize` only
  after that write succeeds. `Some(NaN)` therefore writes the tag before the
  float error.
- `[T; N]` (`576-593`) writes nothing for N = 0. For `u8`, whose `u8_slice` is
  `Some(slice)` (`71-74`), it issues one `write_all` of all N bytes; this is
  the path of `[u8; 32]` and `[u8; 16]`. Otherwise it serializes the elements
  in order.

## The no-std `write_all`

Without its `std` feature, the `io` of borsh is `nostd_io`, and a writer that
implements only `write` gets the provided `Write::write_all`
(`nostd_io.rs:545-560`). `Solanalib.Specs.Borsh.nostd_io.Write.write_all_contract` is
indexed by the `write` of the writer, by the panic of `&buf[n..]` and by the allocator of the
program at the `String` message constructed by `Error::new`, all as callbacks.
`WriteAllRuns` follows the loop case for case, with these callbacks in place
of the code they stand for and the error observed as its kind and message
rather than its representation:

- an empty buffer returns `Ok(())` without calling `write`;
- `Ok(0)` allocates the message of `Error::new(ErrorKind::WriteZero, "failed
  to write whole buffer")` in the state `write` left; a return of the
  allocation gives that error, and its other exits are forwarded;
- `Ok(n)` with `n <= len` continues on `&buf[n..]`;
- `Ok(n)` with `n > len` panics in the core operation `slice_start_index_len_fail(n,
  len)`, and the outcome is the exit of the panic callback;
- an error of kind `Interrupted` is dropped and the same buffer is offered
  again;
- any other error is returned unchanged, including a `WriteZero` from the writer itself;
- unwind and terminal exits of `write` are forwarded.

The retry makes the relation inductive: a writer that is interrupted forever
has no finite outcome. `writeAllFuel` is the executable form at function
callbacks, and `writeAllRuns_ofFunction_iff` relates the two.
`WriterIndex.ofWrite` turns a `write_all` index into the writer index of the
serializers, so they compose over this model. The implementations that
override `write_all` in the same file (`&mut W`, `&mut [u8]` and `Vec<u8>`,
the `write_all` methods at lines 674, 700 and 727) are not this model.

## Executable references and controls

Primitive decoders are plain contracts over `Unit`, with the function reference
`decoderModel`. Generic members are families. Each has an executable
combinator (`optionDecodeFn`, `arrayDecodeFn`, `vecDecodeWithPanicFn`, `deserializeFn`,
`tryFromSliceFn`, `primitiveSerializeFn`, `optionSerializeFn`,
`arraySerializeFn`, with byte variants). A lemma proves that the family
reference at function-graph callbacks is the graph of that combinator.

The test roots check the following controls:

- byte order;
- binary radix complement;
- the emptied slice after a short read;
- the open remainder in the contract;
- the exact remainder after success;
- tag errors;
- NaN rejection in both directions;
- one chunk against element-wise chunking;
- no write for N = 0;
- writer errors with partial effects;
- forwarded unwinds;
- the `cautious` capacity, the `Vec` call order, stopping at the first element
  error, and allocation failure as a terminal exit;
- size truncation at `2^32`, further positive multiples and `2^32 + 1`, the unwind and terminal exits of the
  division panic, and the earlier zero-size,
  short-header and empty-vector exits;
- leftover bytes in `try_from_slice` with a derived-struct decoder;
- the empty buffer of `write_all`, partial counts, `WriteZero` and a failed
  allocation of its message, `Interrupted` retry, unchanged errors, slice
  panic, forwarded unwind, the absence of an outcome for a writer that is
  always interrupted, and a serializer over the modeled `write_all`.

Formatted messages are compared as structured errors inside Lean modules.
The differential tests compare the rendered strings.

The focused native regression is
[`cautious_truncation.rs`](../../../tools/library-conformance/rust/codecs-borsh-0-10-4-bytemuck-1-25-2/tests/cautious_truncation.rs).
It calls published Borsh 0.10.4 with `Huge([u8; 1usize << 32])`, checks that
this is a valid 64-bit Rust layout, and observes division panic, the consumed
length header, no element call and no vector-sized allocation. Controls cover
zero length, a short header, zero-sized elements and the `u8` specialization.
No `Huge` value is constructed. Run it with optimization to avoid an unused
huge return slot in the generic decoder:

```sh
CARGO_BUILD_JOBS=2 cargo +nightly-2026-05-01 test --locked --release \
  --manifest-path tools/library-conformance/rust/codecs-borsh-0-10-4-bytemuck-1-25-2/Cargo.toml \
  --test cautious_truncation
```

This is host execution evidence, including when the Solana source `cfg` is
selected; it does not establish an sBPF ABI or compiler correspondence.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:1075a161670073c4 -->
<a id="review-1075a161670073c4"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

borsh 0.10.4 instantiates the shared vocabulary with Profile (InvalidInput, "Vectors of zero-sized types ..."). Its u8/integer/bool/Option/Vec decoders, default deserialize, try_from_slice and vec_from_reader and hint::cautious match the shared programs statement for statement (src/de/mod.rs 38-52, 65-69, 128-185, 187-210, 290-339, 374-401; src/de/hint.rs 1-5).

borsh 1.6.1 instantiates the shared vocabulary with Profile (InvalidData, ERROR_ZST_FORBIDDEN). Its u8/u32/i32/u64/i64/f64/bool decoders, u8::array_from_reader, Option and [T; N] decoders and default deserialize (src/de/mod.rs 39-41, 138-195, 197-220, 275-298, 300-336, 768-824) and its u8/bool/u32/u64/i64/f64/Option/[T; N] serializers and u8_slice (src/ser/mod.rs 16, 65-96, 136-174, 576-593) match the shared programs statement for statement. Its nostd_io Write::write_all (src/nostd_io.rs 545-560) matches the shared write_all relation case for case, with the write of the writer, the slice panic and the String allocation of Error::new as index callbacks and the io::Error observed as its kind and message.
<!-- /registry -->

<!-- registry:review:1d18dc7136746b3c -->
<a id="review-1d18dc7136746b3c"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Versioned public aggregate of the reviewed mathematical models.

Instantiate the shared mathematical operations for this exact SDK version; keep closed reference, precondition and execution witnesses in the public version namespace.

Legacy stake values share the exact field vocabulary without the later StakeFlags variant. Instruction plans and resource lifetimes follow the selected constructor source. Pack is a callback family and WriteCounter is a serializer state machine, preserving generic effects and cleanup rather than treating them as pure decoders. Lookup decoding models the complete fixed bincode boundary and exact borrowed suffix. Closed references and witnesses are mathematical facts under the stated source interfaces. ALT normal error paths retain bincode Box<ErrorKind> allocation and map_err destruction in the indexed state; its pure decoder remains a value facet.
<!-- /registry -->

<!-- registry:review:1ee9794062f0a284 -->
<a id="review-1ee9794062f0a284"></a>

All 22 recorded stable 1.x releases have the same arbitrary-N body and u8 reader helper, including the InvalidData short-input error. The existing u8/default-hidden-method split and ArrayDropGuard effect boundary are unchanged. Older arrays have different length/type bounds, zero-padding behavior or errors. Error-construction allocation failure is outside the shared model boundary.
<!-- /registry -->

<!-- registry:review:a8e31471f677fe21 -->
<a id="review-a8e31471f677fe21"></a>

The complete arbitrary-N family corresponds from 0.9.1, with const-generics enabled for 0.9.1–0.9.3; it is unconditional from 0.10.0. N=0 does nothing; the actual u8 override gives one write_all of the original slice; a default hidden-method element is serialized in order, retaining every callback exit. The generic body and u8_slice override are byte-identical throughout this set. 0.2.2–0.2.4 provide only u8 lengths 32/64/65 and use write ignoring count. 0.2.5–0.6.0 emit per-element chunks. 0.6.1–0.9.0 bulk-write supported byte lengths via is_u8, but the fixed-length macro does not supply the current arbitrary-N family. These restricted overlaps are not silently promoted.
<!-- /registry -->

<!-- registry:review:1d264637ee491e80 -->
<a id="review-1d264637ee491e80"></a>

All 22 recorded stable 1.x releases share the InvalidData error profile, exact invalid-tag message and element-callback sequencing. The 0.x predecessors use InvalidInput or still older permissive-tag/UnexpectedEof behavior. Source-operation name changes are mapped explicitly. Error-construction allocation failure is outside the shared model boundary.
<!-- /registry -->

<!-- registry:review:5a0184020050b766 -->
<a id="review-5a0184020050b766"></a>

The complete slice-decoder and element-callback behavior corresponds from 0.6.0 through 0.10.4 and also in yanked 0.11.0, with explicit predecessor Option::deserialize mappings. Before 0.2.10 nonzero tags are accepted; before 0.6.0 short input propagates UnexpectedEof; all 1.x use InvalidData instead of InvalidInput. Tag 1 invokes the actual element implementation exactly once and propagates its finite outcomes; tag 0 does not invoke it. Error-construction allocation failure is outside the shared model boundary.
<!-- /registry -->

<!-- registry:review:8adec8483076679e -->
<a id="review-8adec8483076679e"></a>

From 0.2.7 onward None calls the actual write_all of the writer on [0]; Some calls it on [1], then calls the actual element serializer only after tag success. All callback effects, errors, unwind and terminal exits propagate in source order. The top-level body of Option already looked similar in 0.2.4, but the reached u8 serializer used write and ignored its count until 0.2.5; 0.2.7 is the first write_all release. The 0.1.0 Serializable::write predecessor and all 0.2.0–0.2.5 releases are therefore incompatible. No own diagnostic construction is added by this wrapper.
<!-- /registry -->

<!-- registry:review:817c85bec170cc44 -->
<a id="review-817c85bec170cc44"></a>

The complete family corresponds exactly to Borsh 0.10.4 among all 55 assessed stable releases. It rejects zero-sized elements before reading, reports length-read errors before the hint, returns an empty vector for zero length, preserves the u8 reader specialization, and otherwise applies cautious after the length read and before allocation/element callbacks. The model represents the truncating cast and its panic: positive size 2^32 with nonzero length consumes the header then invokes the panic callback without allocation or element calls; size 2^32 + 1 computes capacity using divisor 1. No upper bound is added. Earlier implementations differ in zero-sized-element handling and/or byte-buffer allocation; 0.10.0–0.10.3 and 0.11.0 allow zero-sized elements and decode one such element for nonzero length, while 0.10.4 rejects them before reading. All 1.x use the different InvalidData/Collections zero-sized error profile. Existing callback, allocation and cleanup boundaries are preserved. The diagnostic-allocation exclusion is shared with other library models. The singleton is the result of the complete release/source review, not a baseline pin.
<!-- /registry -->

<!-- registry:review:217b33b885775461 -->
<a id="review-217b33b885775461"></a>

The complete bool slice-decoder operation corresponds in all 22 stable 1.x releases under the shared error-construction boundary. One read_exact reads the fixed scalar width; the reached helper translates UnexpectedEof to InvalidData, "Unexpected length of input". Every 0.x operation differs: versions before 0.6.0 expose UnexpectedEof or older permissive bool behavior; 0.6.0–0.9.3 use the explicit fixed-slice deserialize predecessor and 0.10.x/0.11.0 use deserialize_reader, with InvalidInput rather than InvalidData. Exactly one byte is consumed. Tags 0 and 1 decode to false and true; any other tag returns "Invalid bool representation: N" with the decimal byte N and the profile-specific error kind. Before 0.2.10 every non-1 byte is accepted as false; through 0.2.5 even empty input returns false. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:383eb0cc40ceec37 -->
<a id="review-383eb0cc40ceec37"></a>

The complete bool slice-decoder operation corresponds in all 19 listed releases under the shared error-construction boundary: Borsh 0.6.0–0.9.3 uses the explicit fixed-slice BorshDeserialize::deserialize predecessor; 0.10.0–0.10.4 and 0.11.0 use deserialize_reader with R = &[u8]. Both return InvalidInput, "Unexpected length of input", on short input. Before 0.6.0 the reached operation exposes UnexpectedEof, "failed to fill whole buffer", or older permissive bool behavior. Every stable 1.x release uses InvalidData instead of InvalidInput. Exactly one byte is consumed. Tags 0 and 1 decode to false and true; any other tag returns "Invalid bool representation: N" with the decimal byte N and the profile-specific error kind. Before 0.2.10 every non-1 byte is accepted as false; through 0.2.5 even empty input returns false. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:fd8854e7622ce840 -->
<a id="review-fd8854e7622ce840"></a>

Every listed compatible release, all 48 stable releases from 0.2.7 onward, performs exactly one call to the actual W::write_all for bool, forwarding its success, ordinary error, partial effects, unwind state or terminal reason under the shared error-construction boundary. u8 writes its single byte; bool writes 0 for false and 1 for true; u32/u64/i64 write their fixed-width little-endian bytes, with signed binary radix-complement conversion. Syntactic IO/slice-import changes and bool delegation to u8 from 0.10.0 preserve that sequence. The seven earlier releases call write once and discard its count, so an overridden write_all or positive short write distinguishes them; Borsh 0.1.0 also reverses bool encoding. No writer-success premise is introduced.
<!-- /registry -->

<!-- registry:review:429a2e1b0a9ae90a -->
<a id="review-429a2e1b0a9ae90a"></a>

The provided forwarding wrapper first appears in 0.10.0 and is byte-identical through 1.8.1, including 0.11.0: Self::deserialize_reader(&mut *buf). It calls the actual reader implementation once and returns its full outcome and remainder, with no own diagnostic construction or allocation. Earlier methods named deserialize are required implementations of the decoding operation, not this provided wrapper; there is no equivalent provided predecessor to alias.
<!-- /registry -->

<!-- registry:review:0cc129944db46b6c -->
<a id="review-0cc129944db46b6c"></a>

This is the same provided forwarding operation as the 0.10.4 registered wrapper. Its complete callback-sensitive body is byte-identical in all 28 releases from 0.10.0 through 1.8.1. Its supplied callback owns any primitive/element diagnostic failures, so those failures do not invalidate this wrapper when the existing actual-callback premise is satisfied. Earlier deserialize implementations are not this provided body.
<!-- /registry -->

<!-- registry:review:da68bb645d21593b -->
<a id="review-da68bb645d21593b"></a>

The complete slice-wrapper/callback behavior exists from 0.6.0. The wrapper calls the actual Self::deserialize override exactly once and tests its resulting local slice; leftover bytes produce the stated error. 0.1.0–0.2.3 do not reject trailing input; 0.2.4–0.5.0 inspect Cursor.position instead of the resulting slice of the callback and can disagree for a valid callback that replaces the Cursor. Destructors of the discarded successful value retain the existing unobservability obligation. Error-construction allocation failure is outside the shared model boundary.
<!-- /registry -->

<!-- registry:review:c73c802ae93575b2 -->
<a id="review-c73c802ae93575b2"></a>

The provided method returns Ok(None) without reading, callbacks or allocation at every index. Explicit predecessor mapping admits vec_from_bytes(len, &mut &[u8]) in 0.9.1–0.9.3; the reader-named version exists from 0.10.0. Both bodies ignore length and reader and preserve the complete slice. Earlier is_u8 metadata helpers are not equivalent provided decoding operations. u8 overrides returning Some are outside this default-method contract.
<!-- /registry -->

<!-- registry:review:161a91fa75c09981 -->
<a id="review-161a91fa75c09981"></a>

All 47 helper-present stable releases correspond to the unrestricted family. Every published src/de/hint.rs body casts size_of::<T>() to u32 before evaluating 4096 / divisor, then min with the u32 hint and max with 1. The model represents that cast as size % 2^32 and represents division-by-zero through an explicit panic callback, so size 2^32 panics and size 2^32 + 1 uses divisor 1. There is no size < 2^32 premise. The helper is absent in the eight enumerated earlier releases. The three retained source-closure groups differ only in imports/formatting and share this arithmetic and order.
<!-- /registry -->

<!-- registry:review:9ea05dbdb8b57bf7 -->
<a id="review-9ea05dbdb8b57bf7"></a>

The complete f64 slice-decoder operation corresponds in all 22 stable 1.x releases under the shared error-construction boundary. One read_exact reads the fixed scalar width; the reached helper translates UnexpectedEof to InvalidData, "Unexpected length of input". Every 0.x operation differs: versions before 0.6.0 expose UnexpectedEof or older permissive bool behavior; 0.6.0–0.9.3 use the explicit fixed-slice deserialize predecessor and 0.10.x/0.11.0 use deserialize_reader, with InvalidInput rather than InvalidData. Non-NaN IEEE-754 bits are preserved, including signed zeros, subnormals and infinities. Every NaN sign/payload returns InvalidData, "For portability reasons we do not allow to deserialize NaNs.", after consuming eight bytes. Pre-0.2.4 float decoding intentionally panics on NaN; later 0.x returns InvalidInput. The intentional panic remains in scope. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:4173a0841390920e -->
<a id="review-4173a0841390920e"></a>

The complete f64 serializer family corresponds in all 22 stable 1.x releases under the shared error-construction boundary. Every NaN sign/payload returns InvalidData, "For portability reasons we do not allow to serialize NaNs.", before any writer call. Other IEEE-754 bits, including signed zero, subnormals and infinities, are passed unchanged as one eight-byte little-endian chunk to the actual W::write_all. The indexed provider retains every other ordinary error, partial effect, unwind state and terminal reason. Every 0.x release intentionally panics on NaN; that panic is in scope and makes the complete family incompatible. Additionally, 0.1.0–0.2.5 call write once and discard its short count on non-NaNs. Custom-allocator failure during NaN error construction lies outside the shared model boundary and does not determine version incompatibility.
<!-- /registry -->

<!-- registry:review:9bad8eaa5a89fe49 -->
<a id="review-9bad8eaa5a89fe49"></a>

The complete i32 slice-decoder operation corresponds in all 22 stable 1.x releases under the shared error-construction boundary. One read_exact reads the fixed scalar width; the reached helper translates UnexpectedEof to InvalidData, "Unexpected length of input". Every 0.x operation differs: versions before 0.6.0 expose UnexpectedEof or older permissive bool behavior; 0.6.0–0.9.3 use the explicit fixed-slice deserialize predecessor and 0.10.x/0.11.0 use deserialize_reader, with InvalidInput rather than InvalidData. Fixed-width little-endian conversion yields the exact unsigned value or signed binary radix-complement interpretation; the fixed-length conversion cannot fail after the length check or successful read. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:ed801cbd6396ba7b -->
<a id="review-ed801cbd6396ba7b"></a>

The complete i64 slice-decoder operation corresponds in all 22 stable 1.x releases under the shared error-construction boundary. One read_exact reads the fixed scalar width; the reached helper translates UnexpectedEof to InvalidData, "Unexpected length of input". Every 0.x operation differs: versions before 0.6.0 expose UnexpectedEof or older permissive bool behavior; 0.6.0–0.9.3 use the explicit fixed-slice deserialize predecessor and 0.10.x/0.11.0 use deserialize_reader, with InvalidInput rather than InvalidData. Fixed-width little-endian conversion yields the exact unsigned value or signed binary radix-complement interpretation; the fixed-length conversion cannot fail after the length check or successful read. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:9d69c2467e12cf12 -->
<a id="review-9d69c2467e12cf12"></a>

Every listed compatible release, all 48 stable releases from 0.2.7 onward, performs exactly one call to the actual W::write_all for i64, forwarding its success, ordinary error, partial effects, unwind state or terminal reason under the shared error-construction boundary. u8 writes its single byte; bool writes 0 for false and 1 for true; u32/u64/i64 write their fixed-width little-endian bytes, with signed binary radix-complement conversion. Syntactic IO/slice-import changes and bool delegation to u8 from 0.10.0 preserve that sequence. The seven earlier releases call write once and discard its count, so an overridden write_all or positive short write distinguishes them; Borsh 0.1.0 also reverses bool encoding. No writer-success premise is introduced.
<!-- /registry -->

<!-- registry:review:6719fef64be9c7d5 -->
<a id="review-6719fef64be9c7d5"></a>

The complete i8 slice-decoder operation corresponds in all 19 listed releases under the shared error-construction boundary: Borsh 0.6.0–0.9.3 uses the explicit fixed-slice BorshDeserialize::deserialize predecessor; 0.10.0–0.10.4 and 0.11.0 use deserialize_reader with R = &[u8]. Both return InvalidInput, "Unexpected length of input", on short input. Before 0.6.0 the reached operation exposes UnexpectedEof, "failed to fill whole buffer", or older permissive bool behavior. Every stable 1.x release uses InvalidData instead of InvalidInput. Fixed-width little-endian conversion yields the exact unsigned value or signed binary radix-complement interpretation; the fixed-length conversion cannot fail after the length check or successful read. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:da0a6a33f4d4c193 -->
<a id="review-da0a6a33f4d4c193"></a>

The provided no_std loop corresponds in 35 source releases from 0.8.0; 34 have a usable unmodified no_std build. It offers the current suffix to write; retries Interrupted unchanged after dropping the error; maps Ok(0) to WriteZero through the explicitly indexed String-allocation callback; handles count > length through the explicitly indexed slice-panic callback; and propagates every other callback exit. The method is not used with borsh std or a Write::write_all override. Error construction/kind/display and feature re-exports were reviewed along with the loop. 0.9.2 has source correspondence but its published no_std crate cannot build because of an unrelated missing vec macro import; its source correspondence does not provide a usable build and this profile excludes it.
<!-- /registry -->

<!-- registry:review:a829473bc4dd9b62 -->
<a id="review-a829473bc4dd9b62"></a>

The complete u32 slice-decoder operation corresponds in all 22 stable 1.x releases under the shared error-construction boundary. One read_exact reads the fixed scalar width; the reached helper translates UnexpectedEof to InvalidData, "Unexpected length of input". Every 0.x operation differs: versions before 0.6.0 expose UnexpectedEof or older permissive bool behavior; 0.6.0–0.9.3 use the explicit fixed-slice deserialize predecessor and 0.10.x/0.11.0 use deserialize_reader, with InvalidInput rather than InvalidData. Fixed-width little-endian conversion yields the exact unsigned value or signed binary radix-complement interpretation; the fixed-length conversion cannot fail after the length check or successful read. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:68714ba2dbf9bad5 -->
<a id="review-68714ba2dbf9bad5"></a>

The complete u32 slice-decoder operation corresponds in all 19 listed releases under the shared error-construction boundary: Borsh 0.6.0–0.9.3 uses the explicit fixed-slice BorshDeserialize::deserialize predecessor; 0.10.0–0.10.4 and 0.11.0 use deserialize_reader with R = &[u8]. Both return InvalidInput, "Unexpected length of input", on short input. Before 0.6.0 the reached operation exposes UnexpectedEof, "failed to fill whole buffer", or older permissive bool behavior. Every stable 1.x release uses InvalidData instead of InvalidInput. Fixed-width little-endian conversion yields the exact unsigned value or signed binary radix-complement interpretation; the fixed-length conversion cannot fail after the length check or successful read. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:7b64bf329114bd07 -->
<a id="review-7b64bf329114bd07"></a>

Every listed compatible release, all 48 stable releases from 0.2.7 onward, performs exactly one call to the actual W::write_all for u32, forwarding its success, ordinary error, partial effects, unwind state or terminal reason under the shared error-construction boundary. u8 writes its single byte; bool writes 0 for false and 1 for true; u32/u64/i64 write their fixed-width little-endian bytes, with signed binary radix-complement conversion. Syntactic IO/slice-import changes and bool delegation to u8 from 0.10.0 preserve that sequence. The seven earlier releases call write once and discard its count, so an overridden write_all or positive short write distinguishes them; Borsh 0.1.0 also reverses bool encoding. No writer-success premise is introduced.
<!-- /registry -->

<!-- registry:review:b4d7ff5a84e5b333 -->
<a id="review-b4d7ff5a84e5b333"></a>

The declared 1.x range assumes preservation of this R = &[u8] contract, including exact errors and the successful eight-byte advance. The complete u64 slice-decoder operation corresponds in all 22 stable 1.x releases under the shared error-construction boundary. One read_exact reads the fixed scalar width; the reached helper translates UnexpectedEof to InvalidData, "Unexpected length of input". Every 0.x operation differs: versions before 0.6.0 expose UnexpectedEof or older permissive bool behavior; 0.6.0–0.9.3 use the explicit fixed-slice deserialize predecessor and 0.10.x/0.11.0 use deserialize_reader, with InvalidInput rather than InvalidData. Fixed-width little-endian conversion yields the exact unsigned value or signed binary radix-complement interpretation; the fixed-length conversion cannot fail after the length check or successful read. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:623cf74e78b3d503 -->
<a id="review-623cf74e78b3d503"></a>

The complete u64 slice-decoder operation corresponds in all 19 listed releases under the shared error-construction boundary: Borsh 0.6.0–0.9.3 uses the explicit fixed-slice BorshDeserialize::deserialize predecessor; 0.10.0–0.10.4 and 0.11.0 use deserialize_reader with R = &[u8]. Both return InvalidInput, "Unexpected length of input", on short input. Before 0.6.0 the reached operation exposes UnexpectedEof, "failed to fill whole buffer", or older permissive bool behavior. Every stable 1.x release uses InvalidData instead of InvalidInput. Fixed-width little-endian conversion yields the exact unsigned value or signed binary radix-complement interpretation; the fixed-length conversion cannot fail after the length check or successful read. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:5a4b2e1260a5295a -->
<a id="review-5a4b2e1260a5295a"></a>

The declared 0.10.x range assumes preservation of this R = &[u8] contract, including exact errors and the successful eight-byte advance; the independent 0.11.0 reference does not admit future 0.11.x releases. The complete u64 slice-decoder operation corresponds in all 19 listed releases under the shared error-construction boundary: Borsh 0.6.0–0.9.3 uses the explicit fixed-slice BorshDeserialize::deserialize predecessor; 0.10.0–0.10.4 and 0.11.0 use deserialize_reader with R = &[u8]. Both return InvalidInput, "Unexpected length of input", on short input. Before 0.6.0 the reached operation exposes UnexpectedEof, "failed to fill whole buffer", or older permissive bool behavior. Every stable 1.x release uses InvalidData instead of InvalidInput. Fixed-width little-endian conversion yields the exact unsigned value or signed binary radix-complement interpretation; the fixed-length conversion cannot fail after the length check or successful read. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:813a7ad30c8a6a1b -->
<a id="review-813a7ad30c8a6a1b"></a>

Every listed compatible release, all 48 stable releases from 0.2.7 onward, performs exactly one call to the actual W::write_all for u64, forwarding its success, ordinary error, partial effects, unwind state or terminal reason under the shared error-construction boundary. u8 writes its single byte; bool writes 0 for false and 1 for true; u32/u64/i64 write their fixed-width little-endian bytes, with signed binary radix-complement conversion. Syntactic IO/slice-import changes and bool delegation to u8 from 0.10.0 preserve that sequence. The seven earlier releases call write once and discard its count, so an overridden write_all or positive short write distinguishes them; Borsh 0.1.0 also reverses bool encoding. No writer-success premise is introduced.
<!-- /registry -->

<!-- registry:review:44a6b782c29da279 -->
<a id="review-44a6b782c29da279"></a>

The complete u8 array_from_reader family corresponds in all 22 stable 1.x releases under the shared error-construction boundary. For every const N the source creates [0u8; N], calls read_exact once, and returns Ok(Some(array)); N = 0 consumes no input. The reached short-input helper returns InvalidData, "Unexpected length of input". The method exists from 0.10.0, but 0.10.x and 0.11.0 use InvalidInput and are incompatible. Before 0.10.0 this complete operation is absent: the 0.9.1–0.9.3 copy_from_bytes helper instead mutates a caller-supplied output slice and returns bool. Success consumes exactly N bytes; the existing contract permits either retained or emptied error remainders. The array fast-path method itself is not feature-gated by const-generics.
<!-- /registry -->

<!-- registry:review:0031c987619b4804 -->
<a id="review-0031c987619b4804"></a>

The complete u8 slice-decoder operation corresponds in all 22 stable 1.x releases under the shared error-construction boundary. One read_exact reads the fixed scalar width; the reached helper translates UnexpectedEof to InvalidData, "Unexpected length of input". Every 0.x operation differs: versions before 0.6.0 expose UnexpectedEof or older permissive bool behavior; 0.6.0–0.9.3 use the explicit fixed-slice deserialize predecessor and 0.10.x/0.11.0 use deserialize_reader, with InvalidInput rather than InvalidData. Fixed-width little-endian conversion yields the exact unsigned value or signed binary radix-complement interpretation; the fixed-length conversion cannot fail after the length check or successful read. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:e59ff90f9417543d -->
<a id="review-e59ff90f9417543d"></a>

The complete u8 slice-decoder operation corresponds in all 19 listed releases under the shared error-construction boundary: Borsh 0.6.0–0.9.3 uses the explicit fixed-slice BorshDeserialize::deserialize predecessor; 0.10.0–0.10.4 and 0.11.0 use deserialize_reader with R = &[u8]. Both return InvalidInput, "Unexpected length of input", on short input. Before 0.6.0 the reached operation exposes UnexpectedEof, "failed to fill whole buffer", or older permissive bool behavior. Every stable 1.x release uses InvalidData instead of InvalidInput. Fixed-width little-endian conversion yields the exact unsigned value or signed binary radix-complement interpretation; the fixed-length conversion cannot fail after the length check or successful read. Success advances the slice by the scalar width. The contract deliberately leaves the remaining slice after an error unconstrained: the pinned std read_exact empties a short slice, while the predecessor and Borsh no_std implementation retain it. No additional reader callback domain is admitted by the predecessor mapping, and it does not create a registered older callable binding.
<!-- /registry -->

<!-- registry:review:0d0a895ee5184226 -->
<a id="review-0d0a895ee5184226"></a>

Every listed compatible release, all 48 stable releases from 0.2.7 onward, performs exactly one call to the actual W::write_all for u8, forwarding its success, ordinary error, partial effects, unwind state or terminal reason under the shared error-construction boundary. u8 writes its single byte; bool writes 0 for false and 1 for true; u32/u64/i64 write their fixed-width little-endian bytes, with signed binary radix-complement conversion. Syntactic IO/slice-import changes and bool delegation to u8 from 0.10.0 preserve that sequence. The seven earlier releases call write once and discard its count, so an overridden write_all or positive short write distinguishes them; Borsh 0.1.0 also reverses bool encoding. No writer-success premise is introduced.
<!-- /registry -->

<!-- registry:review:8dfa24b545c6e0d4 -->
<a id="review-8dfa24b545c6e0d4"></a>

All 31 stable releases from 0.9.1 onward implement the u8_slice override as exactly Some(slice). The original pointer, length, contents and borrow are retained, with no copy, allocation or callback. The method is not gated by const-generics. Earlier is_u8 predicates do not perform this borrowed-slice operation, so the API is absent before 0.9.1. Native pointer and length equality assertions supplement the source argument in every buildable std/no_std profile.
<!-- /registry -->

<!-- registry:review:b6f2b6bd1f8ce54d -->
<a id="review-b6f2b6bd1f8ce54d"></a>

All 26 API releases have the identical impl_try_from_slice_unchecked macro and the v1 Borsh trait dispatch. The wrapper copies the input slice reference locally, invokes actual T::deserialize exactly once, propagates its error or nonreturning behavior and state effects, and discards the remaining local slice on success. There is no trailing-byte rejection, re-decoding, allocation or additional callback. Dependency feature changes in 3.0.1/3.0.2 affect the chosen IO representation but not this generic contract. 0.0.1 is a placeholder without the API. Stateful overridden callbacks were executed across the release transitions, including the 3.0.2 no_std dependency profile.
<!-- /registry -->

<!-- registry:review:9546e92a4c193d63 -->
<a id="review-9546e92a4c193d63"></a>

Reference: solana-borsh 2.2.1. Compatibility in [2.2.1, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: Preserve the actual v0_10 generic serializer and WriteCounter interaction: fresh zero count; each write counts its full buffer and returns its length; flush preserves count; return the count only after serializer success. Bind wordBits and checkedOverflow to the actual usize/configuration, retaining checked panic before count update or unchecked wrapping. Preserve writer-error handling, serializer effects, caught unwind, owned IO error resources, cleanup and terminal outcomes. Arbitrary continuations and divergence remain allowed; finite-fuel replay and a compatibility range provide no serializer-termination premise.
<!-- /registry -->
