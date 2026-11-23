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
