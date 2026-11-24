# Callback, unchecked Borsh and logging models

`Solanalib.Contracts.Model.Callback` sequences the existing common outcome relation.
A returned callback supplies the state of the next callback. An unwind carries
its actual state through the wrapper; termination carries its reason without an
invented final state. Ordinary error values remain inside `Except` and are
separate from both exits. The helpers introduce no alternate outcome universe.

The `v1::try_from_slice_unchecked` of Solana Borsh 3.0.2 invokes the supplied
`T::deserialize` callback once on the input slice, then discards its local
remaining-slice reference. It does not require that the remainder be empty and
does not add a trailing-byte error. The model preserves the exact
ordinary result and effects of the callback, including changed state on error, unwind and
termination. It does not impose a suffix property on the local remainder:
an arbitrary implementation of the trait can replace that reference. Concrete
deserializers and their layouts are separate callback interpretations.

The byte-writer helper forwards a single `write_all` callback. Its user supplies
the complete bytes, success or ordinary error, and any partial writer changes.
It neither assumes complete successful writes nor rolls back effects on error.
The Address 2.6.0 derived serializer runs the
Borsh 1.6.1 `[T; N]` model, as described below. A concrete writer implementation
remains a separate source binding. Tests include accepted trailing data, an
empty-input error, changed state on unwind, terminal writer failure and a
partial-write error.

Logging retains the structured callback event before any canonical projection.
Solana Msg 3.1.0 selects a syscall text event containing the exact UTF-8 bytes on
Solana, a stdout-line callback on host builds with `std`, and the unchanged
returning state without a callback on host builds without `std`. A stdout or
syscall callback may unwind or terminate; the model does not suppress that exit.

The `sol_log_data` of Solana Program 4.0.0 forwards the ordered nested byte slices to
the Solana callback, or to a distinct host-stub callback. Empty inner fields and
field boundaries remain observable. `Log.Event.runtimeBytes` supplies the coarse text bytes of the
canonical model/data flattening only; different nested
events can have the same flattened projection. It is not a claim about base64,
prefixes, rendered output, metering or the formatting of a concrete host stub. Anchor
uses this callback vocabulary in its versioned wrapper.

Ordinary source anchors:

| Package | Immutable source | Anchors |
| --- | --- | --- |
| Solana Borsh 3.0.2 | [macros.rs](https://github.com/anza-xyz/solana-sdk/blob/ee893bd4247a632b6738b393994d46f5bc2dcb00/borsh/src/macros.rs#L77), [v1.rs](https://github.com/anza-xyz/solana-sdk/blob/ee893bd4247a632b6738b393994d46f5bc2dcb00/borsh/src/v1.rs#L13) | One deserialize callback and no remainder check, instantiated for Borsh v1 |
| Borsh 1.6.1 support | [ser/mod.rs](https://github.com/near/borsh-rs/blob/f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac/borsh/src/ser/mod.rs#L576) | u8 slice specialization 72; array implementation 576; nonempty byte-array `write_all` 585 |
| Solana Msg 3.1.0 | [lib.rs](https://github.com/anza-xyz/solana-sdk/blob/8f24de0096f939bf75262a645f2d4280b9d1cfd8/msg/src/lib.rs#L54) | Solana, host-with-std and host-without-std branches |
| Solana Program 4.0.0 | [log.rs](https://github.com/anza-xyz/solana-sdk/blob/12b63164cc1854b798362190583de5d1f2fe8091/program/src/log.rs#L52) | Ordered nested fields and target-selected callback |

The versioned callback contracts have closed universal family references and
closed sample satisfiability and execution witnesses. Those samples establish
mathematical consistency, not the behavior of an actual writer, deserializer,
stdout implementation or Solana runtime. Rust implementation and representation
proofs remain outside this layer.

## Address 2.6.0 Borsh derive

`solana_address::Address` 2.6.0 derives `BorshSerialize` and `BorshDeserialize`
at line 90 with `borsh(crate = "borsh")`; its only field is the private
`[u8; 32]` at line 101. Borsh-derive 1.6.1 generates one statement per field.
The serializer calls `BorshSerialize::serialize(&self.0, writer)?` and then
returns `Ok(())`. The decoder returns
`Ok(Self(BorshDeserialize::deserialize_reader(reader)?))`. Both derived bodies
are code in solana-address 2.6.0. Their callees are the Borsh 1.6.1 `[T; N]`
implementations, so each Address model calls the Borsh 1.6.1 array model.

Serialization uses the array implementation at `ser/mod.rs` line 576. For
`N = 32` the zero-length branch is skipped. `u8::u8_slice` returns the whole
array, so the implementation makes exactly one `write_all` call with all 32
bytes (line 585) and never takes the per-element loop. The derived `?` and
`Ok(())` return the result of that call unchanged. The model provides
`serialize_contract`: one writer callback on the 32 address bytes, with its
ordinary error, partial writer changes, unwind state and terminal reason kept
unchanged. Its reference runs the registered Borsh 1.6.1 array serializer at
`T = u8`, `N = 32`. The family uses the Borsh writer index: the writer `W` is a
source type parameter and `write_all` returns `io::Result<()>`. The index
therefore supplies the writer callback and the Borsh `io::Error` observation.

Decoding uses the array implementation at `de/mod.rs` line 768. Line 810 first
asks `T::array_from_reader`. The u8 specialization at line 188 returns
`Some(array)` after one `read_exact` of 32 bytes. It maps `UnexpectedEof` to
`InvalidData` with the message "Unexpected length of input" (lines 27 and 138).
The generic loop and its drop guard are therefore never reached for bytes. The
model is stated over the remaining byte slice of the reader; the standard-library
`read_exact` itself is not modeled. Success returns the first 32 bytes as the
address and leaves every later byte unread. A shorter input returns the mapped
error. With the default `std` feature of Borsh, the slice is empty afterwards,
because the `Read for &[u8]` of std (nightly-2026-05-01, `io/impls.rs` lines
348–353) empties the slice before it reports `UnexpectedEof`. The `no_std` reader of Borsh (`nostd_io.rs` line 1039) leaves the slice unchanged. That
difference affects only the remaining slice, not the error. The contract
therefore leaves the remaining slice after an error unconstrained. The
reference follows std, which Borsh enables by default; a client establishes
the feature from its own feature resolution.
The derived decoder adds no check of its own: every 32-byte value is accepted.
It does not check the curve or any other property of the address.

Tests cover a 31-byte input, an exact 32-byte input, trailing bytes left
unread, the use of the first rather than the last 32 bytes, a single 32-byte
write (two chunks or a shorter chunk are rejected), and a round trip for every
address from the single write of the serializer through the decoder.

| Package | Immutable source | Anchors |
| --- | --- | --- |
| Solana Address 2.6.0 | [lib.rs](https://github.com/anza-xyz/solana-sdk/blob/b658e468fe1c0021dd86c1175dea5ee92cd28a08/address/src/lib.rs#L90) | Borsh derive 90; `[u8; 32]` field 101 |
| Borsh 1.6.1 | [ser/mod.rs](https://github.com/near/borsh-rs/blob/f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac/borsh/src/ser/mod.rs#L576) | u8 slice 72; array serializer 576; one `write_all` 585 |
| Borsh 1.6.1 | [de/mod.rs](https://github.com/near/borsh-rs/blob/f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac/borsh/src/de/mod.rs#L768) | length message 27; EOF mapping 138; u8 `array_from_reader` 188; array decoder 768; specialization call 810 |
| Borsh-derive 1.6.1 | [structs (ser)](https://github.com/near/borsh-rs/blob/f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac/borsh-derive/src/internals/serialize/structs/mod.rs#L36), [structs (de)](https://github.com/near/borsh-rs/blob/f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac/borsh-derive/src/internals/deserialize/structs/mod.rs#L24) | One field statement each, in declaration order |

This review compares the derive output with the pinned generator sources. It
does not prove the expanded Rust body, a concrete writer or reader, or compiler
correspondence.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:1df0300cd6018eba -->
<a id="review-1df0300cd6018eba"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Versioned public aggregate of the reviewed mathematical models.

Instantiate the shared mathematical operations for this exact SDK version; keep closed reference, precondition and execution witnesses in the public version namespace.

Versioned aggregate of the exact registered callable utility models; coverage is the listed API subset.

Solana-msg 2.2.1 calls sol_log_ with the UTF-8 pointer and byte length under target_os = solana. Its complementary branch unconditionally calls println!("{}", message); there is no host-no-std noop profile or alloc/std feature selection in this release. Source formatting, output failure and runtime effects are interpreted by the selected sink.

Generated typed capability catalog retains every complete registered family, exact Rust identity, source/build profile and closed reference witness.
<!-- /registry -->

<!-- registry:review:f829629b6be9428c -->
<a id="review-f829629b6be9428c"></a>

The complete three-target family corresponds to 3.0.0 and 3.1.0: target_os=solana forwards the UTF-8 bytes and byte length to sol_log_; a non-Solana build with std uses println!; a non-Solana build without std uses black_box and has no log event. All 23 earlier real releases have the same Solana forwarding and host printing branches, but cannot realize the hostNoStd configuration of the family: they unconditionally print on non-Solana builds. Their Solana and hostStd branches were separately tested where listed; they are not full-family compatibility. The 0.0.1 package is a placeholder. The reached syscall declaration and macro were reviewed across the resolved major-version transitions; the sink relation still supplies printing, panic, termination and backend effects.
<!-- /registry -->

<!-- registry:review:9c5da246aa651a5e -->
<a id="review-9c5da246aa651a5e"></a>

Solana-msg 2.2.1 calls sol_log_ with the UTF-8 pointer and byte length under target_os = solana. Its complementary branch unconditionally calls println!("{}", message); there is no host-no-std noop profile or alloc/std feature selection in this release. Source formatting, output failure and runtime effects are interpreted by the selected sink. The declared compatible range assumes preservation of the UTF-8 syscall request on Solana and unconditional formatted stdout line on the host, including the state, unwind of the selected sink and terminal outcomes. It does not admit a host no-op branch.
<!-- /registry -->
