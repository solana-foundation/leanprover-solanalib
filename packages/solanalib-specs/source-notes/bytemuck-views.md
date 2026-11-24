# Bytemuck 1.25.0 and 1.25.2 byte views and zeroing

The reviewed files belong to
[`Lokathor/bytemuck`](https://github.com/Lokathor/bytemuck) at revision
`164cedda0eae131bc6cb67902599f4ec253642ca` (1.25.0) and
`f363643e951a7ac9e4b9921de982f2b0918902e3` (1.25.2). The
[source registry](../source-map.json) pins `src/lib.rs`, `src/internal.rs` and
`src/zeroable.rs` of each version. `internal.rs` and `zeroable.rs` are
identical in both versions. The `lib.rs` differences, a `spirv` condition on
`core::error::Error` and a documentation note on empty slices, do not affect
the modeled functions.

Shared definitions are in
[`Solanalib/Specs/Core/Bytemuck.lean`](../Solanalib/Specs/Core/Bytemuck.lean).
The catalog registers `bytes_of`, `try_from_bytes` and `Zeroable::zeroed`;
the applicability profiles select the reviewed versions for each. Each
model is a `Family` indexed by the selected type `T`: its layout
(`size_of::<T>()`, `align_of::<T>()`) together with its byte encoding
(`NoUninit`) or its decoding (`AnyBitPattern`, `Zeroable`). References are
executable Lean functions registered as their graphs. No model changes state,
and no model has an unwind or terminal exit.

## `bytes_of`

`bytes_of::<T>(t)` calls `internal::bytes_of`, which casts
`slice::from_ref(t)` with `try_cast_slice::<T, u8>` and maps `Err` to
`unreachable!()`. `tryCastSlice` follows the source branches in order:
alignment, equal size, divisible size (including the zero-sized target
branch), then slop. For the target `u8`, the alignment branch needs
`align_of::<T>() < 1` and the slop branch needs a byte count not divisible by
one, so neither branch is reachable (`tryCastSlice_toBytes`). The result is
`slice::from_raw_parts(t as *const u8, size_of::<T>())`: the same address and
exactly the bytes of the value.

The pinned source has no separate zero-sized branch in `bytes_of`. A
zero-sized `T` takes the divisible branch with zero elements. The result is an
empty slice at the reference address (`bytesOf_zero_sized`). The doc comment
allows a different pointer value for this case; the model follows the body.

## `try_from_bytes`

`try_from_bytes::<T>(s)` calls `internal::try_from_bytes`. It first compares
`s.len()` with `size_of::<T>()` and returns `SizeMismatch` on any difference,
whatever the address. It then checks `is_aligned_to(s.as_ptr(), align_of::<T>())`
and returns `TargetAlignmentGreaterAndInputNotAligned` on failure. The 1.25.2
documentation states that this check applies to empty slices; the 1.25.0 body
is identical. Success returns `&*(s.as_ptr() as *const T)`: a reference at the
slice address whose value is decoded from the slice bytes. The model takes the
slice address as an explicit argument, so alignment failure is observable.
`TryFromBytesPost` states the result declaratively; `tryFromBytesPost_iff`
shows that it determines the reference result. The function produces neither
`OutputSliceWouldHaveSlop` nor `AlignmentMismatch`.

`is_aligned_to` has two feature branches, `ptr.align_offset(align) == 0` and
`ptr as usize % align == 0`. At run time both decide `address % align = 0` for
a power-of-two `align`. The model uses that condition. Which branch the client
build selects is a binding obligation.

## `Zeroable::zeroed`

The default trait method calls `core::mem::zeroed()`. The model returns the
value decoded from `size_of::<T>()` zero bytes. `core::mem::zeroed` is not
modeled; only its effect on bytes is recorded. The `Zeroable` safety contract
requires an inhabited type for which the all-zero pattern is valid. Under that
contract the zero-validity check inside `core::mem::zeroed` does not fail, so
the model has no panic exit; the binding must justify the contract for the
selected impl. A type that overrides `zeroed`, contrary to the trait contract,
is outside the model.

## Limits

- Layout values, the encoding of each value and the decoding of each valid
  pattern are supplied by the binding for the selected `T` and target. The
  shared `Sample` types (`u64`, `()`, a zero-sized type with alignment eight)
  are instantiations for witnesses and tests, not target claims.
- `SliceRef` and `TypedRef` carry a pointer value and the observed bytes or
  value. Validity, provenance, lifetime and the aliasing of the returned
  reference with its input are binding obligations. The models state only that
  the address is preserved.
- `slice::from_raw_parts`, `slice::from_ref`, `core::mem::size_of_val` and
  pointer casts are described by their effect on address, length and bytes.
  No standard-library function is modeled.
- These are mathematical models compared manually with the pinned source.
  Rust body, compiler layout and runtime correspondence remain open.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:c9d5121329f3d21a -->
<a id="review-c9d5121329f3d21a"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

bytes_of and default Zeroable::zeroed of bytemuck 1.25.2 as Families indexed by the layout of the selected type and encoding or decoding. bytes_of returns the reference address and exactly the size_of::<T>() bytes of the value, empty for a zero-sized type, following the pinned try_cast_slice path; zeroed returns the value of the all-zero pattern. Executable references are registered as graphs with closed reference, satisfiability and execution witnesses at the u64 sample.

try_from_bytes and default Zeroable::zeroed of bytemuck 1.25.0 as Families indexed by the layout of the selected type and decoding. try_from_bytes reports SizeMismatch for any length other than size_of::<T>() regardless of address, then TargetAlignmentGreaterAndInputNotAligned for a misaligned slice address (also for empty slices), and otherwise returns a reference at the slice address with the decoded value; the declarative post determines the result. zeroed returns the value of the all-zero pattern. Executable references are registered as graphs with closed witnesses at the u64 sample.
<!-- /registry -->

<!-- registry:review:6119753468787605 -->
<a id="review-6119753468787605"></a>

1.16.3 removes the literal empty-slice shortcut and changes reached try_cast_slice to accept zero input bytes. For target u8, alignment and slop errors are impossible; all sized and zero-sized cases keep the input address and expose exactly size_of<T>() bytes. Every later published release has the same reached behavior, with equivalent modulo/align_offset branches. Earlier releases violate complete ZST behavior: 1.2.0–1.5.0 panic; other earlier releases return literal &[] at an unrelated address. Before 1.9.0 the public bound is additionally Pod rather than the full NoUninit domain.
<!-- /registry -->

<!-- registry:review:6a3879fc3666b87b -->
<a id="review-6a3879fc3666b87b"></a>

From 1.9.0 onward the public AnyBitPattern entry calls the reached internal routine, which checks exact length before alignment and returns the input-address reference on success. Before 1.14.0 alignment is integer modulo; 1.14.0+ adds the equivalent align_offset feature branch. The ZST still needs alignment. 1.1.0/1.2.0 use AlignmentMismatch, and 1.3.0–1.8.0 retain the narrower Pod domain despite matching equations on that subset. API absent through 1.0.1.
<!-- /registry -->

<!-- registry:review:3b821bb56247500f -->
<a id="review-3b821bb56247500f"></a>

The default trait body is unsafe { core::mem::zeroed() } throughout every published stable release. It has no target or feature branch and does not require Pod, NoUninit or AnyBitPattern. Existing restrictions to the default method and a valid Zeroable implementation are preserved, so custom overrides are outside this contract throughout.
<!-- /registry -->
