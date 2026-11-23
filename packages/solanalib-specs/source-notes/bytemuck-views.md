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
