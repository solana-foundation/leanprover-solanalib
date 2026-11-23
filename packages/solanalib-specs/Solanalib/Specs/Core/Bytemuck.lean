/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Family
public import Solanalib.Runtime.Basic

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Bytemuck

/-- `size_of::<T>()` and `align_of::<T>()` of one selected Rust type on the
selected target. Rust guarantees a power-of-two alignment and a size that is a
multiple of it. The binding supplies the actual values; no target is assumed. -/
structure Layout where
  /-- `size_of::<T>()`; zero for a zero-sized type. -/
  size : Nat
  /-- `align_of::<T>()`. -/
  align : Nat
  /-- Rust alignments are powers of two, in particular nonzero. -/
  align_pow : ∃ k, align = 2 ^ k
  /-- Rust sizes are multiples of the alignment. -/
  size_aligned : size % align = 0

namespace Layout

theorem align_pos (layout : Layout) : 0 < layout.align := by
  obtain ⟨k, same⟩ := layout.align_pow
  rw [same]
  exact Nat.two_pow_pos k

/-- `u8`: one byte with alignment one, the target element of `bytes_of`. -/
def u8 : Layout := ⟨1, 1, ⟨0, rfl⟩, rfl⟩

end Layout

/-- A shared byte-slice reference `&[u8]`: the address of its first byte and
the bytes currently observed through it. The slice length is `bytes.length`.
Validity, provenance and lifetime of the reference are binding obligations. -/
structure SliceRef where
  /-- The pointer value `s.as_ptr() as usize`, also for an empty slice. -/
  address : Nat
  /-- The initialized bytes observed through the slice. -/
  bytes : Solanalib.Runtime.Bytes
  deriving DecidableEq, Repr

/-- A shared typed reference `&T`: its pointer value and the value observed
through it. A cast result keeps the address of its input, so it aliases the
same memory; the binding relates both references to that memory. -/
structure TypedRef (Value : Type) where
  /-- The pointer value of the reference. -/
  address : Nat
  /-- The value of type `T` observed through the reference. -/
  value : Value
  deriving DecidableEq, Repr

/-- `bytemuck::PodCastError` with every source variant, in source order. -/
inductive PodCastError where
  /-- The target alignment is greater and the input address is not aligned. -/
  | TargetAlignmentGreaterAndInputNotAligned
  /-- The output slice would not be a whole number of elements. -/
  | OutputSliceWouldHaveSlop
  /-- Source and destination sizes of a single-value cast differ. -/
  | SizeMismatch
  /-- Alignments differ in an allocation cast (`Box`, `Vec`). -/
  | AlignmentMismatch
  deriving DecidableEq, Repr

/-- A `T: NoUninit` instantiation: its layout and the bytes of each value.
Every byte is initialized, so the encoding has exactly `size_of::<T>()` bytes. -/
structure Encoding where
  /-- Mathematical values of the selected Rust type. -/
  Value : Type
  /-- The size and alignment of the selected type. -/
  layout : Layout
  /-- The in-memory bytes of a value, in address order. -/
  encode : Value → Solanalib.Runtime.Bytes
  /-- A value occupies exactly `size_of::<T>()` initialized bytes. -/
  encode_length : ∀ value, (encode value).length = layout.size

/-- A `T: AnyBitPattern` or `T: Zeroable` instantiation: its layout and the
value stored by `size_of::<T>()` bytes. The models apply `decode` only to
patterns the trait bound declares valid: every pattern of exactly that length
for `AnyBitPattern`, and the all-zero pattern for `Zeroable`. -/
structure Decoding where
  /-- Mathematical values of the selected Rust type. -/
  Value : Type
  /-- The size and alignment of the selected type. -/
  layout : Layout
  /-- The value stored by a valid pattern; padding bytes are ignored. -/
  decode : Solanalib.Runtime.Bytes → Value

/-- Source `is_aligned_to(ptr, align)`. Its `align_offset` feature branch and
its `ptr as usize % align` branch agree at run time for power-of-two `align`. -/
def isAlignedTo (address align : Nat) : Bool := address % align == 0

@[simp] theorem isAlignedTo_eq_true (address align : Nat) :
    isAlignedTo address align = true ↔ address % align = 0 := by
  simp [isAlignedTo]

@[simp] theorem isAlignedTo_eq_false (address align : Nat) :
    isAlignedTo address align = false ↔ address % align ≠ 0 := by
  simp [isAlignedTo]

/-- Source `internal::try_cast_slice::<A, B>` on a slice at `address` with
`count` elements of layout `a`. It returns the address and element count of the
resulting `&[B]`. The branch order, including the zero-sized branch for `B`,
follows the source exactly. -/
def tryCastSlice (a b : Layout) (address count : Nat) : Except PodCastError (Nat × Nat) :=
  let inputBytes := count * a.size
  if a.align < b.align ∧ isAlignedTo address b.align = false then
    .error .TargetAlignmentGreaterAndInputNotAligned
  else if b.size = a.size then .ok (address, count)
  else if (b.size ≠ 0 ∧ inputBytes % b.size = 0) ∨ (b.size = 0 ∧ inputBytes = 0) then
    .ok (address, if b.size ≠ 0 then inputBytes / b.size else 0)
  else .error .OutputSliceWouldHaveSlop

/-- The cast used by `bytes_of` always succeeds: `u8` has alignment one and
size one, so the alignment branch and the slop branch are dead and the source
`unreachable!()` is never reached. The result keeps the address and has
`size_of::<T>()` elements, which is zero for a zero-sized `T`. -/
theorem tryCastSlice_toBytes (layout : Layout) (address : Nat) :
    tryCastSlice layout Layout.u8 address 1 = .ok (address, layout.size) := by
  have positive := layout.align_pos
  unfold tryCastSlice
  split
  · next greater =>
    have : layout.align < 1 := greater.1
    omega
  · split
    · next same =>
      change 1 = layout.size at same
      rw [← same]
    · simp [Layout.u8, Nat.mod_one]

/-- Source `bytes_of(t)`: cast `slice::from_ref(t)`, one element at the
reference address, to `&[u8]`. The returned slice keeps the address and exposes
exactly the bytes of the value, as `slice::from_raw_parts` does. -/
def bytesOf (encoding : Encoding) (t : TypedRef encoding.Value) : SliceRef :=
  ⟨t.address, encoding.encode t.value⟩

/-- `bytesOf` has exactly the address and length chosen by the source cast. -/
theorem bytesOf_source_geometry (encoding : Encoding) (t : TypedRef encoding.Value) :
    tryCastSlice encoding.layout Layout.u8 t.address 1 =
      .ok ((bytesOf encoding t).address, (bytesOf encoding t).bytes.length) := by
  rw [tryCastSlice_toBytes]
  simp [bytesOf, encoding.encode_length]

/-- A zero-sized type yields an empty slice. The pinned source keeps the
reference address in this case as well. -/
theorem bytesOf_zero_sized (encoding : Encoding) (t : TypedRef encoding.Value)
    (zero : encoding.layout.size = 0) :
    bytesOf encoding t = ⟨t.address, []⟩ := by
  have length := encoding.encode_length t.value
  rw [zero] at length
  simp [bytesOf, List.length_eq_zero_iff.mp length]

/-- Source `internal::try_from_bytes::<T>(s)`: the exact length is checked
first, then the alignment of the slice address. Success returns a reference at
the same address whose value is decoded from the bytes of the slice. -/
def tryFromBytes (decoding : Decoding) (s : SliceRef) :
    Except PodCastError (TypedRef decoding.Value) :=
  if s.bytes.length ≠ decoding.layout.size then .error .SizeMismatch
  else if isAlignedTo s.address decoding.layout.align = false then
    .error .TargetAlignmentGreaterAndInputNotAligned
  else .ok ⟨s.address, decoding.decode s.bytes⟩

/-- Declarative result of `try_from_bytes`, with the source check order:
a size mismatch is reported whatever the address; the alignment error requires
the exact size; success requires both and aliases the input address. -/
def TryFromBytesPost (decoding : Decoding) (s : SliceRef) :
    Except PodCastError (TypedRef decoding.Value) → Prop
  | .error .SizeMismatch => s.bytes.length ≠ decoding.layout.size
  | .error .TargetAlignmentGreaterAndInputNotAligned =>
      s.bytes.length = decoding.layout.size ∧ s.address % decoding.layout.align ≠ 0
  | .error .OutputSliceWouldHaveSlop | .error .AlignmentMismatch => False
  | .ok reference => s.bytes.length = decoding.layout.size ∧
      s.address % decoding.layout.align = 0 ∧ reference = ⟨s.address, decoding.decode s.bytes⟩

/-- The declarative result determines `tryFromBytes` exactly. -/
theorem tryFromBytesPost_iff (decoding : Decoding) (s : SliceRef)
    (result : Except PodCastError (TypedRef decoding.Value)) :
    TryFromBytesPost decoding s result ↔ result = tryFromBytes decoding s := by
  unfold tryFromBytes
  by_cases size : s.bytes.length = decoding.layout.size
  · by_cases aligned : s.address % decoding.layout.align = 0
    · have : isAlignedTo s.address decoding.layout.align = true := by simpa using aligned
      simp only [size, ne_eq, not_true_eq_false, ↓reduceIte, this, Bool.true_eq_false]
      rcases result with error | reference
      · cases error <;> simp [TryFromBytesPost, size, aligned]
      · simp [TryFromBytesPost, size, aligned]
    · have : isAlignedTo s.address decoding.layout.align = false := by simpa using aligned
      simp only [size, ne_eq, not_true_eq_false, ↓reduceIte, this]
      rcases result with error | reference
      · cases error <;> simp [TryFromBytesPost, size, aligned]
      · simp [TryFromBytesPost, aligned]
  · simp only [size, ne_eq, not_false_eq_true, ↓reduceIte]
    rcases result with error | reference
    · cases error <;> simp [TryFromBytesPost, size]
    · simp [TryFromBytesPost, size]

/-- The reference function satisfies the declarative result. -/
theorem tryFromBytes_post (decoding : Decoding) (s : SliceRef) :
    TryFromBytesPost decoding s (tryFromBytes decoding s) :=
  (tryFromBytesPost_iff decoding s _).mpr rfl

/-- A wrong length is rejected before the address is inspected. -/
theorem tryFromBytes_size_first (decoding : Decoding) (s : SliceRef)
    (wrong : s.bytes.length ≠ decoding.layout.size) :
    tryFromBytes decoding s = .error .SizeMismatch := by
  simp [tryFromBytes, wrong]

/-- With the exact length, a misaligned address is rejected, even for an
empty slice of a zero-sized type with alignment above one. -/
theorem tryFromBytes_misaligned (decoding : Decoding) (s : SliceRef)
    (size : s.bytes.length = decoding.layout.size)
    (misaligned : s.address % decoding.layout.align ≠ 0) :
    tryFromBytes decoding s = .error .TargetAlignmentGreaterAndInputNotAligned := by
  have : isAlignedTo s.address decoding.layout.align = false := by simpa using misaligned
  simp [tryFromBytes, size, this]

/-- `try_from_bytes` never reports the two errors it does not produce. -/
theorem tryFromBytes_error_cases (decoding : Decoding) (s : SliceRef) (error : PodCastError)
    (failed : tryFromBytes decoding s = .error error) :
    error = .SizeMismatch ∨ error = .TargetAlignmentGreaterAndInputNotAligned := by
  unfold tryFromBytes at failed
  split at failed
  · cases failed
    exact .inl rfl
  · split at failed
    · cases failed
      exact .inr rfl
    · cases failed

/-- `size_of::<T>()` zero bytes, as written by `core::mem::zeroed`. -/
def zeroBytes (layout : Layout) : Solanalib.Runtime.Bytes := List.replicate layout.size 0

@[simp] theorem length_zeroBytes (layout : Layout) :
    (zeroBytes layout).length = layout.size := by
  simp [zeroBytes]

/-- Default `Zeroable::zeroed()` calls `core::mem::zeroed()`: the value whose
`size_of::<T>()` bytes are all zero. -/
def zeroed (decoding : Decoding) : decoding.Value := decoding.decode (zeroBytes decoding.layout)

namespace Sample

/-- `u64` with size eight, alignment eight and little-endian bytes, as on the
SBF and x86-64 targets. A sample instantiation, not a target assumption. -/
abbrev u64Layout : Layout := ⟨8, 8, ⟨3, rfl⟩, rfl⟩

/-- Bytes of a `u64` in little-endian order. -/
abbrev u64Encoding : Encoding where
  Value := UInt64
  layout := u64Layout
  encode := fun value => Solanalib.Runtime.u64le value.toNat
  encode_length := fun _ => by simp [Solanalib.Runtime.u64le]

/-- The `u64` stored by eight little-endian bytes. -/
abbrev u64Decoding : Decoding where
  Value := UInt64
  layout := u64Layout
  decode := fun bytes => UInt64.ofNat (Solanalib.Runtime.leNat bytes)

/-- The zero-sized `()`: size zero, alignment one. -/
abbrev unitEncoding : Encoding where
  Value := Unit
  layout := ⟨0, 1, ⟨0, rfl⟩, rfl⟩
  encode := fun _ => []
  encode_length := fun _ => rfl

/-- A zero-sized type with alignment eight, such as `[u64; 0]`. -/
abbrev emptyU64ArrayDecoding : Decoding where
  Value := Unit
  layout := ⟨0, 8, ⟨3, rfl⟩, rfl⟩
  decode := fun _ => ()

end Sample

end Solanalib.Specs.Core.Bytemuck
