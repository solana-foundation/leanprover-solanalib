/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Bytemuck

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.Bytemuck

open Solanalib.Specs.Core.Bytemuck

/-- `u16`: size two, alignment two. -/
def u16Layout : Layout := ⟨2, 2, ⟨1, rfl⟩, rfl⟩

/-- A zero-sized type with alignment one. -/
def unitLayout : Layout := ⟨0, 1, ⟨0, rfl⟩, rfl⟩

/-- The general cast rejects a misaligned address when the target alignment is greater. -/
theorem cast_rejects_greater_alignment :
    tryCastSlice Layout.u8 u16Layout 3 4 = .error .TargetAlignmentGreaterAndInputNotAligned := rfl

/-- Three bytes are not a whole number of `u16` elements. -/
theorem cast_rejects_slop :
    tryCastSlice Layout.u8 u16Layout 4 3 = .error .OutputSliceWouldHaveSlop := rfl

/-- Four aligned bytes give two `u16` elements at the same address. -/
theorem cast_divides_length :
    tryCastSlice Layout.u8 u16Layout 4 4 = .ok (4, 2) := rfl

/-- The zero-sized target branch accepts only an empty input. -/
theorem cast_zero_sized_target :
    tryCastSlice Layout.u8 unitLayout 5 0 = .ok (5, 0) ∧
    tryCastSlice Layout.u8 unitLayout 5 1 = .error .OutputSliceWouldHaveSlop := ⟨rfl, rfl⟩

/-- `bytes_of` on a zero-sized source takes the divisible branch with no elements. -/
theorem bytes_of_cast_zero_sized_source :
    tryCastSlice unitLayout Layout.u8 7 1 = .ok (7, 0) := tryCastSlice_toBytes unitLayout 7

/-- The declarative `try_from_bytes` result has exactly one solution. -/
theorem try_from_bytes_post_unique (s : SliceRef)
    (left right : Except PodCastError (TypedRef UInt64))
    (leftPost : TryFromBytesPost Sample.u64Decoding s left)
    (rightPost : TryFromBytesPost Sample.u64Decoding s right) : left = right :=
  ((tryFromBytesPost_iff Sample.u64Decoding s left).mp leftPost).trans
    ((tryFromBytesPost_iff Sample.u64Decoding s right).mp rightPost).symm

/-- The zero pattern of the sample decodes to zero. -/
theorem zeroed_u64_is_zero : zeroed Sample.u64Decoding = (0 : UInt64) := by decide

end SolanalibTest.Specs.Core.Bytemuck
