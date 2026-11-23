/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Bytemuck.Bytes

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Bytemuck.Bytes

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Bytemuck

/-- Eight nonuniform bytes make byte order observable. -/
def ascendingBytes : Solanalib.Runtime.Bytes := [1, 2, 3, 4, 5, 6, 7, 8]

/-- An aligned slice of the exact size is accepted at the same address. -/
theorem aligned_exact_size_accepted_same_address :
    (Solanalib.Specs.Bytemuck.try_from_bytes_model Sample.u64Decoding () ⟨16, ascendingBytes⟩).1 =
      .ok ⟨16, (0x0807060504030201 : UInt64)⟩ := rfl

/-- An exact-size slice at a misaligned address is rejected. -/
theorem misaligned_input_rejected :
    (Solanalib.Specs.Bytemuck.try_from_bytes_model Sample.u64Decoding () ⟨12, ascendingBytes⟩).1 =
      .error .TargetAlignmentGreaterAndInputNotAligned := rfl

/-- A short slice at a misaligned address reports the size, which is checked first. -/
theorem size_mismatch_rejected_before_alignment :
    (Solanalib.Specs.Bytemuck.try_from_bytes_model Sample.u64Decoding () ⟨12, ascendingBytes.take
      7⟩).1 =
      .error .SizeMismatch := rfl

/-- An aligned slice that is one byte too long is rejected. -/
theorem long_aligned_input_rejected :
    (Solanalib.Specs.Bytemuck.try_from_bytes_model Sample.u64Decoding () ⟨16, ascendingBytes ++
      [9]⟩).1 =
      .error .SizeMismatch := rfl

/-- The alignment rule applies to an empty slice of a zero-sized type. -/
theorem empty_slice_alignment_checked :
    (Solanalib.Specs.Bytemuck.try_from_bytes_model Sample.emptyU64ArrayDecoding () ⟨1, []⟩).1 =
      .error .TargetAlignmentGreaterAndInputNotAligned ∧
    (Solanalib.Specs.Bytemuck.try_from_bytes_model Sample.emptyU64ArrayDecoding () ⟨8, []⟩).1 =
      .ok ⟨8, ()⟩ := ⟨rfl, rfl⟩

theorem try_from_bytes_versioned_contract_holds :
    (Solanalib.Specs.Bytemuck.try_from_bytes_contract.contract Sample.u64Decoding).ensures
      () ⟨12, ascendingBytes⟩
      (Solanalib.Specs.Bytemuck.try_from_bytes_model Sample.u64Decoding () ⟨12, ascendingBytes⟩).1
        () :=
  Solanalib.Specs.Bytemuck.try_from_bytes_reference Sample.u64Decoding () ⟨12, ascendingBytes⟩ _
    trivial rfl

/-- The contract rejects success on a misaligned address. -/
theorem contract_rejects_success_when_misaligned (value : UInt64) :
    ¬ (Solanalib.Specs.Bytemuck.try_from_bytes_contract.contract Sample.u64Decoding).ensures
      () ⟨12, ascendingBytes⟩ (.ok ⟨12, value⟩) () := by
  intro ⟨⟨_, aligned, _⟩, _⟩
  exact absurd aligned (by decide)

/-- The contract rejects the alignment error when the size is wrong. -/
theorem contract_rejects_alignment_error_on_size_mismatch :
    ¬ (Solanalib.Specs.Bytemuck.try_from_bytes_contract.contract Sample.u64Decoding).ensures
      () ⟨12, ascendingBytes.take 7⟩ (.error .TargetAlignmentGreaterAndInputNotAligned) () := by
  intro ⟨⟨size, _⟩, _⟩
  exact absurd size (by decide)

/-- The contract rejects a decoded value other than the slice bytes. -/
theorem contract_rejects_wrong_value :
    ¬ (Solanalib.Specs.Bytemuck.try_from_bytes_contract.contract Sample.u64Decoding).ensures
      () ⟨16, ascendingBytes⟩ (.ok ⟨16, (0x0102030405060708 : UInt64)⟩) () := by
  intro ⟨⟨_, _, same⟩, _⟩
  have := congrArg TypedRef.value same
  exact absurd this (by decide)

/-- `Zeroable::zeroed` returns the value whose bytes are all zero. -/
theorem zeroed_value_has_all_zero_bytes :
    Sample.u64Encoding.encode
        (Solanalib.Specs.Bytemuck.zeroable.Zeroable.zeroed_model Sample.u64Decoding () ()).1 =
      List.replicate 8 0 := by
  decide

theorem zeroed_contract_rejects_nonzero :
    ¬ (Solanalib.Specs.Bytemuck.zeroable.Zeroable.zeroed_contract.contract
      Sample.u64Decoding).ensures
      () () (1 : UInt64) () := by
  intro ⟨value, _⟩
  exact absurd value (by decide)

end SolanalibTest.Specs.Bytemuck.Bytes

namespace SolanalibTest.Specs.Bytemuck.Bytes

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Bytemuck

/-- A nonuniform `u64` makes byte order observable. -/
def ascendingRef : TypedRef UInt64 := ⟨16, 0x0807060504030201⟩

theorem bytes_of_little_endian_same_address :
    Solanalib.Specs.Bytemuck.bytes_of_model Sample.u64Encoding () ascendingRef =
      (⟨16, [1, 2, 3, 4, 5, 6, 7, 8]⟩, ()) := by
  decide

theorem bytes_of_is_not_big_endian :
    (Solanalib.Specs.Bytemuck.bytes_of_model Sample.u64Encoding () ascendingRef).1.bytes ≠
      [8, 7, 6, 5, 4, 3, 2, 1] := by
  decide

/-- The zero-sized `()` yields an empty slice at the reference address. -/
theorem bytes_of_zero_sized_empty_same_address :
    (Solanalib.Specs.Bytemuck.bytes_of_model Sample.unitEncoding () ⟨3, ()⟩).1 = ⟨3, []⟩ :=
  bytesOf_zero_sized Sample.unitEncoding ⟨3, ()⟩ rfl

/-- The source cast path chooses the same address and eight elements. -/
theorem bytes_of_source_cast_geometry :
    tryCastSlice Sample.u64Layout Layout.u8 16 1 = .ok (16, 8) :=
  tryCastSlice_toBytes Sample.u64Layout 16

theorem bytes_of_versioned_contract_holds :
    (Solanalib.Specs.Bytemuck.bytes_of_contract.contract Sample.u64Encoding).ensures () ascendingRef
      (Solanalib.Specs.Bytemuck.bytes_of_model Sample.u64Encoding () ascendingRef).1 () :=
  Solanalib.Specs.Bytemuck.bytes_of_reference Sample.u64Encoding () ascendingRef _ trivial rfl

/-- The contract rejects a slice with different bytes. -/
theorem bytes_of_contract_rejects_wrong_bytes :
    ¬ (Solanalib.Specs.Bytemuck.bytes_of_contract.contract Sample.u64Encoding).ensures ()
      ascendingRef
      ⟨16, List.replicate 8 0⟩ () := by
  intro ⟨_, bytes, _⟩
  exact absurd bytes (by decide)

/-- The contract rejects a slice at another address. -/
theorem bytes_of_contract_rejects_moved_address :
    ¬ (Solanalib.Specs.Bytemuck.bytes_of_contract.contract Sample.u64Encoding).ensures ()
      ascendingRef
      ⟨24, [1, 2, 3, 4, 5, 6, 7, 8]⟩ () := by
  intro ⟨address, _, _⟩
  exact absurd address (by decide)

theorem zeroed_versioned_contract_holds :
    (Solanalib.Specs.Bytemuck.zeroable.Zeroable.zeroed_contract.contract Sample.u64Decoding).ensures
      () () (Solanalib.Specs.Bytemuck.zeroable.Zeroable.zeroed_model Sample.u64Decoding () ()).1 ()
        :=
  Solanalib.Specs.Bytemuck.zeroable.Zeroable.zeroed_reference Sample.u64Decoding () () _ trivial rfl

end SolanalibTest.Specs.Bytemuck.Bytes
