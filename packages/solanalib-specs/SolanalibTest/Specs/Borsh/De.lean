/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Borsh.De

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Borsh.De

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh
open Solanalib.Specs.Borsh

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) :=
  exceptDecEq

/-- borsh 0.10.4 reports short input, bad tags and zero-sized vectors as
`InvalidInput`; leftover bytes stay `InvalidData`. -/
theorem kinds_are_invalid_input :
    (u64.invalid_input.deserialize_reader_model () [1]).1 =
      (.error ⟨⟨"InvalidInput"⟩, "Unexpected length of input"⟩, []) ∧
    (invalid_input_profile.invalidBool 2).kind = ⟨"InvalidInput"⟩ ∧
    (invalid_input_profile.invalidOption 2).kind = ⟨"InvalidInput"⟩ ∧
    invalid_input_profile.zeroSized = ⟨⟨"InvalidInput"⟩,
      "Vectors of zero-sized types are not allowed due to deny-of-service concerns on \
        deserialization."⟩ ∧
    notAllBytesRead.kind = ⟨"InvalidData"⟩ := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem i8_price_exponent :
    (i8.invalid_input.deserialize_reader_model () [0xfe]).1 = (.ok (-2), []) := by decide

theorem bool_and_option_tags :
    (bool.invalid_input.deserialize_reader_model () [3]).1 = (.error
      (invalid_input_profile.invalidBool 3), []) ∧
    decodeOption invalid_input_profile (decodeU32 invalid_input_profile) [2] = (.error
      (invalid_input_profile.invalidOption 2), []) :=
  ⟨rfl, rfl⟩

/-- A derived struct `{ u64, u64, bool, bool }`, written with `?` sequencing
over the primitive models. -/
def fourFieldStruct : Decoder (UInt64 × UInt64 × Bool × Bool) :=
  (decodeU64 invalid_input_profile).bind fun inAtoms =>
  (decodeU64 invalid_input_profile).bind fun outAtoms =>
  (decodeBool invalid_input_profile).bind fun isBaseIn =>
  (decodeBool invalid_input_profile).bind fun isExactIn =>
  Decoder.pure (inAtoms, outAtoms, isBaseIn, isExactIn)

def fourFieldBytes : Solanalib.Runtime.Bytes := [5, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1,
  0]

/-- `try_from_slice` at the function graph of the derived decoder: exact input
succeeds, a trailing byte gives `Not all bytes read`, a short input the error of the
decoder. -/
theorem try_from_slice_controls :
    de.BorshDeserialize.try_from_slice_run
      ⟨Unit, Empty, Empty, _, Callback.ofFunction (Decoder.lift fourFieldStruct)⟩ () fourFieldBytes
      (.returned (.ok (5, 6, true, false)) ()) ∧
    de.BorshDeserialize.try_from_slice_run
      ⟨Unit, Empty, Empty, _, Callback.ofFunction (Decoder.lift fourFieldStruct)⟩ ()
      (fourFieldBytes ++ [0]) (.returned (.error notAllBytesRead) ()) ∧
    de.BorshDeserialize.try_from_slice_run
      ⟨Unit, Empty, Empty, _, Callback.ofFunction (Decoder.lift fourFieldStruct)⟩ ()
      (fourFieldBytes.take 17) (.returned (.error invalid_input_profile.unexpectedLength) ()) :=
  ⟨(tryFromSliceRun_ofFunction _ () _ _).2 rfl,
    (tryFromSliceRun_ofFunction _ () _ _).2 rfl,
    (tryFromSliceRun_ofFunction _ () _ _).2 rfl⟩

/-- An invalid bool inside the struct is reported, not the leftover check. -/
theorem try_from_slice_reports_inner_error :
    tryFromSlice fourFieldStruct (fourFieldBytes.set 16 2 ++ [0]) = .error
      (invalid_input_profile.invalidBool 2) := rfl

/-- `Vec<T>` with 16-byte elements: the first allocation
is capped at `4096 / 16 = 256` elements for a declared length of 1000, and the
first element error stops before any push. -/
def calls : AllocateFn (List VecCall) Empty Empty := fun log call => .returned () (log ++ [call])

def sixteenBytes : Decoder (FixedArray UInt8 16) := decodeByteArray invalid_input_profile 16

theorem vec_cautious_capacity :
    vecDecodeFn invalid_input_profile 16 (by right; decide) (Decoder.lift sixteenBytes) calls []
      [0xe8, 0x03, 0, 0, 1, 2] =
      .returned (.error invalid_input_profile.unexpectedLength, []) [.withCapacity 256] := rfl

theorem vec_family_at_function_graph :
    Vec.invalid_input.deserialize_reader_run
      ⟨List VecCall, Empty, Empty, .other (FixedArray UInt8 16) 16
        (Callback.ofFunction (Decoder.lift sixteenBytes)), Callback.ofFunction calls,
          noDivisionPanic⟩
      [] [0xe8, 0x03, 0, 0, 1, 2]
      (.returned (.error invalid_input_profile.unexpectedLength, []) [.withCapacity 256]) :=
  (vecDecodeRun_ofFunction invalid_input_profile 16 (by right; decide) _ calls [] _ _).2 rfl

theorem empty_vec_allocates_nothing :
    vecDecodeFn invalid_input_profile 16 (by right; decide) (Decoder.lift sixteenBytes) calls []
      [0, 0, 0, 0, 9] =
      .returned (.ok [], [9]) [] := rfl

theorem vec_from_reader_default_reads_nothing :
    de.BorshDeserialize.vec_from_reader_run ⟨UInt32⟩ () ((3 : UInt32), [1, 2])
      (.returned (.ok none, [1, 2]) ()) := rfl

theorem cautious_values :
    de.hint.cautious_run ⟨Unit, Empty, Empty, 16, noDivisionPanic⟩ ()
      (1000 : UInt32) (.returned (256 : Nat) ()) ∧
    de.hint.cautious_run ⟨Unit, Empty, Empty, 24, noDivisionPanic⟩ ()
      (1000 : UInt32) (.returned (170 : Nat) ()) := ⟨rfl, rfl⟩

/-! ## The `size_of::<T>() as u32` boundary -/

/-- The cast, rather than the original size, is the divisor. A zero hint
does not bypass the division of Rust. -/
theorem cautious_truncates_size :
    cautious (2^32 - 1) 5000 = some 1 ∧
    cautious (2^32) 1 = none ∧
    cautious (2 * 2^32) 0 = none ∧
    cautious (2^32 + 1) 1000 = some 1000 ∧
    cautious (2^32 + 1) 5000 = some 4096 ∧
    cautious (2^32 + 2) 5000 = some 2048 := by decide

def cautiousUnwind (before : Nat) (_ : Unit) : Outcome Nat Empty String String :=
  .unwound "division by zero" (before + 1)

def cautiousTerminate (_ : Nat) (_ : Unit) : Outcome Nat Empty String String :=
  .terminated "division by zero"

/-- The registered family permits the effects and exit of the source panic policy,
including the zero-sized helper itself; it has no size precondition. -/
theorem cautious_family_panics :
    de.hint.cautious_run ⟨Nat, String, String, 2^32, Callback.ofFunction cautiousUnwind⟩
      (7 : Nat) (0 : UInt32) (.unwound "division by zero" (8 : Nat)) ∧
    de.hint.cautious_run ⟨Nat, String, String, 2 * 2^32, Callback.ofFunction cautiousTerminate⟩
      (7 : Nat) (1 : UInt32) (.terminated "division by zero") ∧
    de.hint.cautious_run ⟨Nat, String, String, 0, Callback.ofFunction cautiousUnwind⟩
      (7 : Nat) (1 : UInt32) (.unwound "division by zero" (8 : Nat)) :=
  ⟨(cautiousRun_ofFunction _ cautiousUnwind _ _ _).2 rfl,
    (cautiousRun_ofFunction _ cautiousTerminate _ _ _).2 rfl,
    (cautiousRun_ofFunction _ cautiousUnwind _ _ _).2 rfl⟩

/-- The formerly predicted capacity 1 is rejected at the original admitted
positive size `2^32`. -/
theorem cautious_rejects_untruncated_result :
    ¬ de.hint.cautious_run ⟨Nat, String, String, 2^32, Callback.ofFunction cautiousUnwind⟩
      (7 : Nat) (1 : UInt32) (.returned (1 : Nat) (7 : Nat)) := by
  intro returned
  have impossible := (cautiousRun_ofFunction (2^32) cautiousUnwind 7 1 (.returned 1 7)).1 returned
  cases impossible

inductive VecEvent where
  | allocate (call : VecCall)
  | element (input : Solanalib.Runtime.Bytes)
  | panic (remaining : Solanalib.Runtime.Bytes)
  deriving DecidableEq, Repr

def tracedAllocate : AllocateFn (List VecEvent) String (List VecEvent) :=
  fun log call => .returned () (log ++ [.allocate call])

def tracedDecode : DecodeFn (List VecEvent) UInt8 String (List VecEvent) :=
  fun log input => .returned (decodeU8 invalid_input_profile input) (log ++ [.element input])

def vecUnwind (log : List VecEvent) (remaining : Solanalib.Runtime.Bytes) :
    Outcome (List VecEvent) Empty String (List VecEvent) :=
  .unwound "division by zero" (log ++ [.panic remaining])

def vecTerminate (log : List VecEvent) (remaining : Solanalib.Runtime.Bytes) :
    Outcome (List VecEvent) Empty String (List VecEvent) :=
  .terminated (log ++ [.panic remaining])

/-- The length is consumed before panic, but no allocation or element
callback has run. The family forwards both panic strategies. -/
theorem vec_truncation_panics_before_callbacks :
    Vec.invalid_input.deserialize_reader_run
      ⟨List VecEvent, String, List VecEvent,
        .other UInt8 (2^32) (Callback.ofFunction tracedDecode),
        Callback.ofFunction tracedAllocate, Callback.ofFunction vecUnwind⟩
      [] [1, 0, 0, 0, 9] (.unwound "division by zero" [.panic [9]]) ∧
    Vec.invalid_input.deserialize_reader_run
      ⟨List VecEvent, String, List VecEvent,
        .other UInt8 (2 * 2^32) (Callback.ofFunction tracedDecode),
        Callback.ofFunction tracedAllocate, Callback.ofFunction vecTerminate⟩
      [] [1, 0, 0, 0, 9] (.terminated [.panic [9]]) :=
  ⟨(vecDecodeRun_withPanic_ofFunction invalid_input_profile _ tracedDecode tracedAllocate vecUnwind
    _ _ _).2 rfl,
    (vecDecodeRun_withPanic_ofFunction invalid_input_profile _ tracedDecode tracedAllocate
      vecTerminate _ _ _).2 rfl⟩

/-- All earlier exits retain their source order: zero size rejects before
reading, a short header errors, and zero length returns without the hint. -/
theorem vec_truncation_preserves_earlier_exits :
    vecDecodeWithPanicFn invalid_input_profile 0 tracedDecode tracedAllocate vecUnwind [] [1, 0, 0,
      0, 9] =
      .returned (.error invalid_input_profile.zeroSized, [1, 0, 0, 0, 9]) [] ∧
    vecDecodeWithPanicFn invalid_input_profile (2^32) tracedDecode tracedAllocate vecUnwind [] [1,
      0, 0] =
      .returned (.error invalid_input_profile.unexpectedLength, []) [] ∧
    vecDecodeWithPanicFn invalid_input_profile (2^32) tracedDecode tracedAllocate vecUnwind [] [0,
      0, 0, 0, 9] =
      .returned (.ok [], [9]) [] := ⟨rfl, rfl, rfl⟩

/-- Truncating `2^32 + 1` to 1 restores the requested capacity 2, with the
ordinary allocation/decode/push sequence and exact successful remainder. -/
theorem vec_truncated_nonzero_capacity :
    vecDecodeWithPanicFn invalid_input_profile (2^32 + 1) tracedDecode tracedAllocate vecUnwind []
      [2, 0, 0, 0, 7, 8, 9] =
      .returned (.ok [7, 8], [9])
        [.allocate (.withCapacity 2), .element [7, 8, 9], .allocate (.push 0),
          .element [8, 9], .allocate (.push 1)] := rfl

/-- The byte specialization does not call the cautious hint or its panic
policy; it keeps its zeroed-buffer request. -/
theorem byte_vec_keeps_specialization :
    Vec.invalid_input.deserialize_reader_run
      ⟨List VecEvent, String, List VecEvent, .byte,
        Callback.ofFunction tracedAllocate, Callback.ofFunction vecUnwind⟩
      [] [1, 0, 0, 0, 9] (.returned (.ok ([9] : List UInt8), []) [.allocate (.zeroed 1)]) := by
  exact (decode_runs_ofFunction_iff _ tracedAllocate _ _ _).2 rfl

theorem u8_and_u32_little_endian :
    (u8.invalid_input.deserialize_reader_model () [7, 8]).1 = (.ok 7, [8]) ∧
    (u32.invalid_input.deserialize_reader_model () [0, 1, 0, 0]).1 = (.ok 256, []) ∧
    (u32.invalid_input.deserialize_reader_model () [0, 1]).1 = (.error
      invalid_input_profile.unexpectedLength, []) := by
  decide

/-- `deserialize` forwards the result of the derived decoder and remaining slice. -/
theorem deserialize_family_forwards :
    de.BorshDeserialize.deserialize_run
      ⟨Unit, Empty, Empty, _, Callback.ofFunction (Decoder.lift fourFieldStruct)⟩ ()
      (fourFieldBytes ++ [3]) (.returned (.ok (5, 6, true, false), [3]) ()) :=
  (deserializeRun_ofFunction _ () _ _).2 rfl

end SolanalibTest.Specs.Borsh.De

namespace SolanalibTest.Specs.Borsh.De

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh
open Solanalib.Specs.Borsh

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) :=
  exceptDecEq

/-- borsh 1.6.1 reports short input as `InvalidData`. -/
theorem short_input_is_invalid_data :
    (u64.invalid_data.deserialize_reader_model () [1, 2, 3]).1 =
      (.error ⟨⟨"InvalidData"⟩, "Unexpected length of input"⟩, []) := rfl

/-- Byte order is observable: the first byte is least significant. -/
theorem u32_tag_little_endian :
    (u32.invalid_data.deserialize_reader_model () [2, 0, 0, 0, 7]).1 = (.ok 2, [7]) ∧
    (u32.invalid_data.deserialize_reader_model () [0, 0, 0, 2]).1 = (.ok 0x02000000, []) := by
      decide

theorem i32_negative_exponent :
    (i32.invalid_data.deserialize_reader_model () [0xf8, 0xff, 0xff, 0xff]).1 = (.ok (-8), []) :=
      by decide

theorem i64_and_u64_share_bytes_not_values :
    (i64.invalid_data.deserialize_reader_model () (List.replicate 8 0xff)).1 = (.ok (-1), []) ∧
    (u64.invalid_data.deserialize_reader_model () (List.replicate 8 0xff)).1 = (.ok
      0xffffffffffffffff, []) := by
  decide

/-- `warmup_cooldown_rate = 0.25` decodes; a NaN is rejected with `InvalidData`. -/
theorem f64_rate_and_nan :
    (f64.invalid_data.deserialize_reader_model () [0, 0, 0, 0, 0, 0, 0xd0, 0x3f]).1 =
      (.ok 0x3fd0000000000000, []) ∧
    (f64.invalid_data.deserialize_reader_model () [1, 0, 0, 0, 0, 0, 0xf0, 0x7f]).1 =
      (.error ⟨⟨"InvalidData"⟩,
        "For portability reasons we do not allow to deserialize NaNs."⟩, []) := by
  decide

theorem bool_tag_error_is_invalid_data :
    (bool.invalid_data.deserialize_reader_model () [2]).1 = (.error
      (invalid_data_profile.invalidBool 2), []) ∧
    (invalid_data_profile.invalidBool 2).kind = ⟨"InvalidData"⟩ := ⟨rfl, rfl⟩

/-- The versioned contract holds for the reference output. -/
theorem versioned_contract_holds :
    u64.invalid_data.deserialize_reader_contract.ensures () [1, 0, 0, 0, 0, 0, 0, 0]
      (u64.invalid_data.deserialize_reader_model () [1, 0, 0, 0, 0, 0, 0, 0]).1 () :=
  u64.invalid_data.deserialize_reader_reference () _ trivial

/-- After an error the contract also admits the `nostd_io` remainder. -/
theorem contract_admits_unchanged_slice_after_error :
    u64.invalid_data.deserialize_reader_contract.ensures () [1, 2, 3]
      (.error invalid_data_profile.unexpectedLength, [1, 2, 3]) () := ⟨rfl, rfl⟩

/-- On success the remaining slice is fixed. -/
theorem contract_rejects_wrong_success_remainder :
    ¬ u8.invalid_data.deserialize_reader_contract.ensures () [1, 2] (.ok 1, []) () := by
  rintro ⟨h, _⟩
  cases h

/-- `[u8; 32]` keeps all bytes in order; a short slice is emptied. -/
def ascending : Solanalib.Runtime.Bytes := (List.range 33).map UInt8.ofNat

theorem byte_array_32 :
    decodeByteArray invalid_data_profile 32 ascending =
      (.ok ⟨(List.range 32).map UInt8.ofNat, by simp⟩, [32]) ∧
    decodeByteArray invalid_data_profile 32 [1, 2] = (.error invalid_data_profile.unexpectedLength,
      []) := by decide

theorem array_family_byte_path :
    Array.invalid_data.deserialize_reader_run ⟨Unit, Empty, Empty, 32, .byte⟩ () ascending
      (.returned (decodeByteArray invalid_data_profile 32 ascending) ()) :=
  (arrayDecodeRun_byte invalid_data_profile 32 () ascending _).2 rfl

theorem array_from_reader_some :
    byteArrayFromReader invalid_data_profile 2 [1, 2] = (.ok (some ⟨[1, 2], rfl⟩), []) := by decide

/-- A generic element type reads element by element at a function callback. -/
theorem array_family_generic_path :
    Array.invalid_data.deserialize_reader_run
      ⟨Unit, Empty, Empty, 2,
        .other Int64 8 (Callback.ofFunction (Decoder.lift (decodeI64 invalid_data_profile)))⟩ ()
      ((List.replicate 8 0xff) ++ [1, 0, 0, 0, 0, 0, 0, 0])
      (.returned (.ok (⟨[-1, 1], rfl⟩ : FixedArray Int64 2), []) ()) :=
  (arrayDecodeRun_ofFunction invalid_data_profile 2 8 _ () _ _).2 rfl

/-- An element decoder that unwinds after changing the state. -/
abbrev unwindingIndex : DecodeIndex :=
  ⟨Nat, String, Empty, UInt8,
    fun (state : Nat) _ outcome => outcome = .unwound ("boom" : String) (state + 1)⟩

/-- `deserialize` forwards the exits of the element callback unchanged. -/
theorem deserialize_forwards_unwind :
    de.BorshDeserialize.deserialize_run unwindingIndex (4 : Nat) [1]
      (.unwound ("boom" : String) (5 : Nat)) :=
  (deserializeRun_iff unwindingIndex 4 [1] _).2 rfl

/-- `Option<u32>` at a function-graph element decoder. -/
theorem option_family_at_function_graph :
    Option.invalid_data.deserialize_reader_run
      ⟨Unit, Empty, Empty, UInt32, Callback.ofFunction (Decoder.lift (decodeU32
        invalid_data_profile))⟩ ()
      [1, 9, 0, 0, 0, 4] (.returned (.ok (some (9 : UInt32)), [4]) ()) ∧
    Option.invalid_data.deserialize_reader_run
      ⟨Unit, Empty, Empty, UInt32, Callback.ofFunction (Decoder.lift (decodeU32
        invalid_data_profile))⟩ ()
      [5] (.returned (.error (invalid_data_profile.invalidOption 5), []) ()) :=
  ⟨(optionDecodeRun_ofFunction invalid_data_profile _ () _ _).2 rfl,
    (optionDecodeRun_ofFunction invalid_data_profile _ () _ _).2 rfl⟩

end SolanalibTest.Specs.Borsh.De
