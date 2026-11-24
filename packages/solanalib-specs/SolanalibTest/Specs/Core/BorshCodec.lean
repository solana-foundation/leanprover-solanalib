/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorshFamily

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Nonvacuity controls for the shared borsh wire format and generic members. -/

namespace SolanalibTest.Specs.Core.BorshCodec

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) :=
  exceptDecEq

/-- A closed test profile with a kind distinct from both versions. -/
def testProfile : Profile := ⟨⟨"TestKind"⟩, "zero-sized"⟩

/-! ## Byte order, short reads and remaining slices -/

theorem u32_is_little_endian :
    decodeU32 testProfile [1, 2, 3, 4, 5] = (.ok 0x04030201, [5]) ∧
    decodeU32 testProfile [1, 2, 3, 4, 5] ≠ (.ok 0x01020304, [5]) := by decide

theorem signed_values_are_twos_complement :
    decodeI64 testProfile [254, 255, 255, 255, 255, 255, 255, 255] = (.ok (-2), []) ∧
    decodeI32 testProfile [255, 255, 255, 127] = (.ok 2147483647, []) ∧
    decodeI8 testProfile [128] = (.ok (-128), []) := by decide

/-- The reference follows the `std` slice reader: a short read empties the slice. -/
theorem short_read_empties_slice :
    decodeU64 testProfile [1, 2, 3] = (.error testProfile.unexpectedLength, []) := by decide

/-- After an error the contract leaves the remaining slice open: the `nostd_io`
remainder (the input itself) is admitted as well. -/
theorem error_remainder_is_unconstrained :
    DecodeMatches (decodeU64 testProfile [1, 2, 3]) (.error testProfile.unexpectedLength, [1, 2,
      3]) ∧
    DecodeMatches (decodeU64 testProfile [1, 2, 3]) (.error testProfile.unexpectedLength, []) :=
  ⟨rfl, rfl⟩

/-- On success the remaining slice is exact. -/
theorem success_remainder_is_exact :
    ¬ DecodeMatches (decodeU8 testProfile [1, 2]) (.ok 1, []) := by
  intro h
  cases h

/-- The message strings are computed with `format!` semantics; module-level
kernel checks compare the structured error, and the differential tests compare
the rendered strings. -/
theorem bool_rejects_other_bytes :
    decodeBool testProfile [1] = (.ok true, []) ∧
    decodeBool testProfile [2, 9] = (.error (testProfile.invalidBool 2), [9]) ∧
    (testProfile.invalidBool 2).kind = ⟨"TestKind"⟩ ∧
    (testProfile.invalidBool 2).message = invalidBoolMessage 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem option_tag_rejection :
    decodeOption testProfile (decodeU32 testProfile) [3, 1, 0, 0, 0] =
      (.error (testProfile.invalidOption 3), [1, 0, 0, 0]) ∧
    decodeOption testProfile (decodeU32 testProfile) [0, 1] = (.ok none, [1]) ∧
    decodeOption testProfile (decodeU32 testProfile) [1, 1, 0, 0, 0] = (.ok (some 1), []) :=
  ⟨rfl, rfl, rfl⟩

/-! ## Floats -/

theorem nan_rejected_after_eight_bytes :
    decodeF64 testProfile [0, 0, 0, 0, 0, 0, 0xf8, 0x7f, 3] =
      (.error testProfile.deserializeNaN, [3]) := by decide

theorem infinity_is_not_nan :
    decodeF64 testProfile [0, 0, 0, 0, 0, 0, 0xf0, 0x7f] = (.ok Float64.positiveInfinity, []) := by
  decide

theorem nan_serialization_writes_nothing :
    encodeF64 Float64.quietNaN = .error serializeNaN ∧
    encodeF64 (0x3ff0000000000000 : UInt64) = .ok [[0, 0, 0, 0, 0, 0, 0xf0, 0x3f]] := by decide

/-! ## Arrays and vectors -/

theorem byte_array_is_one_read :
    decodeByteArray testProfile 2 [4, 5, 6] = (.ok ⟨[4, 5], rfl⟩, [6]) ∧
    decodeByteArray testProfile 4 [4, 5, 6] = (.error testProfile.unexpectedLength, []) := by decide

theorem generic_array_reads_elements_in_order :
    decodeArray 2 (decodeU32 testProfile) [1, 0, 0, 0, 2, 0, 0, 0] = (.ok ⟨[1, 2], rfl⟩, []) := by
  decide

/-- A short `Vec<u8>` body consumes the remaining bytes before the error. -/
theorem byte_vec_short_body :
    decodeByteVec testProfile [3, 0, 0, 0, 7, 8] = (.error testProfile.unexpectedLength, []) ∧
    decodeByteVec testProfile [2, 0, 0, 0, 7, 8, 9] = (.ok [7, 8], [9]) := by decide

theorem zero_sized_vector_rejected_before_reading :
    decodeVec testProfile 0 (Or.inl rfl) (decodeU8 testProfile) [1, 0, 0, 0] =
      (.error testProfile.zeroSized, [1, 0, 0, 0]) := by decide

theorem cautious_bounds_the_first_allocation :
    cautious 16 1000 = some 256 ∧ cautious 24 1000 = some 170 ∧
    cautious 8192 5 = some 1 ∧ cautious 1 0 = some 1 := by
  decide

/-- The `u8::vec_from_reader` buffer starts at most at 1 MiB and doubles. -/
theorem byte_vec_buffer_schedule :
    byteVecCalls (3 * 1024 * 1024) (3 * 1024 * 1024) =
      [.zeroed 1048576, .resize 2097152, .resize 3145728] ∧
    byteVecCalls (3 * 1024 * 1024) 1048576 = [.zeroed 1048576, .resize 2097152] ∧
    byteVecCalls (3 * 1024 * 1024) 100 = [.zeroed 1048576] := by decide

/-- A log of `Vec` calls as provider state. -/
def loggingAllocator : AllocateFn (List VecCall) Empty Empty :=
  fun log call => .returned () (log ++ [call])

/-- The generic path allocates with the cautious capacity and pushes after each
element; the slice after the last element is returned. -/
theorem generic_vec_calls :
    vecDecodeFn testProfile 4 (by right; decide) (Decoder.lift (decodeU32 testProfile))
      loggingAllocator []
        [2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 9] =
      .returned (.ok [1, 2], [9]) [.withCapacity 2, .push 0, .push 1] := rfl

/-- An element error stops the loop: no later push. -/
theorem generic_vec_stops_at_element_error :
    vecDecodeFn testProfile 4 (by right; decide) (Decoder.lift (decodeU32 testProfile))
      loggingAllocator []
        [2, 0, 0, 0, 1, 0, 0, 0, 2] =
      .returned (.error testProfile.unexpectedLength, []) [.withCapacity 2, .push 0] := rfl

/-- An allocation failure of the provider is a terminal exit of the decoder. -/
def failingPush : AllocateFn Unit Empty String := fun state call =>
  match call with
  | .push _ => .terminated "allocation failure"
  | _ => .returned () state

theorem allocation_failure_terminates :
    vecDecodeFn testProfile 4 (by right; decide) (Decoder.lift (decodeU32 testProfile)) failingPush
      ()
        [1, 0, 0, 0, 1, 0, 0, 0] = .terminated "allocation failure" := rfl

theorem byte_vec_calls_provider :
    byteVecDecodeFn testProfile loggingAllocator [] [2, 0, 0, 0, 7, 8] =
      .returned (.ok [7, 8], []) [.zeroed 2] := rfl

/-- The family relation at function-graph callbacks is the executable function. -/
theorem vec_family_matches_function :
    vecDecodeRun testProfile
      ⟨List VecCall, Empty, Empty, .other UInt32 4
        (Callback.ofFunction (Decoder.lift (decodeU32 testProfile))),
        Callback.ofFunction loggingAllocator, noDivisionPanic⟩
      [] [1, 0, 0, 0, 5, 0, 0, 0]
      (.returned (.ok ([5] : List UInt32), []) [.withCapacity 1, .push 0]) :=
  (vecDecodeRun_ofFunction testProfile 4 (by right; decide) _ loggingAllocator [] _ _).2 rfl

/-! ## try_from_slice -/

theorem leftover_bytes_rejected :
    tryFromSlice (decodeU8 testProfile) [1] = .ok 1 ∧
    tryFromSlice (decodeU8 testProfile) [1, 2] = .error notAllBytesRead ∧
    tryFromSlice (decodeU8 testProfile) [] = .error testProfile.unexpectedLength := by decide

theorem not_all_bytes_read_is_invalid_data :
    notAllBytesRead = ⟨⟨"InvalidData"⟩, "Not all bytes read"⟩ := rfl

/-! ## Serialization chunking -/

/-- `Some(2u64)` issues two `write_all` calls: the tag and the 8 bytes. -/
theorem option_writes_two_chunks :
    optionSerializeFn recordingWriter (Encoder.serializeFn encodeU64 recordingWriter) []
        (some (2 : UInt64)) =
      (.returned (.ok ()) [[1], [2, 0, 0, 0, 0, 0, 0, 0]] :
        Outcome (List Solanalib.Runtime.Bytes) (Except IoError Unit) Empty Empty) := rfl

/-- `Some(NaN)` writes the tag before the float error. -/
theorem option_nan_after_tag :
    encodeOptionPlan (Encoder.plan encodeF64) (some Float64.quietNaN) =
      ⟨[[1]], some serializeNaN⟩ := by decide

/-- A writer that fails on its second chunk. -/
def failSecond : WriterFn (List Solanalib.Runtime.Bytes) Empty Empty := fun log chunk =>
  if log.length = 0 then .returned (.ok ()) (log ++ [chunk])
  else .returned (.error ⟨⟨"WriteZero"⟩, "failed to write whole buffer"⟩) log

/-- The element serializer runs after the tag; its writer error is returned. -/
theorem option_returns_element_writer_error :
    optionSerializeFn failSecond (Encoder.serializeFn encodeU64 failSecond) []
        (some (2 : UInt64)) =
      .returned (.error ⟨⟨"WriteZero"⟩, "failed to write whole buffer"⟩) [[1]] := rfl

/-- `u8` arrays use one `write_all`; a generic element type writes per element. -/
theorem byte_array_one_chunk_generic_many :
    byteArraySerializeFn 3 recordingWriter [] ⟨[1, 2, 3], rfl⟩ =
      (.returned (.ok ()) [[1, 2, 3]] :
        Outcome (List Solanalib.Runtime.Bytes) (Except IoError Unit) Empty Empty) ∧
    arraySerializeFn 3 recordingWriter (Encoder.serializeFn encodeU8 recordingWriter) []
        ⟨[1, 2, 3], rfl⟩ =
      (.returned (.ok ()) [[1], [2], [3]] :
        Outcome (List Solanalib.Runtime.Bytes) (Except IoError Unit) Empty Empty) :=
  ⟨rfl, rfl⟩

/-- `N = 0` issues no `write_all`, not even an empty one. -/
theorem empty_array_writes_nothing :
    byteArraySerializeFn 0 recordingWriter [] ⟨[], rfl⟩ =
      (.returned (.ok ()) [] : Outcome (List Solanalib.Runtime.Bytes) (Except IoError Unit) Empty
        Empty) :=
  rfl

/-- A writer unwind is forwarded with its state; no later chunk is written. -/
def unwindFirst : WriterFn (List Solanalib.Runtime.Bytes) String Empty := fun log chunk =>
  .unwound "panic in write_all" (log ++ [chunk.take 1])

theorem writer_unwind_is_forwarded :
    optionSerializeFn unwindFirst (Encoder.serializeFn encodeU64 unwindFirst) [] (some (2 :
      UInt64)) =
      .unwound "panic in write_all" [[1]] := rfl

end SolanalibTest.Specs.Core.BorshCodec
