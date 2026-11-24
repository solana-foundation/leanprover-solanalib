/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Borsh.Ser

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Borsh.Ser

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh
open Solanalib.Specs.Borsh

/-- The recording writer as a closed index. -/
abbrev log : WriterIndex := recordingWriterIndex

abbrev Log := List Solanalib.Runtime.Bytes

theorem u32_one_chunk_little_endian :
    u32.serialize_run log ([] : Log) (0x0a0b0c0d : UInt32) (.returned (.ok ()) [[0x0d, 0x0c, 0x0b,
      0x0a]]) :=
  (primitiveSerializeRun_ofFunction encodeU32 recordingWriter _ _ _).2 rfl

theorem i64_twos_complement :
    i64.serialize_run log ([] : Log) (-1 : Int64) (.returned (.ok ()) [List.replicate 8 0xff]) :=
  (primitiveSerializeRun_ofFunction encodeI64 recordingWriter _ _ _).2 rfl

theorem bool_bytes :
    bool.serialize_run log ([] : Log) false (.returned (.ok ()) [[0]]) ∧
    bool.serialize_run log ([] : Log) true (.returned (.ok ()) [[1]]) :=
  ⟨(primitiveSerializeRun_ofFunction encodeBool recordingWriter _ _ _).2 rfl,
    (primitiveSerializeRun_ofFunction encodeBool recordingWriter _ _ _).2 rfl⟩

/-- A finite float is written as its bits; a NaN with any payload is rejected
before the writer is called, with `InvalidData`. -/
theorem f64_finite_and_nan :
    f64.serialize_run log ([] : Log) (0x3fd0000000000000 : UInt64)
      (.returned (.ok ()) [[0, 0, 0, 0, 0, 0, 0xd0, 0x3f]]) ∧
    f64.serialize_run log ([[9]] : Log) (0xfff0000000000001 : UInt64)
      (.returned (.error ⟨⟨"InvalidData"⟩,
        "For portability reasons we do not allow to serialize NaNs."⟩) [[9]]) :=
  ⟨(primitiveSerializeRun_ofFunction encodeF64 recordingWriter _ _ _).2 rfl,
    (primitiveSerializeRun_ofFunction encodeF64 recordingWriter _ _ _).2 rfl⟩

/-- Negative infinity is not a NaN. -/
theorem f64_infinity_written :
    f64.serialize_run log ([] : Log) (0xfff0000000000000 : UInt64)
      (.returned (.ok ()) [[0, 0, 0, 0, 0, 0, 0xf0, 0xff]]) :=
  (primitiveSerializeRun_ofFunction encodeF64 recordingWriter _ _ _).2 rfl

/-- `[u8; 16]` (the `WrappedI80F48` path) is one `write_all`. -/
def sixteen : FixedArray UInt8 16 := ⟨(List.range 16).map UInt8.ofNat, by simp⟩

theorem byte_array_16_one_chunk :
    Array.serialize_run ⟨Log, Empty, Empty, Callback.ofFunction recordingWriter, 16, .byte⟩
      ([] : Log) sixteen (.returned (.ok ()) [(List.range 16).map UInt8.ofNat]) :=
  (arraySerializeRun_byte 16 recordingWriter _ _ _).2 rfl

/-- `Option<[u8; 32]>` as `Option<Address>` would compose: the tag chunk, then
the single chunk of the array. The element callback is the `[u8; 32]` serializer. -/
def thirtyTwo : FixedArray UInt8 32 := ⟨List.replicate 32 7, by simp⟩

theorem option_of_byte_array :
    Option.serialize_run
      ⟨Log, Empty, Empty, Callback.ofFunction recordingWriter, FixedArray UInt8 32,
        Callback.ofFunction (byteArraySerializeFn 32 recordingWriter)⟩
      ([] : Log) (some thirtyTwo) (.returned (.ok ()) [[1], List.replicate 32 7]) ∧
    Option.serialize_run
      ⟨Log, Empty, Empty, Callback.ofFunction recordingWriter, FixedArray UInt8 32,
        Callback.ofFunction (byteArraySerializeFn 32 recordingWriter)⟩
      ([] : Log) none (.returned (.ok ()) [[0]]) :=
  ⟨(optionSerializeRun_ofFunction recordingWriter _ _ _ _).2 rfl,
    (optionSerializeRun_ofFunction recordingWriter _ _ _ _).2 rfl⟩

/-- A failing writer: the error and the partial state are retained. -/
def failing : WriterFn Log Empty Empty := fun log chunk =>
  .returned (.error ⟨⟨"WriteZero"⟩, "failed to write whole buffer"⟩) (log ++ [chunk.take 1])

theorem writer_error_retains_partial_write :
    u64.serialize_run ⟨Log, Empty, Empty, Callback.ofFunction failing⟩ ([] : Log) (5 : UInt64)
      (.returned (.error ⟨⟨"WriteZero"⟩, "failed to write whole buffer"⟩) [[5]]) :=
  (primitiveSerializeRun_ofFunction encodeU64 failing _ _ _).2 rfl

theorem u8_slice_is_some :
    (u8.u8_slice_model () [1, 2, 3]).1 = some [1, 2, 3] := rfl

theorem u8_one_byte_chunk :
    u8.serialize_run log ([[4]] : Log) (200 : UInt8) (.returned (.ok ()) [[4], [200]]) :=
  (primitiveSerializeRun_ofFunction encodeU8 recordingWriter _ _ _).2 rfl

end SolanalibTest.Specs.Borsh.Ser
