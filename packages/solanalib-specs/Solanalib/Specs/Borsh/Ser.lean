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

/-! borsh 1.6.1 serialization over a generic writer `W: Write`
(`src/ser/mod.rs`). The `write_all` callback of the writer is the index callback; each
member issues its exact `write_all` chunks in order and stops at the first
error. -/

namespace Solanalib.Specs.Borsh

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

/-- The closed writer of the serializer samples: it records every chunk. -/
def recordingWriterIndex : WriterIndex :=
  ⟨List Solanalib.Runtime.Bytes, Empty, Empty, Callback.ofFunction recordingWriter⟩

namespace u8

/-- `writer.write_all(core::slice::from_ref(self))`. -/
def serialize_contract : Family := primitiveSerializeFamily UInt8 encodeU8
def serialize_run : FamilyRun serialize_contract := primitiveSerializeRun encodeU8
theorem serialize_reference : FamilyReference serialize_contract serialize_run :=
  serializeFamily_reference _ _ _ _ _ _
def serialize_sample : serialize_contract.Index := recordingWriterIndex
theorem serialize_satisfiable : FamilySatisfiable serialize_contract serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), (7 : UInt8), trivial⟩
theorem serialize_has_execution :
    FamilyHasExecution serialize_contract serialize_run serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), (7 : UInt8), .returned (.ok ()) [[7]], trivial,
    (primitiveSerializeRun_ofFunction encodeU8 recordingWriter _ _ _).2 rfl⟩

/-- `<u8 as BorshSerialize>::u8_slice`: `Some(slice)`. -/
def u8_slice_contract : Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Option
  Solanalib.Runtime.Bytes) :=
  u8SliceContract
def u8_slice_model : Unit → Solanalib.Runtime.Bytes → Option Solanalib.Runtime.Bytes × Unit :=
  u8SliceModel
theorem u8_slice_reference : u8_slice_contract.RealizedBy u8_slice_model := u8Slice_realized
theorem u8_slice_satisfiable : u8_slice_contract.Satisfiable := ⟨(), [], trivial⟩

end u8

namespace bool

/-- `(u8::from(*self)).serialize(writer)`: one byte, `0` or `1`. -/
def serialize_contract : Family := primitiveSerializeFamily Bool encodeBool
def serialize_run : FamilyRun serialize_contract := primitiveSerializeRun encodeBool
theorem serialize_reference : FamilyReference serialize_contract serialize_run :=
  serializeFamily_reference _ _ _ _ _ _
def serialize_sample : serialize_contract.Index := recordingWriterIndex
theorem serialize_satisfiable : FamilySatisfiable serialize_contract serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), true, trivial⟩
theorem serialize_has_execution :
    FamilyHasExecution serialize_contract serialize_run serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), true, .returned (.ok ()) [[1]], trivial,
    (primitiveSerializeRun_ofFunction encodeBool recordingWriter _ _ _).2 rfl⟩

end bool

namespace u32

/-- `writer.write_all(&self.to_le_bytes())`. -/
def serialize_contract : Family := primitiveSerializeFamily UInt32 encodeU32
def serialize_run : FamilyRun serialize_contract := primitiveSerializeRun encodeU32
theorem serialize_reference : FamilyReference serialize_contract serialize_run :=
  serializeFamily_reference _ _ _ _ _ _
def serialize_sample : serialize_contract.Index := recordingWriterIndex
theorem serialize_satisfiable : FamilySatisfiable serialize_contract serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), (0x04030201 : UInt32), trivial⟩
theorem serialize_has_execution :
    FamilyHasExecution serialize_contract serialize_run serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), (0x04030201 : UInt32), .returned (.ok ()) [[1, 2, 3, 4]],
    trivial,
    (primitiveSerializeRun_ofFunction encodeU32 recordingWriter _ _ _).2 rfl⟩

end u32

namespace u64

/-- `writer.write_all(&self.to_le_bytes())`. -/
def serialize_contract : Family := primitiveSerializeFamily UInt64 encodeU64
def serialize_run : FamilyRun serialize_contract := primitiveSerializeRun encodeU64
theorem serialize_reference : FamilyReference serialize_contract serialize_run :=
  serializeFamily_reference _ _ _ _ _ _
def serialize_sample : serialize_contract.Index := recordingWriterIndex
theorem serialize_satisfiable : FamilySatisfiable serialize_contract serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), (1 : UInt64), trivial⟩
theorem serialize_has_execution :
    FamilyHasExecution serialize_contract serialize_run serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), (1 : UInt64), .returned (.ok ()) [[1, 0, 0, 0, 0, 0, 0, 0]],
    trivial, (primitiveSerializeRun_ofFunction encodeU64 recordingWriter _ _ _).2 rfl⟩

end u64

namespace i64

/-- `writer.write_all(&self.to_le_bytes())`, binary radix complement. -/
def serialize_contract : Family := primitiveSerializeFamily Int64 encodeI64
def serialize_run : FamilyRun serialize_contract := primitiveSerializeRun encodeI64
theorem serialize_reference : FamilyReference serialize_contract serialize_run :=
  serializeFamily_reference _ _ _ _ _ _
def serialize_sample : serialize_contract.Index := recordingWriterIndex
theorem serialize_satisfiable : FamilySatisfiable serialize_contract serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), (-2 : Int64), trivial⟩
theorem serialize_has_execution :
    FamilyHasExecution serialize_contract serialize_run serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), (-2 : Int64),
    .returned (.ok ()) [[254, 255, 255, 255, 255, 255, 255, 255]], trivial,
    (primitiveSerializeRun_ofFunction encodeI64 recordingWriter _ _ _).2 rfl⟩

end i64

namespace f64

/-- A NaN returns `InvalidData` before any write; otherwise
`writer.write_all(&self.to_bits().to_le_bytes())`. -/
def serialize_contract : Family := primitiveSerializeFamily Float64.Bits encodeF64
def serialize_run : FamilyRun serialize_contract := primitiveSerializeRun encodeF64
theorem serialize_reference : FamilyReference serialize_contract serialize_run :=
  serializeFamily_reference _ _ _ _ _ _
def serialize_sample : serialize_contract.Index := recordingWriterIndex
theorem serialize_satisfiable : FamilySatisfiable serialize_contract serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), Float64.quietNaN, trivial⟩
/-- The reachable error: a NaN writes nothing. -/
theorem serialize_has_execution :
    FamilyHasExecution serialize_contract serialize_run serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), Float64.quietNaN, .returned (.error serializeNaN) [],
    trivial,
    (primitiveSerializeRun_ofFunction encodeF64 recordingWriter _ _ _).2 rfl⟩

end f64

namespace Option

/-- `0u8.serialize(writer)` for `None`; `1u8.serialize(writer)?` then
`value.serialize(writer)` for `Some`. -/
def serialize_contract : Family := optionSerializeFamily
def serialize_run : FamilyRun serialize_contract := optionSerializeRun
theorem serialize_reference : FamilyReference serialize_contract serialize_run :=
  serializeFamily_reference _ _ _ _ _ _
/-- `Option<u64>` over the recording writer. -/
def serialize_sample : serialize_contract.Index :=
  ⟨List Solanalib.Runtime.Bytes, Empty, Empty, Callback.ofFunction recordingWriter, UInt64,
    Callback.ofFunction (Encoder.serializeFn encodeU64 recordingWriter)⟩
theorem serialize_satisfiable : FamilySatisfiable serialize_contract serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), (none : Option UInt64), trivial⟩
theorem serialize_has_execution :
    FamilyHasExecution serialize_contract serialize_run serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), some (2 : UInt64),
    .returned (.ok ()) [[1], [2, 0, 0, 0, 0, 0, 0, 0]], trivial,
    (optionSerializeRun_ofFunction recordingWriter _ _ _ _).2 rfl⟩

end Option

namespace Array

/-- `[T; N]`: `Ok(())` for `N = 0`; one `write_all` of all bytes when
`T::u8_slice` is `Some` (`u8`); otherwise each element in order. -/
def serialize_contract : Family := arraySerializeFamily
def serialize_run : FamilyRun serialize_contract := arraySerializeRun
theorem serialize_reference : FamilyReference serialize_contract serialize_run :=
  serializeFamily_reference _ _ _ _ _ _
/-- `[u8; 32]`, the `Address` path, over the recording writer. -/
def serialize_sample : serialize_contract.Index :=
  ⟨List Solanalib.Runtime.Bytes, Empty, Empty, Callback.ofFunction recordingWriter, 32, .byte⟩
theorem serialize_satisfiable : FamilySatisfiable serialize_contract serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), (⟨List.replicate 32 0, by simp⟩ : FixedArray UInt8 32),
    trivial⟩
theorem serialize_has_execution :
    FamilyHasExecution serialize_contract serialize_run serialize_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), (⟨List.replicate 32 5, by simp⟩ : FixedArray UInt8 32),
    .returned (.ok ()) [List.replicate 32 5], trivial,
    (arraySerializeRun_byte 32 recordingWriter _ _ _).2 rfl⟩

end Array

end Solanalib.Specs.Borsh
