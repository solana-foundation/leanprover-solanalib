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

/-! borsh 0.10.4 decoding at `R = &[u8]` (`src/de/mod.rs`, `src/de/hint.rs`).
Every decoding error raised by these members has kind `InvalidInput`, except
`Not all bytes read` (`InvalidData`). -/

namespace Solanalib.Specs.Borsh

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

/-- borsh 0.10.4: `InvalidInput` decoding errors and the `Vec` zero-sized message. -/
def invalid_input_profile : Profile := ⟨.invalidInput, zeroSizedVectorMessage⟩

/-! ## Primitive `deserialize_reader` -/

namespace u8.invalid_input

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError UInt8 ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeU8 invalid_input_profile)
def deserialize_reader_model :
    Unit → Solanalib.Runtime.Bytes → (Except IoError UInt8 × Solanalib.Runtime.Bytes) × Unit :=
  decoderModel (decodeU8 invalid_input_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end u8.invalid_input

namespace i8.invalid_input

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError Int8 ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeI8 invalid_input_profile)
def deserialize_reader_model :
    Unit → Solanalib.Runtime.Bytes → (Except IoError Int8 × Solanalib.Runtime.Bytes) × Unit :=
  decoderModel (decodeI8 invalid_input_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end i8.invalid_input

namespace u32.invalid_input

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError UInt32 ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeU32 invalid_input_profile)
def deserialize_reader_model :
    Unit → Solanalib.Runtime.Bytes → (Except IoError UInt32 × Solanalib.Runtime.Bytes) × Unit :=
  decoderModel (decodeU32 invalid_input_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end u32.invalid_input

namespace u64.invalid_input

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError UInt64 ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeU64 invalid_input_profile)
def deserialize_reader_model :
    Unit → Solanalib.Runtime.Bytes → (Except IoError UInt64 × Solanalib.Runtime.Bytes) × Unit :=
  decoderModel (decodeU64 invalid_input_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end u64.invalid_input

namespace bool.invalid_input

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError Bool ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeBool invalid_input_profile)
def deserialize_reader_model :
    Unit → Solanalib.Runtime.Bytes → (Except IoError Bool × Solanalib.Runtime.Bytes) × Unit :=
  decoderModel (decodeBool invalid_input_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end bool.invalid_input

/-! ## Generic `deserialize_reader` -/

namespace Option.invalid_input

def deserialize_reader_contract : Family := optionDecodeFamily invalid_input_profile
def deserialize_reader_run : FamilyRun deserialize_reader_contract := optionDecodeRun
  invalid_input_profile
theorem deserialize_reader_reference :
    FamilyReference deserialize_reader_contract deserialize_reader_run :=
  decodeFamily_reference _ _ _ _ _ _
/-- `Option<u32>`. -/
def deserialize_reader_sample : deserialize_reader_contract.Index :=
  ⟨Unit, Empty, Empty, UInt32, Callback.ofFunction (Decoder.lift (decodeU32 invalid_input_profile))⟩
theorem deserialize_reader_satisfiable :
    FamilySatisfiable deserialize_reader_contract deserialize_reader_sample :=
  ⟨(), [], trivial⟩
theorem deserialize_reader_has_execution :
    FamilyHasExecution deserialize_reader_contract deserialize_reader_run
      deserialize_reader_sample :=
  ⟨(), [1, 7, 0, 0, 0], .returned (.ok (some (7 : UInt32)), []) (), trivial,
    (optionDecodeRun_ofFunction invalid_input_profile _ () _ _).2 rfl⟩

end Option.invalid_input

namespace Vec.invalid_input

/-- `Vec<T>`: zero-sized check, `u32` length, then `u8::vec_from_reader` for
`u8`, or `Vec::with_capacity(hint::cautious::<T>(len))` and `len` element
calls each followed by `push`. The truncated size can cause a division panic
after reading a nonzero length, before allocation or element calls. Allocation
and panic exits go to their respective index providers. -/
def deserialize_reader_contract : Family := vecDecodeFamily invalid_input_profile
def deserialize_reader_run : FamilyRun deserialize_reader_contract := vecDecodeRun
  invalid_input_profile
theorem deserialize_reader_reference :
    FamilyReference deserialize_reader_contract deserialize_reader_run :=
  decodeFamily_reference _ _ _ _ _ _
/-- `Vec<u32>`-like 4-byte elements with an always-returning allocator. -/
def deserialize_reader_sample : deserialize_reader_contract.Index :=
  ⟨Unit, Empty, Empty, .other UInt32 4 (Callback.ofFunction (Decoder.lift (decodeU32
    invalid_input_profile))),
    Callback.ofFunction allocateReturns, noDivisionPanic⟩
theorem deserialize_reader_satisfiable :
    FamilySatisfiable deserialize_reader_contract deserialize_reader_sample :=
  ⟨(), [], trivial⟩
theorem deserialize_reader_has_execution :
    FamilyHasExecution deserialize_reader_contract deserialize_reader_run
      deserialize_reader_sample :=
  ⟨(), [2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], .returned (.ok ([1, 2] : List UInt32), []) (), trivial,
    (vecDecodeRun_ofFunction invalid_input_profile 4 (by right; decide) _ allocateReturns () _ _).2
      rfl⟩

end Vec.invalid_input

/-! ## Trait defaults -/

namespace de.BorshDeserialize

/-- `Self::deserialize_reader(&mut *buf)`: every exit forwarded. -/
def deserialize_contract : Family := deserializeFamily
def deserialize_run : FamilyRun deserialize_contract := deserializeRun
theorem deserialize_reference : FamilyReference deserialize_contract deserialize_run :=
  decodeFamily_reference _ _ _ _ _ _
def deserialize_invalid_input_sample : deserialize_contract.Index :=
  ⟨Unit, Empty, Empty, UInt64, Callback.ofFunction (Decoder.lift (decodeU64 invalid_input_profile))⟩
theorem deserialize_invalid_input_satisfiable : FamilySatisfiable deserialize_contract
  deserialize_invalid_input_sample :=
  ⟨(), [], trivial⟩
theorem deserialize_invalid_input_has_execution :
    FamilyHasExecution deserialize_contract deserialize_run deserialize_invalid_input_sample :=
  ⟨(), [1, 0, 0, 0, 0, 0, 0, 0, 5], .returned (.ok (1 : UInt64), [5]) (), trivial,
    (deserializeRun_ofFunction _ () _ _).2 rfl⟩

/-- `Self::deserialize` on a local copy of the slice, then
`Not all bytes read` if bytes remain. The index callback is `Self::deserialize`. -/
def try_from_slice_contract : Family := tryFromSliceFamily
def try_from_slice_run : FamilyRun try_from_slice_contract := tryFromSliceRun
theorem try_from_slice_reference : FamilyReference try_from_slice_contract try_from_slice_run :=
  tryFromSlice_reference
def try_from_slice_sample : try_from_slice_contract.Index :=
  ⟨Unit, Empty, Empty, UInt64, Callback.ofFunction (Decoder.lift (decodeU64 invalid_input_profile))⟩
theorem try_from_slice_satisfiable :
    FamilySatisfiable try_from_slice_contract try_from_slice_sample :=
  ⟨(), [], trivial⟩
/-- The leftover-bytes error is a permitted execution. -/
theorem try_from_slice_has_execution :
    FamilyHasExecution try_from_slice_contract try_from_slice_run try_from_slice_sample :=
  ⟨(), [1, 0, 0, 0, 0, 0, 0, 0, 5], .returned (.error notAllBytesRead) (), trivial,
    (tryFromSliceRun_ofFunction _ () _ _).2 rfl⟩

/-- Default `vec_from_reader`: `Ok(None)` without reading. -/
def vec_from_reader_contract : Family := vecFromReaderDefaultFamily
def vec_from_reader_run : FamilyRun vec_from_reader_contract := vecFromReaderDefaultRun
theorem vec_from_reader_reference :
    FamilyReference vec_from_reader_contract vec_from_reader_run :=
  vecFromReaderDefault_reference
def vec_from_reader_sample : vec_from_reader_contract.Index := ⟨UInt32⟩
theorem vec_from_reader_satisfiable :
    FamilySatisfiable vec_from_reader_contract vec_from_reader_sample :=
  ⟨(), ((3 : UInt32), []), trivial⟩
theorem vec_from_reader_has_execution :
    FamilyHasExecution vec_from_reader_contract vec_from_reader_run vec_from_reader_sample :=
  ⟨(), ((3 : UInt32), [9]), .returned (.ok none, [9]) (), trivial, rfl⟩

end de.BorshDeserialize

namespace de.hint

/-- The cautious hint after `size_of::<T>() as u32`, including the
division-by-zero panic when that cast is zero. -/
def cautious_contract : Family := cautiousFamily
def cautious_run : FamilyRun cautious_contract := cautiousRun
theorem cautious_reference : FamilyReference cautious_contract cautious_run :=
  Borsh.cautious_reference
/-- A 16-byte element type. -/
def cautious_sample : cautious_contract.Index := ⟨Unit, Empty, Empty, 16, noDivisionPanic⟩
theorem cautious_satisfiable : FamilySatisfiable cautious_contract cautious_sample :=
  ⟨(), (1000 : UInt32), trivial⟩
theorem cautious_has_execution :
    FamilyHasExecution cautious_contract cautious_run cautious_sample :=
  ⟨(), (1000 : UInt32), .returned (256 : Nat) (), trivial, rfl⟩

end de.hint

end Solanalib.Specs.Borsh

/-! borsh 1.6.1 decoding at `R = &[u8]` (`src/de/mod.rs`). Every decoding
error raised by these members has kind `InvalidData`. -/

namespace Solanalib.Specs.Borsh

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

/-- borsh 1.6.1: `InvalidData` decoding errors and `ERROR_ZST_FORBIDDEN`. -/
def invalid_data_profile : Profile := ⟨.invalidData, zeroSizedCollectionMessage⟩

/-! ## Primitive `deserialize_reader` -/

namespace u8.invalid_data

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError UInt8 ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeU8 invalid_data_profile)
def deserialize_reader_model : Unit → Solanalib.Runtime.Bytes → (Except IoError UInt8 ×
  Solanalib.Runtime.Bytes) × Unit :=
  decoderModel (decodeU8 invalid_data_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

/-- `u8::array_from_reader::<&[u8], N>`. -/
def array_from_reader_contract : Family := byteArrayFromReaderFamily invalid_data_profile
def array_from_reader_run : FamilyRun array_from_reader_contract := byteArrayFromReaderRun
  invalid_data_profile
theorem array_from_reader_reference :
    FamilyReference array_from_reader_contract array_from_reader_run :=
  decodeFamily_reference _ _ _ _ _ _
def array_from_reader_sample : array_from_reader_contract.Index := ⟨32⟩
theorem array_from_reader_satisfiable :
    FamilySatisfiable array_from_reader_contract array_from_reader_sample :=
  ⟨(), [], trivial⟩
theorem array_from_reader_has_execution :
    FamilyHasExecution array_from_reader_contract array_from_reader_run
      array_from_reader_sample :=
  ⟨(), [], .returned (byteArrayFromReader invalid_data_profile 32 []) (), trivial, rfl⟩

end u8.invalid_data

namespace u32.invalid_data

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError UInt32 ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeU32 invalid_data_profile)
def deserialize_reader_model :
    Unit → Solanalib.Runtime.Bytes → (Except IoError UInt32 × Solanalib.Runtime.Bytes) × Unit :=
  decoderModel (decodeU32 invalid_data_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end u32.invalid_data

namespace i32.invalid_data

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError Int32 ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeI32 invalid_data_profile)
def deserialize_reader_model :
    Unit → Solanalib.Runtime.Bytes → (Except IoError Int32 × Solanalib.Runtime.Bytes) × Unit :=
  decoderModel (decodeI32 invalid_data_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end i32.invalid_data

namespace u64.invalid_data

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError UInt64 ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeU64 invalid_data_profile)
def deserialize_reader_model :
    Unit → Solanalib.Runtime.Bytes → (Except IoError UInt64 × Solanalib.Runtime.Bytes) × Unit :=
  decoderModel (decodeU64 invalid_data_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end u64.invalid_data

namespace i64.invalid_data

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError Int64 ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeI64 invalid_data_profile)
def deserialize_reader_model :
    Unit → Solanalib.Runtime.Bytes → (Except IoError Int64 × Solanalib.Runtime.Bytes) × Unit :=
  decoderModel (decodeI64 invalid_data_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end i64.invalid_data

namespace f64.invalid_data

/-- Binary64 bits; a NaN bit pattern is rejected after its 8 bytes. -/
def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError Float64.Bits ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeF64 invalid_data_profile)
def deserialize_reader_model :
    Unit → Solanalib.Runtime.Bytes → (Except IoError Float64.Bits × Solanalib.Runtime.Bytes) × Unit
      :=
  decoderModel (decodeF64 invalid_data_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end f64.invalid_data

namespace bool.invalid_data

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError Bool ×
      Solanalib.Runtime.Bytes) :=
  decoderContract (decodeBool invalid_data_profile)
def deserialize_reader_model :
    Unit → Solanalib.Runtime.Bytes → (Except IoError Bool × Solanalib.Runtime.Bytes) × Unit :=
  decoderModel (decodeBool invalid_data_profile)
theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model := decoderContract_realized _
theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end bool.invalid_data

/-! ## Generic `deserialize_reader` -/

namespace Option.invalid_data

def deserialize_reader_contract : Family := optionDecodeFamily invalid_data_profile
def deserialize_reader_run : FamilyRun deserialize_reader_contract := optionDecodeRun
  invalid_data_profile
theorem deserialize_reader_reference :
    FamilyReference deserialize_reader_contract deserialize_reader_run :=
  decodeFamily_reference _ _ _ _ _ _
/-- `Option<u32>` with a state-preserving element decoder. -/
def deserialize_reader_sample : deserialize_reader_contract.Index :=
  ⟨Unit, Empty, Empty, UInt32, Callback.ofFunction (Decoder.lift (decodeU32 invalid_data_profile))⟩
theorem deserialize_reader_satisfiable :
    FamilySatisfiable deserialize_reader_contract deserialize_reader_sample :=
  ⟨(), [], trivial⟩
theorem deserialize_reader_has_execution :
    FamilyHasExecution deserialize_reader_contract deserialize_reader_run
      deserialize_reader_sample :=
  ⟨(), [1, 7, 0, 0, 0], .returned (.ok (some (7 : UInt32)), []) (), trivial,
    (optionDecodeRun_ofFunction invalid_data_profile _ () _ _).2 rfl⟩

end Option.invalid_data

namespace Array.invalid_data

/-- `[T; N]`: one `read_exact` for `u8` elements, otherwise `N` element calls. -/
def deserialize_reader_contract : Family := arrayDecodeFamily invalid_data_profile
def deserialize_reader_run : FamilyRun deserialize_reader_contract := arrayDecodeRun
  invalid_data_profile
theorem deserialize_reader_reference :
    FamilyReference deserialize_reader_contract deserialize_reader_run :=
  decodeFamily_reference _ _ _ _ _ _
/-- `[u8; 32]`, the path of every `Address` field. -/
def deserialize_reader_sample : deserialize_reader_contract.Index :=
  ⟨Unit, Empty, Empty, 32, .byte⟩
theorem deserialize_reader_satisfiable :
    FamilySatisfiable deserialize_reader_contract deserialize_reader_sample :=
  ⟨(), [], trivial⟩
theorem deserialize_reader_has_execution :
    FamilyHasExecution deserialize_reader_contract deserialize_reader_run
      deserialize_reader_sample :=
  ⟨(), List.replicate 32 9, .returned (decodeByteArray invalid_data_profile 32 (List.replicate 32
    9)) (),
    trivial, rfl⟩

end Array.invalid_data

/-! ## Trait default `deserialize` -/

namespace de.BorshDeserialize

def deserialize_invalid_data_sample : deserialize_contract.Index :=
  ⟨Unit, Empty, Empty, UInt64, Callback.ofFunction (Decoder.lift (decodeU64 invalid_data_profile))⟩
theorem deserialize_invalid_data_satisfiable : FamilySatisfiable deserialize_contract
  deserialize_invalid_data_sample :=
  ⟨(), [], trivial⟩
theorem deserialize_invalid_data_has_execution :
    FamilyHasExecution deserialize_contract deserialize_run deserialize_invalid_data_sample :=
  ⟨(), [1, 0, 0, 0, 0, 0, 0, 0, 5], .returned (.ok (1 : UInt64), [5]) (), trivial,
    (deserializeRun_ofFunction _ () _ _).2 rfl⟩

end de.BorshDeserialize

end Solanalib.Specs.Borsh
