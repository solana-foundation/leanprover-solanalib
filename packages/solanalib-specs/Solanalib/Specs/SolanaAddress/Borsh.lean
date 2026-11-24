/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Address
public import Solanalib.Specs.Core.BorshFamily
public import Solanalib.Specs.Borsh.De
public import Solanalib.Specs.Borsh.Ser
public import Solanalib.Specs.Core.AddressOperations
public import Solanalib.Specs.Core.AddressBorsh

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! The `BorshSerialize` and `BorshDeserialize` implementations derived for
`Address` (line 90). Each derived body makes one call on the `[u8; 32]` field,
so both models run the Borsh 1.6.1 `[T; N]` models at `T = u8`, `N = 32`. -/

namespace Solanalib.Specs.SolanaAddress.Address

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

/-- The private `[u8; 32]` field. -/
def field (address : _root_.Solanalib.Runtime.Pubkey) : FixedArray UInt8 32 :=
  ⟨address.bytes, address.length_eq⟩

/-- `Self(field)`. -/
def ofField (array : FixedArray UInt8 32) : _root_.Solanalib.Runtime.Pubkey :=
  ⟨array.val, array.property⟩

@[simp] theorem field_val (address : _root_.Solanalib.Runtime.Pubkey) : (field address).val =
  address.bytes :=
  rfl

@[simp] theorem ofField_field (address : _root_.Solanalib.Runtime.Pubkey) : ofField (field address)
  = address :=
  rfl

/-! ## Serialization -/

/-- The derived `BorshSerialize::serialize(&self.0, writer)?;` followed by `Ok(())`. -/
def questionOk (result : Except IoError Unit) : Except IoError Unit :=
  result.bind fun _ => .ok ()

@[simp] theorem questionOk_eq (result : Except IoError Unit) : questionOk result = result := by
  cases result <;> rfl

/-- The nonempty `[u8; 32]` path makes exactly one `write_all` of all bytes and
returns the outcome of that call. -/
theorem byteArray32_serialize_iff {State Unwind Terminal : Type}
    (writer : Writer State Unwind Terminal) (before : State) (bytes : FixedArray UInt8 32)
    (outcome : Outcome State (Except IoError Unit) Unwind Terminal) :
    Solanalib.Specs.Borsh.Array.serialize_run ⟨State, Unwind, Terminal, writer, 32, .byte⟩ before
      bytes
        outcome ↔
      writer before bytes.val outcome := by
  have program : byteArraySerializeProgram (α := Empty) 32 bytes =
      .call (.writeAll bytes.val) fun result =>
        match result with
        | .error error => .pure (.error error)
        | .ok () => .pure (.ok ()) := rfl
  show (byteArraySerializeProgram (α := Empty) 32 bytes).Runs (writeHandler writer noElement)
    before outcome ↔ _
  rw [program, Program.runs_call]
  constructor
  · rintro ⟨intermediate, step, rest⟩
    cases intermediate with
    | returned result state =>
      cases result with
      | error error =>
        have exact : outcome = .returned (.error error) state := rest
        subst exact
        exact step
      | ok done =>
        cases done
        have exact : outcome = .returned (.ok ()) state := rest
        subst exact
        exact step
    | unwound reason state =>
      have exact : outcome = .unwound reason state := rest
      subst exact
      exact step
    | terminated reason =>
      have exact : outcome = .terminated reason := rest
      subst exact
      exact step
  · intro step
    refine ⟨outcome, step, ?_⟩
    cases outcome with
    | returned result state =>
      cases result with
      | error error => exact (rfl : Outcome.returned (Except.error error) state = _)
      | ok done => cases done; exact (rfl : Outcome.returned (Except.ok ()) state = _)
    | unwound => rfl
    | terminated => rfl

/-- The writer `W` is the family index. Its `write_all` receives all 32 address
bytes once; its ordinary error, partial writer state, unwind state and terminal
reason are returned unchanged. -/
def serialize_contract : Family where
  Index := WriterIndex
  State := WriterIndex.State
  Args := fun _ => _root_.Solanalib.Runtime.Pubkey
  Value := fun _ => Except IoError Unit
  Unwind := WriterIndex.Unwind
  Terminal := WriterIndex.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before address outcome => index.writer before address.bytes outcome }

/-- The derived body: the Borsh 1.6.1 `[T; N]` serializer at `T = u8`, `N = 32`,
then `?` and `Ok(())`. -/
def serialize_run : FamilyRun serialize_contract := fun index =>
  Callback.map questionOk fun before address =>
    Solanalib.Specs.Borsh.Array.serialize_run
      ⟨index.State, index.Unwind, index.Terminal, index.writer, 32, .byte⟩ before (field address)

theorem serialize_run_iff (index : serialize_contract.Index)
    (before : serialize_contract.State index) (address : _root_.Solanalib.Runtime.Pubkey)
    (outcome : Outcome index.State (Except IoError Unit) index.Unwind index.Terminal) :
    serialize_run index before address outcome ↔ index.writer before address.bytes outcome := by
  constructor
  · rintro ⟨inner, step, mapped⟩
    have written := (byteArray32_serialize_iff index.writer before (field address) inner).1 step
    have same : Outcome.map questionOk inner = inner := by
      cases inner <;> simp only [Outcome.map, questionOk_eq]
    have exact : inner = outcome := same.symm.trans mapped
    subst exact
    exact written
  · intro step
    refine ⟨outcome, (byteArray32_serialize_iff index.writer before (field address) outcome).2
      step, ?_⟩
    show Outcome.map questionOk outcome = outcome
    cases outcome <;> simp only [Outcome.map, questionOk_eq]

theorem serialize_reference : FamilyReference serialize_contract serialize_run :=
  fun index before address outcome _ step => (serialize_run_iff index before address outcome).1 step

/-- The `write_all` error from `std` when a write returns zero bytes. -/
def sampleWriteError : IoError := ⟨⟨"WriteZero"⟩, "failed to write whole buffer"⟩

/-- A writer that appends three bytes and then fails. -/
def sampleWriter : Writer _root_.Solanalib.Runtime.Bytes Nat Nat := fun before bytes outcome =>
  outcome = .returned (.error sampleWriteError) (before ++ bytes.take 3)

def serialize_sample : serialize_contract.Index := ⟨_root_.Solanalib.Runtime.Bytes, Nat, Nat,
  sampleWriter⟩

def sampleAddress : _root_.Solanalib.Runtime.Pubkey := ⟨7 :: List.replicate 31 0, by simp⟩

theorem serialize_satisfiable : FamilySatisfiable serialize_contract serialize_sample :=
  ⟨([] : _root_.Solanalib.Runtime.Bytes), sampleAddress, trivial⟩

/-- A failed write can still have observable effects. This concrete execution
witnesses model consistency; it is not a proof about a Rust writer. -/
theorem serialize_has_execution :
    FamilyHasExecution serialize_contract serialize_run serialize_sample :=
  ⟨([] : _root_.Solanalib.Runtime.Bytes), sampleAddress,
    .returned (.error sampleWriteError) ([7, 0, 0] : _root_.Solanalib.Runtime.Bytes), trivial,
    (serialize_run_iff serialize_sample _ _ _).2 rfl⟩

/-! ## Decoding at `R = &[u8]` -/

/-- `Ok(Self(<[u8; 32]>::deserialize_reader(reader)?))`: one 32-byte read through
`u8::array_from_reader`. Every 32-byte value is accepted. -/
def decoder : Decoder _root_.Solanalib.Runtime.Pubkey :=
  (decodeByteArray Solanalib.Specs.Borsh.invalid_data_profile 32).map ofField

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit _root_.Solanalib.Runtime.Bytes
      (Except IoError _root_.Solanalib.Runtime.Pubkey × _root_.Solanalib.Runtime.Bytes) :=
  decoderContract decoder

def deserialize_reader_model :
    Unit → _root_.Solanalib.Runtime.Bytes → (Except IoError _root_.Solanalib.Runtime.Pubkey ×
      _root_.Solanalib.Runtime.Bytes) × Unit :=
  decoderModel decoder

theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model :=
  decoderContract_realized _

theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

/-- The decoder maps `Self` over exactly the registered Borsh 1.6.1 `[u8; 32]`
reference outcome. -/
theorem decoder_calls_array (input : _root_.Solanalib.Runtime.Bytes) :
    ∃ field, Solanalib.Specs.Borsh.Array.invalid_data.deserialize_reader_run ⟨Unit, Empty, Empty,
      32, .byte⟩ () input
        (.returned field ()) ∧
      decoder input = (field.1.map ofField, field.2) :=
  ⟨decodeByteArray Solanalib.Specs.Borsh.invalid_data_profile 32 input, rfl, rfl⟩

theorem decoder_ok {input : _root_.Solanalib.Runtime.Bytes} (long : 32 ≤ input.length) :
    decoder input = (.ok ⟨input.take 32, by simp [List.length_take, long]⟩, input.drop 32) := by
  simp [decoder, Decoder.map, decodeByteArray, long, ofField, Except.map]

theorem decoder_short {input : _root_.Solanalib.Runtime.Bytes} (short : input.length < 32) :
    decoder input = (.error Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength, []) := by
  simp [decoder, Decoder.map, decodeByteArray, Nat.not_le_of_gt short, Except.map]

end Solanalib.Specs.SolanaAddress.Address

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaAddress.Address

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Operations

/-! The reached Borsh implementation delegates one fixed byte array field.
The provider is the actual writer/read_exact method, including overrides,
ordinary IO errors, partial effects and abnormal exits. -/

def deserialize_reader_read_exact_contract : Family := Borsh.readFamily .invalidData
def deserialize_reader_read_exact_run : FamilyRun deserialize_reader_read_exact_contract :=
  Borsh.readReference .invalidData
def deserialize_reader_read_exact_sample : deserialize_reader_read_exact_contract.Index :=
  Borsh.readSample

theorem deserialize_reader_read_exact_reference : FamilyReference
  deserialize_reader_read_exact_contract deserialize_reader_read_exact_run :=
  Borsh.readReference_correct .invalidData

theorem deserialize_reader_read_exact_has_execution :
    FamilyHasExecution deserialize_reader_read_exact_contract deserialize_reader_read_exact_run
      deserialize_reader_read_exact_sample :=
  Borsh.readSample_execution .invalidData

theorem deserialize_reader_read_exact_satisfiable :
    FamilySatisfiable deserialize_reader_read_exact_contract deserialize_reader_read_exact_sample :=
  deserialize_reader_read_exact_has_execution.satisfiable

end Solanalib.Specs.SolanaAddress.Address
