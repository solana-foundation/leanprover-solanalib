/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorshCodec
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Version-independent borsh contracts and families. Version roots instantiate
them with their `Profile` and register them under their own names. -/

namespace Solanalib.Specs.Core.Borsh

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-! ## Primitive decoders at `R = &[u8]` -/

/-- A primitive decoder agrees with its reference decoding and keeps the
caller state. After an error the remaining slice is unconstrained. -/
def decoderContract {α : Type} (decoder : Decoder α) :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Except IoError α ×
      Solanalib.Runtime.Bytes) :=
  .returning (fun _ _ => True)
    (fun before input result after => DecodeMatches (decoder input) result ∧ after = before)

/-- The executable reference: the `std` slice reader. -/
def decoderModel {α : Type} (decoder : Decoder α) (before : Unit) (input : Solanalib.Runtime.Bytes)
  :
    (Except IoError α × Solanalib.Runtime.Bytes) × Unit :=
  (decoder input, before)

theorem decoderContract_realized {α : Type} (decoder : Decoder α) :
    (decoderContract decoder).RealizedBy (decoderModel decoder) :=
  fun _ input _ => ⟨DecodeMatches.refl (decoder input), rfl⟩

theorem decoderContract_satisfiable {α : Type} (decoder : Decoder α) :
    (decoderContract decoder).Satisfiable :=
  ⟨(), [], trivial⟩

/-! ## Outcome agreement for decoding families -/

/-- Agreement of an actual outcome with an exact reference outcome: decode
results agree by `DecodeMatches` in the same state; other exits are equal. -/
def DecodeOutcomeMatches {State α Unwind Terminal : Type} :
    Outcome State (Except IoError α × Solanalib.Runtime.Bytes) Unwind Terminal →
      Outcome State (Except IoError α × Solanalib.Runtime.Bytes) Unwind Terminal → Prop
  | .returned expected state, actual => ∃ result, actual = .returned result state ∧
      DecodeMatches expected result
  | .unwound reason state, actual => actual = .unwound reason state
  | .terminated reason, actual => actual = .terminated reason

theorem DecodeOutcomeMatches.refl {State α Unwind Terminal : Type}
    (outcome : Outcome State (Except IoError α × Solanalib.Runtime.Bytes) Unwind Terminal) :
    DecodeOutcomeMatches outcome outcome := by
  cases outcome with
  | returned result state => exact ⟨result, rfl, DecodeMatches.refl result⟩
  | unwound => rfl
  | terminated => rfl

/-! ## Family indices -/

/-- Source types and the trait implementation of `T` (or `Self`) at `R = &[u8]`. -/
structure DecodeIndex where
  State : Type
  Unwind : Type
  Terminal : Type
  Value : Type
  decode : Decode State Value Unwind Terminal

structure ArrayDecodeIndex where
  State : Type
  Unwind : Type
  Terminal : Type
  length : Nat
  element : DecodeElement State Unwind Terminal

structure VecDecodeIndex where
  State : Type
  Unwind : Type
  Terminal : Type
  element : DecodeElement State Unwind Terminal
  allocate : Allocate State Unwind Terminal
  /-- The division-by-zero panic, with the slice left after reading the length.
  Its unwind state or terminal reason is determined by the source panic policy. -/
  panic : Callback.Run State Solanalib.Runtime.Bytes Empty Unwind Terminal

/-- The writer `W` of a serializer, by its `write_all`. -/
structure WriterIndex where
  State : Type
  Unwind : Type
  Terminal : Type
  writer : Writer State Unwind Terminal

structure OptionSerializeIndex where
  State : Type
  Unwind : Type
  Terminal : Type
  writer : Writer State Unwind Terminal
  Value : Type
  serialize : Serialize State Value Unwind Terminal

structure ArraySerializeIndex where
  State : Type
  Unwind : Type
  Terminal : Type
  writer : Writer State Unwind Terminal
  length : Nat
  element : SerializeElement State Unwind Terminal

/-- No allocation requests are issued by programs without a `Vec`. -/
def noAllocate {State Unwind Terminal : Type} : Allocate State Unwind Terminal :=
  Callback.ofFunction allocateReturns

/-- An empty panic relation for an adapter whose size rules out this call.
It is never used as a substitute for a reachable source panic. -/
def noDivisionPanic {State Context Unwind Terminal : Type} :
    Callback.Run State Context Empty Unwind Terminal := fun _ _ _ => False

/-! ## A decoding family from a program -/

/-- Decoding family whose reference runs `program` with the index callbacks;
the contract relaxes the remaining slice after an error. -/
def decodeFamily (Index : Type 1) (State Unwind Terminal Value : Index → Type)
    (run : (index : Index) → State index → Solanalib.Runtime.Bytes →
      Outcome (State index) (Except IoError (Value index) × Solanalib.Runtime.Bytes)
        (Unwind index) (Terminal index) → Prop) : Family where
  Index := Index
  State := State
  Args := fun _ => Solanalib.Runtime.Bytes
  Value := fun index => Except IoError (Value index) × Solanalib.Runtime.Bytes
  Unwind := Unwind
  Terminal := Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before input outcome => ∃ exact, run index before input exact ∧
      DecodeOutcomeMatches exact outcome }

theorem decodeFamily_reference (Index : Type 1) (State Unwind Terminal Value : Index → Type)
    (run : (index : Index) → State index → Solanalib.Runtime.Bytes →
      Outcome (State index) (Except IoError (Value index) × Solanalib.Runtime.Bytes)
        (Unwind index) (Terminal index) → Prop) :
    FamilyReference (decodeFamily Index State Unwind Terminal Value run) run :=
  fun _ _ _ outcome _ step => ⟨outcome, step, DecodeOutcomeMatches.refl outcome⟩

/-! ## `Option<T>` decoding -/

def optionDecodeRun (profile : Profile) (index : DecodeIndex) :
    index.State → Solanalib.Runtime.Bytes →
      Outcome index.State (Except IoError (Option index.Value) × Solanalib.Runtime.Bytes)
        index.Unwind index.Terminal → Prop :=
  fun before input outcome =>
    (optionProgram profile input).Runs (decodeHandler index.decode noAllocate) before outcome

def optionDecodeFamily (profile : Profile) : Family :=
  decodeFamily DecodeIndex DecodeIndex.State DecodeIndex.Unwind DecodeIndex.Terminal
    (fun index => Option index.Value) (optionDecodeRun profile)

/-- Executable `Option<T>` decoding at a function element decoder. -/
def optionDecodeFn {State Value Unwind Terminal : Type} (profile : Profile)
    (decode : DecodeFn State Value Unwind Terminal) :
    DecodeFn State (Option Value) Unwind Terminal :=
  fun before input =>
    (optionProgram profile input).run (decodeHandlerFn decode allocateReturns) before

theorem optionDecodeRun_ofFunction {State Value Unwind Terminal : Type} (profile : Profile)
    (decode : DecodeFn State Value Unwind Terminal) (before : State) (input :
      Solanalib.Runtime.Bytes)
    (outcome : Outcome State (Except IoError (Option Value) × Solanalib.Runtime.Bytes) Unwind
      Terminal) :
    optionDecodeRun profile ⟨State, Unwind, Terminal, Value, Callback.ofFunction decode⟩
        before input outcome ↔
      optionDecodeFn profile decode before input = outcome :=
  decode_runs_ofFunction_iff decode allocateReturns _ before outcome

/-! ## `[T; N]` decoding -/

def arrayDecodeRun (profile : Profile) : (index : ArrayDecodeIndex) →
    index.State → Solanalib.Runtime.Bytes →
      Outcome index.State
        (Except IoError (FixedArray index.element.Value index.length) × Solanalib.Runtime.Bytes)
        index.Unwind index.Terminal → Prop
  | ⟨_, _, _, length, .byte⟩ => fun before input outcome =>
    outcome = .returned (decodeByteArray profile length input) before
  | ⟨_, _, _, length, .other _ _ decode⟩ => fun before input outcome =>
    (arrayProgram length input).Runs (decodeHandler decode noAllocate) before outcome

def arrayDecodeFamily (profile : Profile) : Family :=
  decodeFamily ArrayDecodeIndex ArrayDecodeIndex.State ArrayDecodeIndex.Unwind
    ArrayDecodeIndex.Terminal (fun index => FixedArray index.element.Value index.length)
    (arrayDecodeRun profile)

/-- Executable `[T; N]` decoding for an element without the `u8` override. -/
def arrayDecodeFn {State Value Unwind Terminal : Type} (length : Nat)
    (decode : DecodeFn State Value Unwind Terminal) :
    DecodeFn State (FixedArray Value length) Unwind Terminal :=
  fun before input =>
    (arrayProgram length input).run (decodeHandlerFn decode allocateReturns) before

/-- Executable `[u8; N]` decoding. -/
def byteArrayDecodeFn {State Unwind Terminal : Type} (profile : Profile) (length : Nat) :
    DecodeFn State (FixedArray UInt8 length) Unwind Terminal :=
  Decoder.lift (decodeByteArray profile length)

theorem arrayDecodeRun_byte {State Unwind Terminal : Type} (profile : Profile) (length : Nat)
    (before : State) (input : Solanalib.Runtime.Bytes)
    (outcome : Outcome State (Except IoError (FixedArray UInt8 length) × Solanalib.Runtime.Bytes)
      Unwind Terminal) :
    arrayDecodeRun profile ⟨State, Unwind, Terminal, length, .byte⟩ before input outcome ↔
      byteArrayDecodeFn profile length before input = outcome :=
  eq_comm

theorem arrayDecodeRun_ofFunction {State Value Unwind Terminal : Type} (profile : Profile)
    (length size : Nat) (decode : DecodeFn State Value Unwind Terminal) (before : State)
    (input : Solanalib.Runtime.Bytes)
    (outcome : Outcome State (Except IoError (FixedArray Value length) × Solanalib.Runtime.Bytes)
      Unwind Terminal) :
    arrayDecodeRun profile
        ⟨State, Unwind, Terminal, length, .other Value size (Callback.ofFunction decode)⟩
        before input outcome ↔
      arrayDecodeFn length decode before input = outcome :=
  decode_runs_ofFunction_iff decode allocateReturns _ before outcome

/-! ## `Vec<T>` decoding -/

def vecDecodeRun (profile : Profile) : (index : VecDecodeIndex) →
    index.State → Solanalib.Runtime.Bytes →
      Outcome index.State (Except IoError (List index.element.Value) × Solanalib.Runtime.Bytes)
        index.Unwind index.Terminal → Prop
  | ⟨_, _, _, .byte, allocate, _⟩ => fun before input outcome =>
    (byteVecProgram profile input).Runs
      (decodeHandler (Callback.ofFunction (Decoder.lift (decodeU8 profile))) allocate)
      before outcome
  | ⟨_, _, _, .other _ size decode, allocate, panic⟩ => fun before input outcome =>
    (vecProgram profile size input).Runs decode allocate panic before outcome

def vecDecodeFamily (profile : Profile) : Family :=
  decodeFamily VecDecodeIndex VecDecodeIndex.State VecDecodeIndex.Unwind
    VecDecodeIndex.Terminal (fun index => List index.element.Value) (vecDecodeRun profile)

/-- Executable `Vec<T>` decoding for every size, with the source panic policy. -/
def vecDecodeWithPanicFn {State Value Unwind Terminal : Type} (profile : Profile) (size : Nat)
    (decode : DecodeFn State Value Unwind Terminal) (allocate : AllocateFn State Unwind Terminal)
    (panic : State → Solanalib.Runtime.Bytes → Outcome State Empty Unwind Terminal) :
    DecodeFn State (List Value) Unwind Terminal :=
  fun before input => (vecProgram profile size input).run decode allocate panic before

/-- Returning adapter for sizes that cannot reach the division
panic of the vector. This proof restricts only the adapter, not `vecDecodeFamily`. -/
def vecDecodeFn {State Value Unwind Terminal : Type} (profile : Profile) (size : Nat)
    (safe : VecNoDivisionByZero size)
    (decode : DecodeFn State Value Unwind Terminal) (allocate : AllocateFn State Unwind Terminal) :
    DecodeFn State (List Value) Unwind Terminal :=
  fun before input =>
    (vecProgramNormal profile size safe input).run (decodeHandlerFn decode allocate) before

/-- Executable `Vec<u8>` decoding. -/
def byteVecDecodeFn {State Unwind Terminal : Type} (profile : Profile)
    (allocate : AllocateFn State Unwind Terminal) :
    DecodeFn State (List UInt8) Unwind Terminal :=
  fun before input =>
    (byteVecProgram profile input).run
      (decodeHandlerFn (Decoder.lift (decodeU8 profile)) allocate) before

theorem vecDecodeRun_byte {State Unwind Terminal : Type} (profile : Profile)
    (allocate : AllocateFn State Unwind Terminal) (before : State) (input : Solanalib.Runtime.Bytes)
    (outcome : Outcome State (Except IoError (List UInt8) × Solanalib.Runtime.Bytes) Unwind
      Terminal) :
    vecDecodeRun profile ⟨State, Unwind, Terminal, .byte, Callback.ofFunction allocate,
      noDivisionPanic⟩
        before input outcome ↔
      byteVecDecodeFn profile allocate before input = outcome :=
  decode_runs_ofFunction_iff _ allocate _ before outcome

theorem vecDecodeRun_ofFunction {State Value Unwind Terminal : Type} (profile : Profile)
    (size : Nat) (safe : VecNoDivisionByZero size) (decode : DecodeFn State Value Unwind Terminal)
    (allocate : AllocateFn State Unwind Terminal) (before : State) (input : Solanalib.Runtime.Bytes)
    (outcome : Outcome State (Except IoError (List Value) × Solanalib.Runtime.Bytes) Unwind
      Terminal) :
    vecDecodeRun profile
        ⟨State, Unwind, Terminal, .other Value size (Callback.ofFunction decode),
          Callback.ofFunction allocate, noDivisionPanic⟩ before input outcome ↔
      vecDecodeFn profile size safe decode allocate before input = outcome := by
  change (vecProgram profile size input).Runs _ _ _ before outcome ↔ _
  rw [vecProgram_eq_ready profile size safe input]
  exact decode_runs_ofFunction_iff decode allocate _ before outcome

theorem vecDecodeRun_withPanic_ofFunction {State Value Unwind Terminal : Type} (profile : Profile)
    (size : Nat) (decode : DecodeFn State Value Unwind Terminal)
    (allocate : AllocateFn State Unwind Terminal)
    (panic : State → Solanalib.Runtime.Bytes → Outcome State Empty Unwind Terminal)
    (before : State) (input : Solanalib.Runtime.Bytes)
    (outcome : Outcome State (Except IoError (List Value) × Solanalib.Runtime.Bytes) Unwind
      Terminal) :
    vecDecodeRun profile
        ⟨State, Unwind, Terminal, .other Value size (Callback.ofFunction decode),
          Callback.ofFunction allocate, Callback.ofFunction panic⟩ before input outcome ↔
      vecDecodeWithPanicFn profile size decode allocate panic before input = outcome :=
  VecProgram.runs_ofFunction_iff decode allocate panic _ before outcome

/-! ## Default `deserialize` -/

def deserializeRun (index : DecodeIndex) :
    index.State → Solanalib.Runtime.Bytes →
      Outcome index.State (Except IoError index.Value × Solanalib.Runtime.Bytes)
        index.Unwind index.Terminal → Prop :=
  fun before input outcome =>
    (deserializeProgram input).Runs (decodeHandler index.decode noAllocate) before outcome

def deserializeFamily : Family :=
  decodeFamily DecodeIndex DecodeIndex.State DecodeIndex.Unwind DecodeIndex.Terminal
    DecodeIndex.Value deserializeRun

/-- `deserialize` forwards every exit of `deserialize_reader` unchanged. -/
theorem deserializeRun_iff (index : DecodeIndex) (before : index.State) (input :
  Solanalib.Runtime.Bytes)
    (outcome : Outcome index.State (Except IoError index.Value × Solanalib.Runtime.Bytes)
      index.Unwind index.Terminal) :
    deserializeRun index before input outcome ↔ index.decode before input outcome := by
  unfold deserializeRun deserializeProgram
  rw [Program.runs_call]
  constructor
  · rintro ⟨intermediate, step, rest⟩
    cases intermediate with
    | returned response state =>
      dsimp only at rest
      rw [Program.runs_pure] at rest
      cases rest; exact step
    | unwound reason state => dsimp only at rest; cases rest; exact step
    | terminated reason => dsimp only at rest; cases rest; exact step
  · intro step
    refine ⟨outcome, step, ?_⟩
    cases outcome with
    | returned => exact (Program.runs_pure _ _ _ _).2 rfl
    | unwound => rfl
    | terminated => rfl

def deserializeFn {State Value Unwind Terminal : Type}
    (decode : DecodeFn State Value Unwind Terminal) : DecodeFn State Value Unwind Terminal :=
  fun before input => (deserializeProgram input).run (decodeHandlerFn decode allocateReturns) before

theorem deserializeRun_ofFunction {State Value Unwind Terminal : Type}
    (decode : DecodeFn State Value Unwind Terminal) (before : State) (input :
      Solanalib.Runtime.Bytes)
    (outcome : Outcome State (Except IoError Value × Solanalib.Runtime.Bytes) Unwind Terminal) :
    deserializeRun ⟨State, Unwind, Terminal, Value, Callback.ofFunction decode⟩
        before input outcome ↔
      deserializeFn decode before input = outcome :=
  decode_runs_ofFunction_iff decode allocateReturns _ before outcome

/-! ## Default `try_from_slice` -/

def tryFromSliceRun (index : DecodeIndex) :
    index.State → Solanalib.Runtime.Bytes →
      Outcome index.State (Except IoError index.Value) index.Unwind index.Terminal → Prop :=
  fun before input outcome =>
    (tryFromSliceProgram input).Runs (decodeHandler index.decode noAllocate) before outcome

/-- `Self::deserialize` on the slice; leftover bytes give `Not all bytes read`.
The local slice is discarded, so the contract is the reference itself. -/
def tryFromSliceFamily : Family where
  Index := DecodeIndex
  State := DecodeIndex.State
  Args := fun _ => Solanalib.Runtime.Bytes
  Value := fun index => Except IoError index.Value
  Unwind := DecodeIndex.Unwind
  Terminal := DecodeIndex.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before input outcome => tryFromSliceRun index before input outcome }

theorem tryFromSlice_reference : FamilyReference tryFromSliceFamily tryFromSliceRun :=
  fun _ _ _ _ _ step => step

def tryFromSliceFn {State Value Unwind Terminal : Type}
    (decode : DecodeFn State Value Unwind Terminal) :
    State → Solanalib.Runtime.Bytes → Outcome State (Except IoError Value) Unwind Terminal :=
  fun before input =>
    (tryFromSliceProgram input).run (decodeHandlerFn decode allocateReturns) before

theorem tryFromSliceRun_ofFunction {State Value Unwind Terminal : Type}
    (decode : DecodeFn State Value Unwind Terminal) (before : State) (input :
      Solanalib.Runtime.Bytes)
    (outcome : Outcome State (Except IoError Value) Unwind Terminal) :
    tryFromSliceRun ⟨State, Unwind, Terminal, Value, Callback.ofFunction decode⟩
        before input outcome ↔
      tryFromSliceFn decode before input = outcome :=
  decode_runs_ofFunction_iff decode allocateReturns _ before outcome

/-! ## Serialization families -/

/-- Serialization family whose contract is the exact relation of its program over
the writer and element callbacks: the `write_all` chunks in order, stopping at
the first error, with every callback exit retained. -/
def serializeFamily (Index : Type 1) (State Unwind Terminal Args : Index → Type)
    (run : (index : Index) → State index → Args index →
      Outcome (State index) (Except IoError Unit) (Unwind index) (Terminal index) → Prop) :
    Family where
  Index := Index
  State := State
  Args := Args
  Value := fun _ => Except IoError Unit
  Unwind := Unwind
  Terminal := Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before value outcome => run index before value outcome }

theorem serializeFamily_reference (Index : Type 1) (State Unwind Terminal Args : Index → Type)
    (run : (index : Index) → State index → Args index →
      Outcome (State index) (Except IoError Unit) (Unwind index) (Terminal index) → Prop) :
    FamilyReference (serializeFamily Index State Unwind Terminal Args run) run :=
  fun _ _ _ _ _ step => step

/-! ### Primitive serializers -/

def primitiveSerializeRun {Value : Type} (encoder : Encoder Value) (index : WriterIndex) :
    index.State → Value → Outcome index.State (Except IoError Unit) index.Unwind index.Terminal →
      Prop :=
  fun before value outcome =>
    (encodeProgram (α := Empty) encoder value).Runs (writeHandler index.writer noElement)
      before outcome

def primitiveSerializeFamily (Value : Type) (encoder : Encoder Value) : Family :=
  serializeFamily WriterIndex WriterIndex.State WriterIndex.Unwind WriterIndex.Terminal
    (fun _ => Value) (primitiveSerializeRun encoder)

def primitiveSerializeFn {State Value Unwind Terminal : Type} (encoder : Encoder Value)
    (writer : WriterFn State Unwind Terminal) : SerializeFn State Value Unwind Terminal :=
  Encoder.serializeFn encoder writer

theorem primitiveSerializeRun_ofFunction {State Value Unwind Terminal : Type}
    (encoder : Encoder Value) (writer : WriterFn State Unwind Terminal) (before : State)
    (value : Value) (outcome : Outcome State (Except IoError Unit) Unwind Terminal) :
    primitiveSerializeRun encoder ⟨State, Unwind, Terminal, Callback.ofFunction writer⟩
        before value outcome ↔
      primitiveSerializeFn encoder writer before value = outcome := by
  have handler : writeHandler (Value := Empty) (Callback.ofFunction writer) noElement =
      writeHandler (Callback.ofFunction writer)
        (Callback.ofFunction (fun (_ : State) (value : Empty) => nomatch value)) := by
    funext r
    cases r with
    | writeAll => rfl
    | element value => exact nomatch value
  unfold primitiveSerializeRun
  rw [handler]
  exact write_runs_ofFunction_iff writer _ _ before outcome

/-! ### `Option<T>` serialization -/

def optionSerializeRun (index : OptionSerializeIndex) :
    index.State → Option index.Value →
      Outcome index.State (Except IoError Unit) index.Unwind index.Terminal → Prop :=
  fun before value outcome =>
    (optionSerializeProgram value).Runs (writeHandler index.writer index.serialize) before outcome

def optionSerializeFamily : Family :=
  serializeFamily OptionSerializeIndex OptionSerializeIndex.State OptionSerializeIndex.Unwind
    OptionSerializeIndex.Terminal (fun index => Option index.Value) optionSerializeRun

def optionSerializeFn {State Value Unwind Terminal : Type}
    (writer : WriterFn State Unwind Terminal) (serialize : SerializeFn State Value Unwind Terminal)
      :
    SerializeFn State (Option Value) Unwind Terminal :=
  fun before value => (optionSerializeProgram value).run (writeHandlerFn writer serialize) before

theorem optionSerializeRun_ofFunction {State Value Unwind Terminal : Type}
    (writer : WriterFn State Unwind Terminal) (serialize : SerializeFn State Value Unwind Terminal)
    (before : State) (value : Option Value)
    (outcome : Outcome State (Except IoError Unit) Unwind Terminal) :
    optionSerializeRun
        ⟨State, Unwind, Terminal, Callback.ofFunction writer, Value, Callback.ofFunction serialize⟩
        before value outcome ↔
      optionSerializeFn writer serialize before value = outcome :=
  write_runs_ofFunction_iff writer serialize _ before outcome

/-! ### `[T; N]` serialization -/

def arraySerializeRun : (index : ArraySerializeIndex) →
    index.State → FixedArray index.element.Value index.length →
      Outcome index.State (Except IoError Unit) index.Unwind index.Terminal → Prop
  | ⟨_, _, _, writer, length, .byte⟩ => fun before bytes outcome =>
    (byteArraySerializeProgram (α := Empty) length bytes).Runs (writeHandler writer noElement)
      before outcome
  | ⟨_, _, _, writer, length, .other _ serialize⟩ => fun before values outcome =>
    (arraySerializeProgram length values).Runs (writeHandler writer serialize) before outcome

def arraySerializeFamily : Family :=
  serializeFamily ArraySerializeIndex ArraySerializeIndex.State ArraySerializeIndex.Unwind
    ArraySerializeIndex.Terminal (fun index => FixedArray index.element.Value index.length)
    arraySerializeRun

def byteArraySerializeFn {State Unwind Terminal : Type} (length : Nat)
    (writer : WriterFn State Unwind Terminal) :
    SerializeFn State (FixedArray UInt8 length) Unwind Terminal :=
  fun before bytes =>
    (byteArraySerializeProgram (α := Empty) length bytes).run
      (writeHandlerFn writer (fun _ value => nomatch value)) before

def arraySerializeFn {State Value Unwind Terminal : Type} (length : Nat)
    (writer : WriterFn State Unwind Terminal) (serialize : SerializeFn State Value Unwind Terminal)
      :
    SerializeFn State (FixedArray Value length) Unwind Terminal :=
  fun before values => (arraySerializeProgram length values).run (writeHandlerFn writer serialize)
    before

theorem arraySerializeRun_byte {State Unwind Terminal : Type} (length : Nat)
    (writer : WriterFn State Unwind Terminal) (before : State) (bytes : FixedArray UInt8 length)
    (outcome : Outcome State (Except IoError Unit) Unwind Terminal) :
    arraySerializeRun ⟨State, Unwind, Terminal, Callback.ofFunction writer, length, .byte⟩
        before bytes outcome ↔
      byteArraySerializeFn length writer before bytes = outcome := by
  have handler : writeHandler (Value := Empty) (Callback.ofFunction writer) noElement =
      writeHandler (Callback.ofFunction writer)
        (Callback.ofFunction (fun (_ : State) (value : Empty) => nomatch value)) := by
    funext r
    cases r with
    | writeAll => rfl
    | element value => exact nomatch value
  show (byteArraySerializeProgram (α := Empty) length bytes).Runs
    (writeHandler (Callback.ofFunction writer) noElement) before outcome ↔ _
  rw [handler]
  exact write_runs_ofFunction_iff writer _ _ before outcome

theorem arraySerializeRun_ofFunction {State Value Unwind Terminal : Type} (length : Nat)
    (writer : WriterFn State Unwind Terminal) (serialize : SerializeFn State Value Unwind Terminal)
    (before : State) (values : FixedArray Value length)
    (outcome : Outcome State (Except IoError Unit) Unwind Terminal) :
    arraySerializeRun ⟨State, Unwind, Terminal, Callback.ofFunction writer, length,
        .other Value (Callback.ofFunction serialize)⟩ before values outcome ↔
      arraySerializeFn length writer serialize before values = outcome :=
  write_runs_ofFunction_iff writer serialize _ before outcome

/-! ## Hidden trait methods and helpers -/

/-- A const-generic length `N`. -/
structure LengthIndex : Type 1 where
  length : Nat

/-- `u8::array_from_reader::<&[u8], N>`: one `read_exact` of `N` bytes, `Some`
on success. -/
def byteArrayFromReader (profile : Profile) (length : Nat) :
    Decoder (Option (FixedArray UInt8 length)) :=
  (decodeByteArray profile length).map some

def byteArrayFromReaderRun (profile : Profile) (index : LengthIndex) :
    Unit → Solanalib.Runtime.Bytes →
      Outcome Unit (Except IoError (Option (FixedArray UInt8 index.length)) ×
        Solanalib.Runtime.Bytes)
        Empty Empty → Prop :=
  fun before input outcome =>
    outcome = .returned (byteArrayFromReader profile index.length input) before

def byteArrayFromReaderFamily (profile : Profile) : Family :=
  decodeFamily LengthIndex (fun _ => Unit) (fun _ => Empty) (fun _ => Empty)
    (fun index => Option (FixedArray UInt8 index.length)) (byteArrayFromReaderRun profile)

/-- The source type `Self` of a trait default method. -/
structure SelfIndex : Type 1 where
  Value : Type

/-- Default `vec_from_reader`: `Ok(None)` without reading. -/
def vecFromReaderDefaultRun (index : SelfIndex) :
    Unit → UInt32 × Solanalib.Runtime.Bytes →
      Outcome Unit (Except IoError (Option (List index.Value)) × Solanalib.Runtime.Bytes) Empty
        Empty →
        Prop :=
  fun before args outcome => outcome = .returned (.ok none, args.2) before

/-- The arguments are `len` and the current slice; the result carries the
remaining slice. The default reads nothing. -/
def vecFromReaderDefaultFamily : Family where
  Index := SelfIndex
  State := fun _ => Unit
  Args := fun _ => UInt32 × Solanalib.Runtime.Bytes
  Value := fun index => Except IoError (Option (List index.Value)) × Solanalib.Runtime.Bytes
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before args outcome => vecFromReaderDefaultRun index before args outcome }

theorem vecFromReaderDefault_reference :
    FamilyReference vecFromReaderDefaultFamily vecFromReaderDefaultRun :=
  fun _ _ _ _ _ step => step

/-- `T` for `hint::cautious::<T>`, by `size_of::<T>()`, and the division-by-zero panic policy of the
source. -/
structure SizeIndex : Type 1 where
  State : Type
  Unwind : Type
  Terminal : Type
  size : Nat
  panic : Callback.Run State Unit Empty Unwind Terminal

def cautiousRun (index : SizeIndex) :
    index.State → UInt32 → Outcome index.State Nat index.Unwind index.Terminal → Prop :=
  fun before hint outcome =>
    match cautious index.size hint.toNat with
    | some capacity => outcome = .returned capacity before
    | none => Callback.map Empty.elim index.panic before () outcome

/-- `max(min(hint, 4096 / (size_of::<T>() as u32)), 1)`, including the
division-by-zero panic at every size congruent to zero modulo `2^32`.
No size bound or nonzero-size premise excludes that behavior. -/
def cautiousFamily : Family where
  Index := SizeIndex
  State := SizeIndex.State
  Args := fun _ => UInt32
  Value := fun _ => Nat
  Unwind := SizeIndex.Unwind
  Terminal := SizeIndex.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before hint outcome => cautiousRun index before hint outcome }

theorem cautious_reference : FamilyReference cautiousFamily cautiousRun :=
  fun _ _ _ _ _ step => step

def cautiousFn {State Unwind Terminal : Type} (size : Nat)
    (panic : State → Unit → Outcome State Empty Unwind Terminal)
    (before : State) (hint : UInt32) : Outcome State Nat Unwind Terminal :=
  match cautious size hint.toNat with
  | some capacity => .returned capacity before
  | none => Outcome.map Empty.elim (panic before ())

theorem cautiousRun_ofFunction {State Unwind Terminal : Type} (size : Nat)
    (panic : State → Unit → Outcome State Empty Unwind Terminal)
    (before : State) (hint : UInt32) (outcome : Outcome State Nat Unwind Terminal) :
    cautiousRun ⟨State, Unwind, Terminal, size, Callback.ofFunction panic⟩ before hint outcome ↔
      cautiousFn size panic before hint = outcome := by
  unfold cautiousRun cautiousFn
  cases cautious size hint.toNat with
  | some capacity => exact eq_comm
  | none => exact Callback.map_ofFunction Empty.elim panic before () outcome

/-- `<u8 as BorshSerialize>::u8_slice`: `Some(slice)`. -/
def u8SliceContract :
    Solanalib.Contracts.Model Unit Solanalib.Runtime.Bytes (Option Solanalib.Runtime.Bytes) :=
  .returning (fun _ _ => True)
    (fun before slice result after => result = some slice ∧ after = before)

def u8SliceModel (before : Unit) (slice : Solanalib.Runtime.Bytes) : Option Solanalib.Runtime.Bytes
  × Unit :=
  (some slice, before)

theorem u8Slice_realized : u8SliceContract.RealizedBy u8SliceModel :=
  fun _ _ _ => ⟨rfl, rfl⟩

end Solanalib.Specs.Core.Borsh
