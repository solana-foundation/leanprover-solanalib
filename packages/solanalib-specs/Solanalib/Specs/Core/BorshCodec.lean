/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorshWire
public import Solanalib.Specs.Core.BorshProgram

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Generic borsh members as request programs.

`Option<T>`, `[T; N]`, `Vec<T>`, `deserialize` and `try_from_slice` call the
trait implementation of `T` (or `Self`). Each is a `Program` over element
requests, `write_all` requests and `Vec` allocation calls. A family reference
runs the program with relational callbacks (`Program.Runs`); the executable
combinator runs it with function callbacks (`Program.run`); a pure combinator
evaluates it with total, state-free responses (`Program.eval`). -/

namespace Solanalib.Specs.Core.Borsh

/-! ## Decoding requests -/

/-- `Vec` calls made by the borsh source while decoding. The provider owns
their allocation, capacity and failure semantics; on Solana an allocation
failure aborts. Deallocation and destructors on error paths are not reported. -/
inductive VecCall where
  /-- `Vec::with_capacity(hint::cautious::<T>(len))`. -/
  | withCapacity (capacity : Nat)
  /-- `result.push(..)` onto a vector holding `length` elements. -/
  | push (length : Nat)
  /-- `vec![0u8; len.min(1024 * 1024)]` in `u8::vec_from_reader`. -/
  | zeroed (length : Nat)
  /-- `vec.resize(new_len, 0)` in `u8::vec_from_reader`. -/
  | resize (length : Nat)
  deriving DecidableEq, Repr

inductive DecodeRequest where
  /-- One call of the decoder for the element (or for `Self`) on the current slice. -/
  | element (input : Solanalib.Runtime.Bytes)
  | allocate (call : VecCall)
  deriving DecidableEq, Repr

@[reducible] def DecodeRequest.Response (α : Type) : DecodeRequest → Type
  | .element _ => Except IoError α × Solanalib.Runtime.Bytes
  | .allocate _ => Unit

abbrev DecodeProgram (α β : Type) := Program DecodeRequest (DecodeRequest.Response α) β

/-- `<T as BorshDeserialize>::deserialize_reader::<&[u8]>` (or `T::deserialize`)
as a callback: current slice to result and remaining slice. -/
abbrev Decode (State Value Unwind Terminal : Type) :=
  Callback.Run State Solanalib.Runtime.Bytes (Except IoError Value × Solanalib.Runtime.Bytes)
    Unwind Terminal

abbrev DecodeFn (State Value Unwind Terminal : Type) :=
  State → Solanalib.Runtime.Bytes → Outcome State (Except IoError Value × Solanalib.Runtime.Bytes)
    Unwind Terminal

/-- A provider for the `Vec` calls of a decoder. -/
abbrev Allocate (State Unwind Terminal : Type) := Callback.Run State VecCall Unit Unwind Terminal

abbrev AllocateFn (State Unwind Terminal : Type) :=
  State → VecCall → Outcome State Unit Unwind Terminal

/-- A pure decoder as a callback that keeps the state. -/
def Decoder.lift {State Value Unwind Terminal : Type} (decoder : Decoder Value) :
    DecodeFn State Value Unwind Terminal :=
  fun before input => .returned (decoder input) before

/-- The allocation provider that always returns and keeps the state. -/
def allocateReturns {State Unwind Terminal : Type} : AllocateFn State Unwind Terminal :=
  fun before _ => .returned () before

def decodeHandler {State Value Unwind Terminal : Type}
    (decode : Decode State Value Unwind Terminal) (allocate : Allocate State Unwind Terminal) :
    (r : DecodeRequest) → State →
      Outcome State (r.Response Value) Unwind Terminal → Prop
  | .element input => fun before outcome => decode before input outcome
  | .allocate call => fun before outcome => allocate before call outcome

def decodeHandlerFn {State Value Unwind Terminal : Type}
    (decode : DecodeFn State Value Unwind Terminal) (allocate : AllocateFn State Unwind Terminal) :
    (r : DecodeRequest) → State → Outcome State (r.Response Value) Unwind Terminal
  | .element input => fun before => decode before input
  | .allocate call => fun before => allocate before call

def decodeRespond {Value : Type} (decoder : Decoder Value) :
    (r : DecodeRequest) → r.Response Value
  | .element input => decoder input
  | .allocate _ => ()

theorem decodeHandler_ofFunction {State Value Unwind Terminal : Type}
    (decode : DecodeFn State Value Unwind Terminal) (allocate : AllocateFn State Unwind Terminal) :
    decodeHandler (Callback.ofFunction decode) (Callback.ofFunction allocate) =
      fun r before outcome => decodeHandlerFn decode allocate r before = outcome := by
  funext r
  cases r <;> rfl

/-- A decoding program at function-graph callbacks is the graph of its
executable interpretation. -/
theorem decode_runs_ofFunction_iff {State Value Unwind Terminal β : Type}
    (decode : DecodeFn State Value Unwind Terminal) (allocate : AllocateFn State Unwind Terminal)
    (program : DecodeProgram Value β) (before : State)
    (outcome : Outcome State β Unwind Terminal) :
    program.Runs (decodeHandler (Callback.ofFunction decode) (Callback.ofFunction allocate))
        before outcome ↔
      program.run (decodeHandlerFn decode allocate) before = outcome := by
  rw [decodeHandler_ofFunction]
  exact Program.runs_ofFunction_iff _ program before outcome

/-! ## Decoding programs -/

/-- Issue the given `Vec` calls in order, then return. -/
def allocateAll {α β : Type} : List VecCall → β → DecodeProgram α β
  | [], result => .pure result
  | call :: calls, result => .call (.allocate call) fun _ => allocateAll calls result

/-- `Option<T>`: flag byte, then `T` only for flag `1`. -/
def optionProgram {α : Type} (profile : Profile) (input : Solanalib.Runtime.Bytes) :
    DecodeProgram α (Except IoError (Option α) × Solanalib.Runtime.Bytes) :=
  match decodeU8 profile input with
  | (.error error, remaining) => .pure (.error error, remaining)
  | (.ok tag, remaining) =>
    if tag = 0 then .pure (.ok none, remaining)
    else if tag = 1 then
      .call (.element remaining) fun (response : Except IoError α × Solanalib.Runtime.Bytes) =>
        .pure (response.1.map some, response.2)
    else .pure (.error (profile.invalidOption tag), remaining)

/-- `[T; N]` without the `u8` override: `N` element calls in order; the first
error returns at once. -/
def arrayProgram {α : Type} : (n : Nat) → Solanalib.Runtime.Bytes →
    DecodeProgram α (Except IoError (FixedArray α n) × Solanalib.Runtime.Bytes)
  | 0, input => .pure (.ok ⟨[], rfl⟩, input)
  | n + 1, input =>
    .call (.element input) fun (response : Except IoError α × Solanalib.Runtime.Bytes) =>
      match response with
      | (.error error, remaining) => .pure (.error error, remaining)
      | (.ok head, remaining) => (arrayProgram n remaining).bind fun tail =>
          .pure (tail.1.map (FixedArray.cons head), tail.2)

/-- The Rust expression `size_of::<T>() as u32`, including truncation on a 64-bit target. -/
def cautiousDivisor (size : Nat) : Nat := size % 2^32

/-- The arithmetic of `hint::cautious::<T>(len)`. `none` requests the
division-by-zero panic; the panic callback of the family determines its exit.
Rust evaluates the division even when `hint = 0`. -/
def cautious (size hint : Nat) : Option Nat :=
  if cautiousDivisor size = 0 then none
  else some (max (min hint (4096 / cautiousDivisor size)) 1)

/-- The element loop of the generic `Vec<T>` path: decode, then `push`. -/
def vecElements {α : Type} : (count pushed : Nat) → Solanalib.Runtime.Bytes →
    DecodeProgram α (Except IoError (List α) × Solanalib.Runtime.Bytes)
  | 0, _, input => .pure (.ok [], input)
  | count + 1, pushed, input =>
    .call (.element input) fun (response : Except IoError α × Solanalib.Runtime.Bytes) =>
      match response with
      | (.error error, remaining) => .pure (.error error, remaining)
      | (.ok head, remaining) =>
        .call (.allocate (.push pushed)) fun _ =>
          (vecElements count (pushed + 1) remaining).bind fun tail =>
            .pure (tail.1.map (head :: ·), tail.2)

/-- The prefix of the generic vector either selects a request program or panics
after reading the length. The latter retains the remaining slice for the
panic callback; no allocation or element request has occurred. -/
inductive VecProgram (α : Type) where
  | ready (program : DecodeProgram α (Except IoError (List α) × Solanalib.Runtime.Bytes))
  | divideByZero (remaining : Solanalib.Runtime.Bytes)

/-- `Vec<T>` for an element implementation without the `u8` override, where
`size = size_of::<T>()`. A zero-sized `T` is rejected before any read. An
empty vector returns before the cautious hint is evaluated. -/
def vecProgram {α : Type} (profile : Profile) (size : Nat) (input : Solanalib.Runtime.Bytes) :
    VecProgram α :=
  if size = 0 then .ready (.pure (.error profile.zeroSized, input)) else
  match decodeU32 profile input with
  | (.error error, remaining) => .ready (.pure (.error error, remaining))
  | (.ok len, remaining) =>
    if len.toNat = 0 then .ready (.pure (.ok [], remaining)) else
    match cautious size len.toNat with
    | none => .divideByZero remaining
    | some capacity => .ready (.call (.allocate (.withCapacity capacity)) fun _ =>
        vecElements len.toNat 0 remaining)

/-- Sizes for which the generic vector never reaches its own division panic.
This is a domain of the pure/returning adapters, not of the vector family. -/
def VecNoDivisionByZero (size : Nat) : Prop := size = 0 ∨ cautiousDivisor size ≠ 0

theorem vecProgram_not_divideByZero {α : Type} (profile : Profile) (size : Nat)
    (safe : VecNoDivisionByZero size) (input remaining : Solanalib.Runtime.Bytes) :
    vecProgram (α := α) profile size input ≠ .divideByZero remaining := by
  by_cases zero : size = 0
  · simp [vecProgram, zero]
  · have divisor : cautiousDivisor size ≠ 0 := safe.resolve_left zero
    cases decoded : decodeU32 profile input with
    | mk result rest =>
      cases result with
      | error error => simp [vecProgram, zero, decoded]
      | ok len =>
        by_cases empty : len.toNat = 0
        · simp [vecProgram, zero, decoded, empty]
        · simp [vecProgram, zero, decoded, empty, cautious, divisor]

/-- A request program for the returning adapter, obtained from the full
prefix using a proof that its division panic is unreachable. -/
def vecProgramNormal {α : Type} (profile : Profile) (size : Nat)
    (safe : VecNoDivisionByZero size) (input : Solanalib.Runtime.Bytes) :
    DecodeProgram α (Except IoError (List α) × Solanalib.Runtime.Bytes) :=
  match h : vecProgram profile size input with
  | .ready program => program
  | .divideByZero remaining => False.elim (vecProgram_not_divideByZero profile size safe input
    remaining h)

theorem vecProgram_eq_ready {α : Type} (profile : Profile) (size : Nat)
    (safe : VecNoDivisionByZero size) (input : Solanalib.Runtime.Bytes) :
    vecProgram (α := α) profile size input = .ready (vecProgramNormal profile size safe input) := by
  unfold vecProgramNormal
  split
  · assumption
  · rename_i remaining h
    exact False.elim (vecProgram_not_divideByZero profile size safe input remaining h)

/-- Interpret the prefix and its subsequent requests. The panic callback
receives the slice after the length read and has no ordinary return value. -/
def VecProgram.Runs {State Value Unwind Terminal : Type}
    (decode : Decode State Value Unwind Terminal) (allocate : Allocate State Unwind Terminal)
    (panic : Callback.Run State Solanalib.Runtime.Bytes Empty Unwind Terminal) :
    VecProgram Value → State →
      Outcome State (Except IoError (List Value) × Solanalib.Runtime.Bytes) Unwind Terminal → Prop
  | .ready program, before, outcome =>
      program.Runs (decodeHandler decode allocate) before outcome
  | .divideByZero remaining, before, outcome =>
      Callback.map Empty.elim panic before remaining outcome

def VecProgram.run {State Value Unwind Terminal : Type}
    (decode : DecodeFn State Value Unwind Terminal) (allocate : AllocateFn State Unwind Terminal)
    (panic : State → Solanalib.Runtime.Bytes → Outcome State Empty Unwind Terminal) :
    VecProgram Value → State →
      Outcome State (Except IoError (List Value) × Solanalib.Runtime.Bytes) Unwind Terminal
  | .ready program, before => program.run (decodeHandlerFn decode allocate) before
  | .divideByZero remaining, before => Outcome.map Empty.elim (panic before remaining)

theorem VecProgram.runs_ofFunction_iff {State Value Unwind Terminal : Type}
    (decode : DecodeFn State Value Unwind Terminal) (allocate : AllocateFn State Unwind Terminal)
    (panic : State → Solanalib.Runtime.Bytes → Outcome State Empty Unwind Terminal)
    (program : VecProgram Value) (before : State)
    (outcome : Outcome State (Except IoError (List Value) × Solanalib.Runtime.Bytes) Unwind
      Terminal) :
    program.Runs (Callback.ofFunction decode) (Callback.ofFunction allocate)
        (Callback.ofFunction panic) before outcome ↔
      program.run decode allocate panic before = outcome := by
  cases program with
  | ready program => exact decode_runs_ofFunction_iff decode allocate program before outcome
  | divideByZero remaining =>
    exact Callback.map_ofFunction Empty.elim panic before remaining outcome

/-- Initial buffer bound of `u8::vec_from_reader`. -/
def byteVecInitialLimit : Nat := 1024 * 1024

/-- The `resize` targets of `u8::vec_from_reader` on a slice with `available`
bytes. A resize happens whenever the buffer is full and more bytes are due.
Each step strictly grows the buffer towards `len`, so `fuel = len` suffices. -/
def byteVecResizes (len available : Nat) : (fuel capacity : Nat) → List Nat
  | 0, _ => []
  | fuel + 1, capacity =>
    if capacity < len ∧ capacity ≤ available then
      let next := min (capacity * 2) len
      next :: byteVecResizes len available fuel next
    else []

/-- The `Vec` calls of `u8::vec_from_reader` for `len > 0`. -/
def byteVecCalls (len available : Nat) : List VecCall :=
  let first := min len byteVecInitialLimit
  .zeroed first :: (byteVecResizes len available len first).map .resize

/-- The result of `u8::vec_from_reader`: repeated `read` calls consume the
whole slice before a zero-length read reports the short input. -/
def byteVecResult (profile : Profile) (len : Nat) (input : Solanalib.Runtime.Bytes) :
    Except IoError (List UInt8) × Solanalib.Runtime.Bytes :=
  if len ≤ input.length then (.ok (input.take len), input.drop len)
  else (.error profile.unexpectedLength, [])

/-- `Vec<u8>`: length, then `u8::vec_from_reader`. -/
def byteVecProgram {α : Type} (profile : Profile) (input : Solanalib.Runtime.Bytes) :
    DecodeProgram α (Except IoError (List UInt8) × Solanalib.Runtime.Bytes) :=
  match decodeU32 profile input with
  | (.error error, remaining) => .pure (.error error, remaining)
  | (.ok len, remaining) =>
    if len.toNat = 0 then .pure (.ok [], remaining)
    else allocateAll (byteVecCalls len.toNat remaining.length)
      (byteVecResult profile len.toNat remaining)

/-- Default `BorshDeserialize::deserialize`: `Self::deserialize_reader(&mut *buf)`. -/
def deserializeProgram {α : Type} (input : Solanalib.Runtime.Bytes) :
    DecodeProgram α (Except IoError α × Solanalib.Runtime.Bytes) :=
  .call (.element input) fun (response : Except IoError α × Solanalib.Runtime.Bytes) => .pure
    response

/-- Default `BorshDeserialize::try_from_slice`: `Self::deserialize`, then reject
leftover bytes. -/
def tryFromSliceProgram {α : Type} (input : Solanalib.Runtime.Bytes) : DecodeProgram α (Except
  IoError α) :=
  .call (.element input) fun (response : Except IoError α × Solanalib.Runtime.Bytes) =>
    match response with
    | (.error error, _) => .pure (.error error)
    | (.ok value, []) => .pure (.ok value)
    | (.ok _, _ :: _) => .pure (.error notAllBytesRead)

/-! ## Pure decoding combinators -/

def decodeOption {α : Type} (profile : Profile) (element : Decoder α) : Decoder (Option α) :=
  fun input => (optionProgram profile input).eval (decodeRespond element)

def decodeArray {α : Type} (n : Nat) (element : Decoder α) : Decoder (FixedArray α n) :=
  fun input => (arrayProgram n input).eval (decodeRespond element)

def decodeVec {α : Type} (profile : Profile) (size : Nat) (safe : VecNoDivisionByZero size)
    (element : Decoder α) :
    Decoder (List α) :=
  fun input => (vecProgramNormal profile size safe input).eval (decodeRespond element)

def decodeByteVec (profile : Profile) : Decoder (List UInt8) :=
  fun input => (byteVecProgram (α := UInt8) profile input).eval (decodeRespond (decodeU8 profile))

def tryFromSlice {α : Type} (decoder : Decoder α) (input : Solanalib.Runtime.Bytes) : Except
  IoError α :=
  (tryFromSliceProgram input).eval (decodeRespond decoder)

/-! ## Element implementations in family indices -/

/-- The implementation of `T: BorshDeserialize` seen by `[T; N]` and `Vec<T>`:
`u8`, which overrides `array_from_reader` and `vec_from_reader`, or an
implementation that keeps their defaults (`Ok(None)`), with
`size = size_of::<T>()`. -/
inductive DecodeElement (State Unwind Terminal : Type) : Type 1 where
  | byte
  | other (Value : Type) (size : Nat) (decode : Decode State Value Unwind Terminal)

def DecodeElement.Value {State Unwind Terminal : Type} :
    DecodeElement State Unwind Terminal → Type
  | .byte => UInt8
  | .other Value _ _ => Value

/-- The implementation of `T: BorshSerialize` seen by `[T; N]`: `u8`, whose
`u8_slice` returns the bytes, or one that keeps the default (`None`). -/
inductive SerializeElement (State Unwind Terminal : Type) : Type 1 where
  | byte
  | other (Value : Type) (serialize : Callback.Run State Value (Except IoError Unit) Unwind
    Terminal)

def SerializeElement.Value {State Unwind Terminal : Type} :
    SerializeElement State Unwind Terminal → Type
  | .byte => UInt8
  | .other Value _ => Value

/-! ## Serialization requests -/

inductive WriteRequest (α : Type) where
  /-- One `Write::write_all` call of the writer `W`. -/
  | writeAll (chunk : Solanalib.Runtime.Bytes)
  /-- One `<T as BorshSerialize>::serialize::<W>` call on an element. -/
  | element (value : α)

abbrev WriteProgram (α : Type) :=
  Program (WriteRequest α) (fun _ => Except IoError Unit) (Except IoError Unit)

/-- `W::write_all` as a callback. Its errors, partial effects, unwind state and
terminal reason remain those of the writer. -/
abbrev Writer (State Unwind Terminal : Type) :=
  Callback.Run State Solanalib.Runtime.Bytes (Except IoError Unit) Unwind Terminal

abbrev WriterFn (State Unwind Terminal : Type) :=
  State → Solanalib.Runtime.Bytes → Outcome State (Except IoError Unit) Unwind Terminal

abbrev Serialize (State Value Unwind Terminal : Type) :=
  Callback.Run State Value (Except IoError Unit) Unwind Terminal

abbrev SerializeFn (State Value Unwind Terminal : Type) :=
  State → Value → Outcome State (Except IoError Unit) Unwind Terminal

def writeHandler {State Value Unwind Terminal : Type}
    (writer : Writer State Unwind Terminal) (serialize : Serialize State Value Unwind Terminal) :
    (r : WriteRequest Value) → State → Outcome State (Except IoError Unit) Unwind Terminal → Prop
  | .writeAll chunk => fun before outcome => writer before chunk outcome
  | .element value => fun before outcome => serialize before value outcome

def writeHandlerFn {State Value Unwind Terminal : Type}
    (writer : WriterFn State Unwind Terminal) (serialize : SerializeFn State Value Unwind Terminal)
      :
    (r : WriteRequest Value) → State → Outcome State (Except IoError Unit) Unwind Terminal
  | .writeAll chunk => fun before => writer before chunk
  | .element value => fun before => serialize before value

/-- A serialization callback for programs without element requests. -/
def noElement {State Value Unwind Terminal : Type} : Serialize State Value Unwind Terminal :=
  fun _ _ _ => False

theorem writeHandler_ofFunction {State Value Unwind Terminal : Type}
    (writer : WriterFn State Unwind Terminal) (serialize : SerializeFn State Value Unwind Terminal)
      :
    writeHandler (Callback.ofFunction writer) (Callback.ofFunction serialize) =
      fun r before outcome => writeHandlerFn writer serialize r before = outcome := by
  funext r
  cases r <;> rfl

theorem write_runs_ofFunction_iff {State Value Unwind Terminal : Type}
    (writer : WriterFn State Unwind Terminal) (serialize : SerializeFn State Value Unwind Terminal)
    (program : WriteProgram Value) (before : State)
    (outcome : Outcome State (Except IoError Unit) Unwind Terminal) :
    program.Runs (writeHandler (Callback.ofFunction writer) (Callback.ofFunction serialize))
        before outcome ↔
      program.run (writeHandlerFn writer serialize) before = outcome := by
  rw [writeHandler_ofFunction]
  exact Program.runs_ofFunction_iff _ program before outcome

/-! ## Serialization programs -/

/-- Continue after `?`: stop at the first error. -/
def WriteProgram.andThen {α : Type} (first next : WriteProgram α) : WriteProgram α :=
  first.bind fun result =>
    match result with
    | .error error => .pure (.error error)
    | .ok () => next

/-- Sequential `write_all` calls, stopping at the first error. -/
def writeChunks {α : Type} : List Solanalib.Runtime.Bytes → WriteProgram α
  | [] => .pure (.ok ())
  | chunk :: chunks => .call (.writeAll chunk) fun result =>
      match result with
      | .error error => .pure (.error error)
      | .ok () => writeChunks chunks

/-- The `write_all` chunks issued with a writer that never fails, and the
borsh error, if any, that follows them. -/
structure WritePlan where
  chunks : List Solanalib.Runtime.Bytes
  failure : Option IoError
  deriving DecidableEq, Repr

/-- The plan of a pure encoder. -/
def WritePlan.ofEncoded (encoded : Except IoError (List Solanalib.Runtime.Bytes)) : WritePlan :=
  match encoded with
  | .error error => ⟨[], some error⟩
  | .ok chunks => ⟨chunks, none⟩

/-- Its interpretation: the chunks in order, then the borsh error. -/
def WritePlan.program {α : Type} (plan : WritePlan) : WriteProgram α :=
  WriteProgram.andThen (writeChunks plan.chunks)
    (match plan.failure with
     | some error => .pure (.error error)
     | none => .pure (.ok ()))

/-- A primitive serializer: its pure encoder as a write program. -/
def encodeProgram {α β : Type} (encoder : Encoder β) (value : β) : WriteProgram α :=
  (WritePlan.ofEncoded (encoder value)).program

/-- `Option<T>`: `0u8.serialize` for `None`; `1u8.serialize` then `T::serialize`. -/
def optionSerializeProgram {α : Type} : Option α → WriteProgram α
  | none => writeChunks [[0]]
  | some value => WriteProgram.andThen (writeChunks [[1]]) (.call (.element value) .pure)

/-- Element-wise serialization, stopping at the first error. -/
def elementsSerializeProgram {α : Type} : List α → WriteProgram α
  | [] => .pure (.ok ())
  | value :: values => WriteProgram.andThen (.call (.element value) .pure)
      (elementsSerializeProgram values)

/-- `[T; N]` (borsh 1.x): nothing for `N = 0`; one `write_all` of all bytes
for `u8`; otherwise each element in order. -/
def byteArraySerializeProgram {α : Type} (n : Nat) (bytes : FixedArray UInt8 n) : WriteProgram α :=
  if n = 0 then .pure (.ok ()) else writeChunks [bytes.val]

def arraySerializeProgram {α : Type} (n : Nat) (values : FixedArray α n) : WriteProgram α :=
  if n = 0 then .pure (.ok ()) else elementsSerializeProgram values.val

/-- The plan of a write program whose writes succeed, given the plan of each element. -/
def WriteProgram.plan {α : Type} (elementPlan : α → WritePlan) : WriteProgram α → WritePlan
  | .pure (.ok ()) => ⟨[], none⟩
  | .pure (.error error) => ⟨[], some error⟩
  | .call (.writeAll chunk) next =>
    let rest := WriteProgram.plan elementPlan (next (.ok ()))
    ⟨chunk :: rest.chunks, rest.failure⟩
  | .call (.element value) next =>
    let first := elementPlan value
    let rest := WriteProgram.plan elementPlan
      (next (match first.failure with | some error => .error error | none => .ok ()))
    ⟨first.chunks ++ rest.chunks, rest.failure⟩

/-! ## Pure encoding combinators -/

/-- A pure element encoder as a plan. -/
def Encoder.plan {α : Type} (encoder : Encoder α) (value : α) : WritePlan :=
  WritePlan.ofEncoded (encoder value)

def encodeOptionPlan {α : Type} (element : α → WritePlan) (value : Option α) : WritePlan :=
  (optionSerializeProgram value).plan element

def encodeArrayPlan {α : Type} (n : Nat) (element : α → WritePlan) (values : FixedArray α n) :
    WritePlan :=
  (arraySerializeProgram n values).plan element

def encodeByteArrayPlan (n : Nat) (bytes : FixedArray UInt8 n) : WritePlan :=
  (byteArraySerializeProgram (α := UInt8) n bytes).plan (Encoder.plan encodeU8)

/-- A pure encoder as a serialization callback over any writer: its program
with only `write_all` requests. -/
def Encoder.serializeFn {State Value Unwind Terminal : Type} (encoder : Encoder Value)
    (writer : WriterFn State Unwind Terminal) : SerializeFn State Value Unwind Terminal :=
  fun before value =>
    (encodeProgram (α := Empty) encoder value).run
      (writeHandlerFn writer (fun _ value => nomatch value)) before

def Encoder.serialize {State Value Unwind Terminal : Type} (encoder : Encoder Value)
    (writer : Writer State Unwind Terminal) : Serialize State Value Unwind Terminal :=
  fun before value outcome =>
    (encodeProgram (α := Empty) encoder value).Runs (writeHandler writer noElement) before outcome

/-- A recording writer for controls: appends each chunk and never fails. -/
def recordingWriter {Unwind Terminal : Type} : WriterFn (List Solanalib.Runtime.Bytes) Unwind
  Terminal :=
  fun log chunk => .returned (.ok ()) (log ++ [chunk])

end Solanalib.Specs.Core.Borsh
