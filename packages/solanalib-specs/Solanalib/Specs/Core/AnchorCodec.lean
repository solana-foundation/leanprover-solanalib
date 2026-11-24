/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorshWriteAll
public import Solanalib.Specs.Core.OwnedFocus

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorCodec

/-- The actual mutable slice reference is an argument of the generic default
method. Its current cursor and every other effect belong to State; even an
unwind may change them. No discriminator predicate is invented by the default. -/
structure DeserializeTypes where
  State : Type
  SliceRef : Type
  Value : Type
  Error : Type
  Unwind : Type
  Terminal : Type
  unchecked : Callback.Run State SliceRef (Except Error Value) Unwind Terminal

/-- The provided `AccountDeserialize::try_deserialize` method forwards the
one unchecked call, including its exact result, state, unwind and termination.
The source binding must select this default, not an implementation override. -/
def deserializeFamily : Family where
  Index := DeserializeTypes
  State := DeserializeTypes.State
  Args := DeserializeTypes.SliceRef
  Value := fun types => Except types.Error types.Value
  Unwind := DeserializeTypes.Unwind
  Terminal := DeserializeTypes.Terminal
  contract := fun types => { requires := fun _ _ => True, post := types.unchecked }

def deserializeRun : FamilyRun deserializeFamily := DeserializeTypes.unchecked

theorem deserialize_reference : FamilyReference deserializeFamily deserializeRun :=
  fun _ _ _ _ _ run => run

/-- A failed unchecked call may consume bytes. This closed sample deliberately
does so, ruling out a success-only or unchanged-cursor default interpretation. -/
abbrev deserializeSample : DeserializeTypes where
  State := Solanalib.Runtime.Bytes
  SliceRef := Unit
  Value := Nat
  Error := String
  Unwind := Nat
  Terminal := Nat
  unchecked := fun before _ outcome => outcome = .returned (.error "codec rejected") (before.drop 1)

theorem deserialize_execution : FamilyHasExecution deserializeFamily deserializeRun
  deserializeSample :=
  ⟨[3, 4], (), .returned (.error "codec rejected") [4], trivial, rfl⟩

theorem deserialize_satisfiable : FamilySatisfiable deserializeFamily deserializeSample :=
  deserialize_execution.satisfiable

/-- An owned view of the backing slice of the writer and its u64 cursor. The
mathematical cursor is a Nat; its width and the usize bound of the backing slice
are source-representation obligations, not success conditions of writing. -/
structure Writer where
  bytes : Solanalib.Runtime.Bytes
  position : Nat
  deriving DecidableEq, Repr

/-- One actual `sol_memcpy` dependency request. The source slice is retained
in full, together with the exact count and destination suffix offset. -/
structure CopyRequest where
  offset : Nat
  destinationLength : Nat
  source : Solanalib.Runtime.Bytes
  count : Nat
  deriving DecidableEq, Repr

/-- Pure effects of the one write call used by the override of BpfWriter. -/
structure WriteStep where
  writer : Writer
  count : Nat
  copy : Option CopyRequest
  deriving DecidableEq, Repr

/-- On the selected 64-bit target the old length comparison and the newer
`get_mut(pos as usize..)` branch have this same effect. A zero-byte memcpy is
still reached for an empty source when the destination suffix is nonempty. -/
def writeStep (writer : Writer) (input : Solanalib.Runtime.Bytes) : WriteStep :=
  if writer.position < writer.bytes.length then
    let count := min (writer.bytes.length - writer.position) input.length
    ⟨⟨writer.bytes.take writer.position ++ input.take count ++
        writer.bytes.drop (writer.position + count), writer.position + count⟩,
      count, some ⟨writer.position, writer.bytes.length - writer.position, input, count⟩⟩
  else ⟨writer, 0, none⟩

/-- The writer never reports more bytes than offered. -/
theorem writeStep_count_le (writer : Writer) (input : Solanalib.Runtime.Bytes) :
    (writeStep writer input).count ≤ input.length := by
  unfold writeStep
  split
  · exact Nat.min_le_right _ _
  · exact Nat.zero_le _

/-- The replacement preserves backing length, including on a short write. -/
theorem writeStep_length (writer : Writer) (input : Solanalib.Runtime.Bytes) :
    (writeStep writer input).writer.bytes.length = writer.bytes.length := by
  unfold writeStep
  split
  · rename_i inside
    simp only [List.length_append, List.length_take, List.length_drop]
    have count := Nat.min_le_left (writer.bytes.length - writer.position) input.length
    have offered := Nat.min_le_right (writer.bytes.length - writer.position) input.length
    omega
  · rfl

/-- At an admitted source-width input, a write cannot overflow the u64 cursor. -/
theorem writeStep_position_bound (writer : Writer) (input : Solanalib.Runtime.Bytes) (limit : Nat)
    (position : writer.position < limit) (length : writer.bytes.length < limit) :
    (writeStep writer input).writer.position < limit := by
  unfold writeStep
  split
  · dsimp only
    have count := Nat.min_le_left (writer.bytes.length - writer.position) input.length
    omega
  · exact position

/-- Primitive copy and ordinary diagnostic-error construction. The latter
returns the actual error owner, not just its message. Allocation failure in
diagnostic construction is outside applicability; normal allocation effects
remain observable through the returned State of this dependency. -/
structure WriteTypes where
  State : Type
  Error : Type
  Terminal : Type
  copy : Callback.Run State CopyRequest Unit Empty Terminal
  makeError : Callback.Run State Borsh.IoError Error Empty Terminal

/-- The backing slice and cursor remain part of every state-bearing exit. -/
structure WriteState (State : Type) where
  writer : Writer
  ambient : State
  deriving DecidableEq, Repr

def ambientFocus (State : Type) : Owned.Focus (WriteState State) State where
  get := WriteState.ambient
  set := fun outer inner => { outer with ambient := inner }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- The actual copy dependency runs before the partial bytes/cursor update is
observed by `write_all`. Its terminal exits stop immediately. -/
def copyStep (types : WriteTypes) (step : WriteStep) :
    Callback.Run types.State Unit Unit Empty types.Terminal :=
  match step.copy with
  | none => fun before _ outcome => outcome = .returned () before
  | some request => fun before _ => types.copy before request

/-- BpfWriter overrides the looping std `write_all`: it calls write once and
returns WriteZero on any short count. That error retains the already changed
bytes and cursor. It does not retry and does not roll back a partial copy. -/
def writeAllRun (types : WriteTypes) :
    Callback.Run (WriteState types.State) Solanalib.Runtime.Bytes (Except types.Error Unit) Empty
      types.Terminal :=
  fun before input outcome =>
    let step := writeStep before.writer input
    ∃ copied, copyStep types step before.ambient () copied ∧
      match copied with
      | .returned () ambient =>
        let after := WriteState.mk step.writer ambient
        if step.count = input.length then outcome = .returned (.ok ()) after
        else Callback.map Except.error ((ambientFocus types.State).lift types.makeError)
          after Borsh.writeZeroError outcome
      | .unwound impossible _ => nomatch impossible
      | .terminated reason => outcome = .terminated reason

def writeAllFamily : Family where
  Index := WriteTypes
  State := fun types => WriteState types.State
  Args := fun _ => Solanalib.Runtime.Bytes
  Value := fun types => Except types.Error Unit
  Unwind := fun _ => Empty
  Terminal := WriteTypes.Terminal
  contract := fun types => { requires := fun _ _ => True, post := writeAllRun types }

theorem writeAll_reference : FamilyReference writeAllFamily writeAllRun :=
  fun _ _ _ _ _ run => run

/-- Exact primitive observations for executable conformance and controls. -/
inductive WriteEvent where
  | copied (request : CopyRequest)
  | errorCreated (error : Borsh.IoError)
  deriving DecidableEq, Repr

abbrev writeSample : WriteTypes where
  State := List WriteEvent
  Error := Borsh.IoError
  Terminal := Nat
  copy := fun before request outcome => outcome = .returned () (before ++ [.copied request])
  makeError := fun before error outcome => outcome = .returned error (before ++ [.errorCreated
    error])

/-- The reference observation returns an error after copying only two bytes,
with the cursor at the end of the unchanged-size destination. -/
theorem writeAll_execution : FamilyHasExecution writeAllFamily writeAllRun writeSample := by
  refine ⟨⟨⟨[10, 11, 12], 1⟩, []⟩, [20, 21, 22],
    .returned (.error Borsh.writeZeroError)
      ⟨⟨[10, 20, 21], 3⟩, [.copied ⟨1, 2, [20, 21, 22], 2⟩, .errorCreated Borsh.writeZeroError]⟩,
    trivial, ?_⟩
  refine ⟨.returned () [.copied ⟨1, 2, [20, 21, 22], 2⟩], rfl, ?_⟩
  change Callback.map Except.error ((ambientFocus writeSample.State).lift writeSample.makeError)
    ⟨⟨[10, 20, 21], 3⟩, [.copied ⟨1, 2, [20, 21, 22], 2⟩]⟩ Borsh.writeZeroError _
  refine ⟨.returned Borsh.writeZeroError
    ⟨⟨[10, 20, 21], 3⟩, [.copied ⟨1, 2, [20, 21, 22], 2⟩, .errorCreated Borsh.writeZeroError]⟩, ?_,
      rfl⟩
  exact ⟨.returned Borsh.writeZeroError
    [.copied ⟨1, 2, [20, 21, 22], 2⟩, .errorCreated Borsh.writeZeroError], rfl, rfl⟩

theorem writeAll_satisfiable : FamilySatisfiable writeAllFamily writeSample :=
  writeAll_execution.satisfiable

end Solanalib.Specs.Core.AnchorCodec
