/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.OwnedCleanup
public import Solanalib.Runtime.Basic

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.ProgramPack

/-- The source type, selected trait callbacks, error representation and value
destructor. `unpack_unchecked` is overridable: this index deliberately does not
replace it by the default length check of the trait. The error type can retain the
owned String resource of legacy `BorshIoError`. -/
structure Index where
  State : Type
  Value : Type
  Error : Type
  Unwind : Type
  Terminal : Type
  uninitializedAccount : Error
  unpackUnchecked : Callback.Run State Solanalib.Runtime.Bytes (Except Error Value) Unwind Terminal
  initialized : Callback.Run State Value Bool Unwind Terminal
  dropValue : Callback.Run State Value Unit Unwind Terminal
  doubleUnwind : Owned.DoubleUnwind State Unwind Terminal

/-- The selected value remains owned while its shared initialization query
runs. A query unwind drops it; an ordinary false result drops it once before
returning UninitializedAccount. A destructor unwind does not run a second drop. -/
def check (index : Index) (value : index.Value) :
    Callback.Run index.State Unit (Except index.Error index.Value) index.Unwind index.Terminal :=
  let drop : Owned.DropAction index.State index.Unwind index.Terminal :=
    fun state => index.dropValue state value
  let queried : Callback.Run index.State Unit Bool index.Unwind index.Terminal :=
    Owned.protect index.doubleUnwind [drop] (fun before _ => index.initialized before value)
  Callback.bind queried fun initialized after outcome =>
    if initialized then outcome = .returned (.ok value) after
    else Owned.scope index.doubleUnwind [drop]
      (fun before (_ : Unit) final => final = .returned (.error index.uninitializedAccount) before)
      after () outcome

/-- A decoding error propagates unchanged and skips initialization and drop.
Successful decoding threads its actual state into the initialization query. -/
def unpack (index : Index) :
    Callback.Run index.State Solanalib.Runtime.Bytes (Except index.Error index.Value)
      index.Unwind index.Terminal :=
  Callback.bind index.unpackUnchecked fun result after outcome =>
    match result with
    | .error error => outcome = .returned (.error error) after
    | .ok value => check index value after () outcome

def family : Family where
  Index := Index
  State := Index.State
  Args := fun _ => Solanalib.Runtime.Bytes
  Value := fun index => Except index.Error index.Value
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => { requires := fun _ _ => True, post := unpack index }

def reference : FamilyRun family := unpack

theorem reference_holds : FamilyReference family reference := fun _ _ _ _ _ run => run

/-- The default `unpack_unchecked` is available as a separate composition when
the source resolution actually selects that provided method. Length mismatch
precedes the selected `unpack_from_slice`, and does not call it. -/
def defaultUnchecked {State Value Error Unwind Terminal : Type} (length : Nat)
    (invalidAccountData : Error)
    (decode : Callback.Run State Solanalib.Runtime.Bytes (Except Error Value) Unwind Terminal) :
    Callback.Run State Solanalib.Runtime.Bytes (Except Error Value) Unwind Terminal :=
  fun before bytes outcome =>
    if bytes.length ≠ length then outcome = .returned (.error invalidAccountData) before
    else decode before bytes outcome

theorem default_wrong_length {State Value Error Unwind Terminal : Type} (length : Nat)
    (invalidAccountData : Error)
    (decode : Callback.Run State Solanalib.Runtime.Bytes (Except Error Value) Unwind Terminal)
    (before : State) (bytes : Solanalib.Runtime.Bytes) (wrong : bytes.length ≠ length)
    (outcome : Outcome State (Except Error Value) Unwind Terminal) :
    defaultUnchecked length invalidAccountData decode before bytes outcome ↔
      outcome = .returned (.error invalidAccountData) before := by
  simp [defaultUnchecked, wrong]

theorem decode_error (index : Index) (before after : index.State) (bytes : Solanalib.Runtime.Bytes)
    (error : index.Error)
    (decoded : index.unpackUnchecked before bytes (.returned (.error error) after)) :
    unpack index before bytes (.returned (.error error) after) :=
  ⟨.returned (.error error) after, decoded, rfl⟩

theorem initialized_return (index : Index) (before decoded checked : index.State)
    (bytes : Solanalib.Runtime.Bytes) (value : index.Value)
    (decode : index.unpackUnchecked before bytes (.returned (.ok value) decoded))
    (query : index.initialized decoded value (.returned true checked)) :
    unpack index before bytes (.returned (.ok value) checked) := by
  refine ⟨.returned (.ok value) decoded, decode, ?_⟩
  exact ⟨.returned true checked, ⟨.returned true checked, query, rfl⟩, rfl⟩

theorem uninitialized_drop (index : Index) (before decoded checked after : index.State)
    (bytes : Solanalib.Runtime.Bytes) (value : index.Value)
    (decode : index.unpackUnchecked before bytes (.returned (.ok value) decoded))
    (query : index.initialized decoded value (.returned false checked))
    (drop : index.dropValue checked value (.returned () after)) :
    unpack index before bytes (.returned (.error index.uninitializedAccount) after) := by
  refine ⟨.returned (.ok value) decoded, decode, ?_⟩
  refine ⟨.returned false checked, ⟨.returned false checked, query, rfl⟩, ?_⟩
  exact ⟨.returned (.error index.uninitializedAccount) checked, rfl,
    .returned () after, drop, rfl⟩

/-- An explicit nonempty sample, including both successful and false-query
paths. The Nat state counts decoder, query and drop effects. -/
def sample : Index where
  State := Nat
  Value := Bool
  Error := Nat
  Unwind := Nat
  Terminal := Nat
  uninitializedAccount := 10
  unpackUnchecked := Callback.ofFunction fun before bytes =>
    .returned (.ok (!bytes.isEmpty)) (before + 1)
  initialized := Callback.ofFunction fun before value => .returned value (before + 10)
  dropValue := Callback.ofFunction fun before _ => .returned () (before + 100)
  doubleUnwind := fun _ first later terminal => terminal = first + later

theorem sample_execution : FamilyHasExecution family reference sample :=
  ⟨(0 : Nat), [1], .returned (.ok true) (11 : Nat), trivial,
    initialized_return sample (0 : Nat) (1 : Nat) (11 : Nat) [1] true rfl rfl⟩

theorem sample_satisfiable : FamilySatisfiable family sample := sample_execution.satisfiable

end Solanalib.Specs.Core.ProgramPack
