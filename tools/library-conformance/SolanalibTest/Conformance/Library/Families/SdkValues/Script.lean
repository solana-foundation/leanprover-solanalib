/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core
import Solanalib.Specs.Core.ProgramOptionOperations
import Solanalib.Specs.Core.NullableOperations

/-!
The finite callback scripts used by the native SDK value drivers. An input mode
selects return, unwind or process exit before an SDK call. Owner identities and
event order remain observable in every nonterminal outcome. The scripts do not
read the recorded outcome. Their graph lemmas connect execution to the shared
model families, including cleanup after a borrowed nullable query unwinds.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.SdkValues.Script

open Solanalib.Contracts.Model Solanalib.Specs.Core

structure State where
  events : List String
  live : List Nat
  deriving DecidableEq, Repr

structure Tracked where
  id : Nat
  value : UInt64
  dropMode : Nat
  deriving DecidableEq, Repr

structure Query where
  id : Nat
  value : UInt64
  deriving DecidableEq, Repr

abbrev Exit (V : Type) := Outcome State V String Nat

def event (state : State) (message : String) : State :=
  { state with events := state.events ++ [message] }

/-- Linux wait status for the deliberate exit of the driver 73. -/
def processExit : Nat := 18688

/-- Linux wait status for SIGABRT in the recording runtime, including its
core-dump status bit. The kernel retains that bit even with the file-size limit zero. -/
def doublePanic : Nat := 134

def mode {V : Type} (script : Nat) (message : String) (value : V) (state : State) : Exit V :=
  if script = 0 then .returned value state
  else if script = 1 then .unwound message state
  else .terminated processExit

def dropValue (state : State) (value : Tracked) : Exit Unit :=
  let after := event { state with live := state.live.filter (· != value.id) } s!"drop:\
    {value.id}"
  mode value.dropMode s!"drop {value.id}" () after

def equal (script : Nat) (state : State) (args : Tracked × Tracked) : Exit Bool :=
  mode script "eq" (args.1.value == args.2.value)
    (event state s!"eq:{args.1.id}:{args.2.id}")

def contains (script : Nat) (state : State) (args : Query × Tracked) : Exit Bool :=
  mode script "contains" (args.1.value < args.2.value)
    (event state s!"contains:{args.1.id}:{args.2.id}")

def call (script : Nat) (state : State) (args : Tracked × Tracked) : Exit UInt64 :=
  let after := event state s!"call:{args.1.id}:{args.2.id}"
  (dropValue after args.2).bind fun _ afterPayload =>
    (dropValue afterPayload args.1).bind fun _ afterClosure =>
      mode script "call" (args.1.value + args.2.value) afterClosure

def defaultValue (script : Nat) (state : State) (_ : Unit) : Exit Tracked :=
  let after := event state "default"
  if script = 0 then .returned ⟨4, 42, 0⟩ { after with live := (after.live ++ [4]).mergeSort (· ≤
    ·) }
  else if script = 1 then .unwound "default" after
  else .terminated processExit

def query (script : Nat) (isNull : Bool) (state : State) (value : Tracked) : Exit Bool :=
  mode script "query" isNull (event state s!"query:{value.id}")

abbrev eqIndex (script : Nat) : ProgramOption.EqIndex where
  State := State
  T := Tracked
  Unwind := String
  Terminal := Nat
  equal := Callback.ofFunction (equal script)

abbrev containsIndex (script : Nat) : ProgramOption.ContainsIndex where
  State := State
  T := Tracked
  Query := Query
  Unwind := String
  Terminal := Nat
  equal := Callback.ofFunction (contains script)

abbrev unwrapIndex : ProgramOption.UnwrapIndex where
  State := State
  T := Tracked
  Unwind := String
  Terminal := Nat
  panic := Callback.ofFunction fun state message => .unwound message state

abbrev mapIndex (script : Nat) : ProgramOption.MapIndex where
  State := State
  T := Tracked
  U := UInt64
  Closure := Tracked
  Unwind := String
  Terminal := Nat
  call := Callback.ofFunction (call script)
  dropClosure := Callback.ofFunction dropValue

abbrev unwrapOrIndex : ProgramOption.UnwrapOrIndex where
  State := State
  T := Tracked
  Unwind := String
  Terminal := Nat
  dropValue := Callback.ofFunction dropValue
  returnPlace := .retain
  doubleUnwind := fun _ _ _ status => status = doublePanic

abbrev defaultIndex (script : Nat) : ProgramOption.DefaultIndex where
  State := State
  T := Tracked
  Unwind := String
  Terminal := Nat
  defaultValue := Callback.ofFunction (defaultValue script)

abbrev nullableIndex (script : Nat) (isNull : Bool) : Nullable.Index where
  State := State
  T := Tracked
  Unwind := String
  Terminal := Nat
  isNone := Callback.ofFunction (query script isNull)
  dropValue := Callback.ofFunction dropValue
  doubleUnwind := fun _ _ _ status => status = doublePanic

def eq (script : Nat) (state : State)
    (args : ProgramOption.Value Tracked × ProgramOption.Value Tracked) : Exit Bool :=
  match args with
  | (.none, .none) => .returned true state
  | (.some left, .some right) => equal script state (left, right)
  | _ => .returned false state

theorem eq_graph (script : Nat) (state : State)
    (args : ProgramOption.Value Tracked × ProgramOption.Value Tracked) (outcome : Exit Bool) :
    ProgramOption.eqRun (eqIndex script) state args outcome ↔ eq script state args = outcome := by
  rcases args with ⟨left, right⟩
  cases left <;> cases right <;> simp [ProgramOption.eqRun, eq, eqIndex, Callback.ofFunction,
    eq_comm]

def containsRun (script : Nat) (state : State)
    (args : ProgramOption.Value Tracked × Query) : Exit Bool :=
  match args.1 with
  | .none => .returned false state
  | .some value => contains script state (args.2, value)

theorem contains_graph (script : Nat) (state : State)
    (args : ProgramOption.Value Tracked × Query) (outcome : Exit Bool) :
    ProgramOption.containsRun (containsIndex script) state args outcome ↔
      containsRun script state args = outcome := by
  rcases args with ⟨value, query⟩
  cases value <;> simp [ProgramOption.containsRun, containsRun, containsIndex,
    Callback.ofFunction, eq_comm]

def unwrap (state : State) : ProgramOption.Value Tracked → Exit Tracked
  | .none => .unwound ProgramOption.unwrapMessage state
  | .some value => .returned value state

theorem unwrap_graph (state : State) (value : ProgramOption.Value Tracked) (outcome : Exit Tracked)
  :
    ProgramOption.unwrapRun unwrapIndex state value outcome ↔ unwrap state value = outcome := by
  cases value <;> simp [ProgramOption.unwrapRun, unwrap, unwrapIndex,
    Callback.map_ofFunction, eq_comm]

def map (script : Nat) (state : State)
    (args : ProgramOption.Value Tracked × Tracked) : Exit (ProgramOption.Value UInt64) :=
  match args.1 with
  | .none => Outcome.map (fun _ => .none) (dropValue state args.2)
  | .some value => Outcome.map ProgramOption.Value.some (call script state (args.2, value))

theorem map_graph (script : Nat) (state : State)
    (args : ProgramOption.Value Tracked × Tracked) (outcome : Exit (ProgramOption.Value UInt64)) :
    ProgramOption.mapRun (mapIndex script) state args outcome ↔ map script state args = outcome :=
      by
  rcases args with ⟨value, closure⟩
  cases value <;> simp [ProgramOption.mapRun, map, mapIndex, Callback.map_ofFunction]

def unwrapOr (state : State) (args : ProgramOption.Value Tracked × Tracked) : Exit Tracked :=
  match args.1 with
  | .none => .returned args.2 state
  | .some value => Outcome.map (fun _ => value) (dropValue state args.2)

theorem unwrapOr_graph (state : State) (args : ProgramOption.Value Tracked × Tracked)
    (outcome : Exit Tracked) :
    ProgramOption.unwrapOrRun unwrapOrIndex state args outcome ↔ unwrapOr state args = outcome := by
  rcases args with ⟨value, fallback⟩
  cases value <;> simp [ProgramOption.unwrapOrRun, unwrapOr, unwrapOrIndex,
    Callback.map_ofFunction, eq_comm]

def unwrapOrDefault (script : Nat) (state : State) : ProgramOption.Value Tracked → Exit Tracked
  | .none => defaultValue script state ()
  | .some value => .returned value state

theorem default_graph (script : Nat) (state : State) (value : ProgramOption.Value Tracked)
    (outcome : Exit Tracked) :
    ProgramOption.unwrapOrDefaultRun (defaultIndex script) state value outcome ↔
      unwrapOrDefault script state value = outcome := by
  cases value <;> simp [ProgramOption.unwrapOrDefaultRun, unwrapOrDefault, defaultIndex,
    Callback.ofFunction, eq_comm]

def nullable (script : Nat) (isNull : Bool) (state : State) (value : Tracked) : Exit (Option
  Tracked) :=
  match query script isNull state value with
  | .returned false after => .returned (some value) after
  | .returned true after => Outcome.map (fun _ => none) (dropValue after value)
  | .unwound reason after =>
      match dropValue after value with
      | .returned () final => .unwound reason final
      | .unwound _ _ => .terminated doublePanic
      | .terminated reason => .terminated reason
  | .terminated reason => .terminated reason

theorem nullable_graph (script : Nat) (isNull : Bool) (state : State) (value : Tracked)
    (outcome : Exit (Option Tracked)) :
    Nullable.getRun (nullableIndex script isNull) state value outcome ↔
      nullable script isNull state value = outcome := by
  cases h : query script isNull state value with
  | returned result after =>
    cases result <;>
      simp [Nullable.getRun, nullableIndex, Callback.ofFunction, Callback.map,
        nullable, h, eq_comm]
  | unwound reason after =>
    cases hdrop : dropValue after value <;>
      simp [Nullable.getRun, nullableIndex, Callback.ofFunction, Owned.cleanup,
        nullable, h, hdrop, eq_comm]
  | terminated reason =>
    simp [Nullable.getRun, nullableIndex, Callback.ofFunction, nullable, h, eq_comm]

end SolanalibTest.Conformance.Library.Families.SdkValues.Script
