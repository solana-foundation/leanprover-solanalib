/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Nullable

/-- The Nullable::is_none of the source is a borrowed callback, possibly overridden.
It is not assumed to be equality with a zero value. The T argument retains
identity across the query and any later move or drop; mutable interior data
belongs in State. The query provider includes its own temporary cleanup. -/
structure Index where
  State : Type
  T : Type
  Unwind : Type
  Terminal : Type
  isNone : Callback.Run State T Bool Unwind Terminal
  dropValue : Callback.Run State T Unit Unwind Terminal
  doubleUnwind : Owned.DoubleUnwind State Unwind Terminal

/-- Query first. Null returns None after dropping the still-owned value;
non-null moves it into Some. A query unwind drops the retained owner in the
actual unwind state; a second unwind is terminal. A terminal query does no
later cleanup and has no fabricated post-state. -/
def getRun (index : Index) :
    Callback.Run index.State index.T (Option index.T) index.Unwind index.Terminal :=
  fun before value outcome => ∃ queried, index.isNone before value queried ∧
    match queried with
    | .returned false after => outcome = .returned (some value) after
    | .returned true after =>
        Callback.map (fun _ => none) index.dropValue after value outcome
    | .unwound reason after => Owned.cleanup index.doubleUnwind
        [fun state final => index.dropValue state value final]
        (.unwound reason after : Outcome index.State (Option index.T)
          index.Unwind index.Terminal) outcome
    | .terminated reason => outcome = .terminated reason

def getFamily : Family where
  Index := Index
  State := Index.State
  Args := Index.T
  Value := fun index => Option index.T
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => ⟨fun _ _ => True, getRun index⟩

theorem getReference : FamilyReference getFamily getRun := fun _ _ _ _ _ run => run

/-- A zero-sentinel sample, with observable query and destructor steps. -/
abbrev sample : Index where
  State := Nat
  T := Nat
  Unwind := String
  Terminal := String
  isNone := Callback.ofFunction fun before value => .returned (value == 0) (before + 1)
  dropValue := Callback.ofFunction fun before _ => .returned () (before + 1)
  doubleUnwind := fun _ _ _ reason => reason = "double panic"

theorem getExecution : FamilyHasExecution getFamily getRun sample := by
  unfold FamilyHasExecution
  dsimp only [getFamily, sample, Solanalib.Contracts.Model.HasExecution]
  exact ⟨0, 0, .returned none 2, trivial, .returned true 1, rfl, .returned () 2, rfl, rfl⟩

theorem getSatisfiable : FamilySatisfiable getFamily sample := getExecution.satisfiable

/-- A successful non-null query moves the same value and preserves its callback
state. No equality, cloning or destructor callback follows that query. -/
theorem get_some (index : Index) (before after : index.State) (value : index.T)
    (query : index.isNone before value (.returned false after)) :
    getRun index before value (.returned (some value) after) :=
  ⟨.returned false after, query, rfl⟩

/-- A terminal query stops immediately, independently of its destructor. -/
theorem get_terminal (index : Index) (before : index.State) (value : index.T)
    (reason : index.Terminal) (query : index.isNone before value (.terminated reason)) :
    getRun index before value (.terminated reason) :=
  ⟨.terminated reason, query, rfl⟩

/-- A second panic during retained-value cleanup cannot be converted to an
ordinary returned None or Some. -/
theorem get_double_unwind (index : Index) (before middle after : index.State)
    (value : index.T) (first second : index.Unwind) (terminal : index.Terminal)
    (query : index.isNone before value (.unwound first middle))
    (drop : index.dropValue middle value (.unwound second after))
    (abort : index.doubleUnwind after first second terminal) :
    getRun index before value (.terminated terminal) :=
  ⟨.unwound first middle, query, .unwound second after, drop, terminal, abort, rfl⟩

end Solanalib.Specs.Core.Nullable
