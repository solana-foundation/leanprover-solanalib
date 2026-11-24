/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.NullableOperations
public import Solanalib.Runtime.Ids

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Nullable.Value

/-- A source interpretation with a pure total null query and a trivial
destructor. This index is not applicable to an effectful override or destructor. -/
def index {T : Type} (isNull : T → Bool) : Nullable.Index where
  State := Unit
  T := T
  Unwind := Empty
  Terminal := Empty
  isNone := Callback.ofFunction fun before value => .returned (isNull value) before
  dropValue := Callback.ofFunction fun before _ => .returned () before
  doubleUnwind := fun _ impossible => nomatch impossible

def get {T : Type} (isNull : T → Bool) (value : T) : Option T :=
  if isNull value then none else some value

/-- The exact pure-value graph is derived from the general cleanup relation. -/
theorem graph {T : Type} (isNull : T → Bool) (before : Unit) (value : T)
    (outcome : Outcome Unit (Option T) Empty Empty) :
    Nullable.getRun (index isNull) before value outcome ↔
      outcome = .returned (get isNull value) before := by
  simp only [Nullable.getRun, index, Callback.ofFunction, exists_eq_left']
  cases query : isNull value <;>
    simp [query, get, Callback.map, Callback.ofFunction, eq_comm]

/-- The reviewed Address implementations reserve the all-zero key. -/
def addressIndex : Nullable.Index := index (fun key : Solanalib.Runtime.Pubkey => decide (key =
  Solanalib.Runtime.Ids.systemProgram))

def addressGet := get (fun key : Solanalib.Runtime.Pubkey => decide (key =
  Solanalib.Runtime.Ids.systemProgram))

theorem address_graph (before : Unit) (key : Solanalib.Runtime.Pubkey) (outcome : Outcome Unit
  (Option Solanalib.Runtime.Pubkey) Empty Empty) :
    Nullable.getRun addressIndex before key outcome ↔ outcome = .returned (addressGet key) before :=
  graph _ _ _ _

theorem address_execution : FamilyHasExecution Nullable.getFamily (Nullable.getRun) addressIndex :=
  by
  refine ⟨(), Solanalib.Runtime.Ids.systemProgram, .returned none (), trivial, ?_⟩
  apply (address_graph _ _ _).mpr
  simp [addressGet, get]
  rfl

theorem address_satisfiable : FamilySatisfiable Nullable.getFamily addressIndex :=
  address_execution.satisfiable

end Solanalib.Specs.Core.Nullable.Value
