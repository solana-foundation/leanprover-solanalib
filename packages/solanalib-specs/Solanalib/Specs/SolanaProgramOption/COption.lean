/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.ProgramOption
public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.ProgramOptionOperations

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgramOption.COption

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The source is generic over every sized payload type. Neither inspection
nor its model needs a Clone, Copy, equality or destructor callback. -/
def is_some_contract : Family where
  Index := Type
  State := fun _ => Unit
  Args := ProgramOption.Value
  Value := fun _ => Bool
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => .returning (fun _ _ => True)
    (fun before option value after => after = before ∧ value = ProgramOption.isSome option)

/-- Total variant inspection for every payload type. -/
def is_some_run : FamilyRun is_some_contract :=
  fun _ => returnsOf fun before option => (ProgramOption.isSome option, before)

theorem is_some_reference : FamilyReference is_some_contract is_some_run := by
  intro T before option outcome _ step
  cases outcome with
  | returned value after =>
      cases step
      exact ⟨rfl, rfl⟩
  | unwound reason _ | terminated reason => cases reason

/-- A concrete payload type for the registered execution witness. -/
def is_some_sample : Type := Nat

theorem is_some_hasExecution :
    FamilyHasExecution is_some_contract is_some_run is_some_sample :=
  ⟨(), ProgramOption.Value.some (7 : Nat), .returned true (), trivial, rfl⟩

theorem is_some_satisfiable : FamilySatisfiable is_some_contract is_some_sample :=
  is_some_hasExecution.satisfiable

end Solanalib.Specs.SolanaProgramOption.COption

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgramOption.COption

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Return a field reference retaining the same parent identity. -/
abbrev as_ref_contract : Family := ProgramOption.asRefFamily

/-- Exact relational reference at every source interpretation. -/
abbrev as_ref_run : FamilyRun as_ref_contract := ProgramOption.asRefRun

theorem as_ref_reference : FamilyReference as_ref_contract as_ref_run :=
  ProgramOption.asRefReference

/-- Closed registered source-type and callback sample. -/
abbrev as_ref_sample := ProgramOption.asRefSample

theorem as_ref_has_execution : FamilyHasExecution as_ref_contract as_ref_run as_ref_sample :=
  ProgramOption.asRefExecution

theorem as_ref_satisfiable : FamilySatisfiable as_ref_contract as_ref_sample :=
  ProgramOption.asRefSatisfiable

/-- Inspect only the absent discriminant. -/
abbrev is_none_contract : Family := ProgramOption.isNoneFamily

/-- Exact relational reference at every source interpretation. -/
abbrev is_none_run : FamilyRun is_none_contract := ProgramOption.isNoneRun

theorem is_none_reference : FamilyReference is_none_contract is_none_run :=
  ProgramOption.isNoneReference

/-- Closed registered source-type and callback sample. -/
abbrev is_none_sample := ProgramOption.isNoneSample

theorem is_none_has_execution : FamilyHasExecution is_none_contract is_none_run is_none_sample :=
  ProgramOption.isNoneExecution

theorem is_none_satisfiable : FamilySatisfiable is_none_contract is_none_sample :=
  ProgramOption.isNoneSatisfiable

/-- Call FnOnce on Some; drop the unused closure on None; preserve every callback exit. -/
abbrev map_contract : Family := ProgramOption.mapFamily

/-- Exact relational reference at every source interpretation. -/
abbrev map_run : FamilyRun map_contract := ProgramOption.mapRun

theorem map_reference : FamilyReference map_contract map_run :=
  ProgramOption.mapReference

/-- Closed registered source-type and callback sample. -/
abbrev map_sample := ProgramOption.mapSample

theorem map_has_execution : FamilyHasExecution map_contract map_run map_sample :=
  ProgramOption.mapExecution

theorem map_satisfiable : FamilySatisfiable map_contract map_sample :=
  ProgramOption.mapSatisfiable

/-- Move the fallback on None; drop the fallback on Some before returning its payload. -/
abbrev unwrap_or_contract : Family := ProgramOption.unwrapOrFamily

/-- Exact relational reference at every source interpretation. -/
abbrev unwrap_or_run : FamilyRun unwrap_or_contract := ProgramOption.unwrapOrRun

theorem unwrap_or_reference : FamilyReference unwrap_or_contract unwrap_or_run :=
  ProgramOption.unwrapOrReference

/-- Closed registered source-type and callback sample. -/
abbrev unwrap_or_sample := ProgramOption.unwrapOrSample

theorem unwrap_or_has_execution : FamilyHasExecution unwrap_or_contract unwrap_or_run
  unwrap_or_sample :=
  ProgramOption.unwrapOrExecution

theorem unwrap_or_satisfiable : FamilySatisfiable unwrap_or_contract unwrap_or_sample :=
  ProgramOption.unwrapOrSatisfiable


end Solanalib.Specs.SolanaProgramOption.COption
