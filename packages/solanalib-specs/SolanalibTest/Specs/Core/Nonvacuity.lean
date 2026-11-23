/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.Nonvacuity

/-- A simple state-changing contract used to distinguish consistency from an
empty relation satisfying partial correctness. -/
def writeContract : Solanalib.Contracts.Model Nat Nat Unit :=
  .returning (fun _ _ => True)
    (fun _ input value after => value = () ∧ after = input)

/-- This relation has no executions, even though the precondition is inhabited. -/
def emptyReference : Nat → Nat →
    Solanalib.Contracts.Model.Outcome Nat Unit Empty Empty → Prop := fun _ _ _ => False

/-- Partial correctness alone admits an empty reference relation. -/
theorem empty_reference_holds : writeContract.Holds emptyReference := by
  intro _ _ _ _ step
  exact False.elim step

/-- The separate execution obligation rejects that empty reference. -/
theorem empty_reference_has_no_execution : ¬ writeContract.HasExecution emptyReference := by
  rintro ⟨_, _, _, _, step⟩
  exact step

/-- The same write operation is meaningful over any Type-valued source model. -/
def replacement : Solanalib.Contracts.Model.Family where
  Index := Type
  State := fun valueType => valueType
  Args := fun valueType => valueType
  Value := fun _ => Unit
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => .returning (fun _ _ => True)
    (fun _ input value after => value = () ∧ after = input)

/-- This reference changes the state to its supplied value at every index. -/
def replacementRun : Solanalib.Contracts.Model.FamilyRun replacement :=
  fun _ => Solanalib.Contracts.Model.returnsOf (fun _ input => ((), input))

/-- One closed theorem covers every value type, independently of the sample. -/
theorem replacement_reference :
    Solanalib.Contracts.Model.FamilyReference replacement replacementRun := by
  intro index
  apply (Solanalib.Contracts.Model.realized_iff_holds
    (replacement.contract index) (fun _ input => ((), input))).mp
  intro _ _ _
  exact ⟨rfl, rfl⟩

/-- The registered nonvacuity sample uses natural-number state. -/
def replacementSample : replacement.Index := Nat

/-- The sample precondition has concrete inhabitants. -/
theorem replacement_satisfiable :
    Solanalib.Contracts.Model.FamilySatisfiable replacement replacementSample :=
  ⟨(3 : Nat), (41 : Nat), True.intro⟩

/-- A concrete reference execution changes the sample state from 3 to 41. -/
theorem replacement_has_execution :
    Solanalib.Contracts.Model.FamilyHasExecution replacement replacementRun replacementSample :=
  ⟨(3 : Nat), (41 : Nat), .returned () (41 : Nat), True.intro, rfl⟩

/-- Universal reference correctness also applies at a different value type. -/
theorem replacement_at_bool :
    (replacement.contract Bool).post true false (.returned () false) :=
  replacement_reference Bool true false (.returned () false) True.intro rfl

/-- A generic family can include an uninhabited type without admitting a false
execution witness at that type. The Nat sample does not prove this instance inhabited. -/
theorem replacement_empty_has_no_execution :
    ¬ Solanalib.Contracts.Model.FamilyHasExecution replacement replacementRun Empty := by
  rintro ⟨before, _, _, _, _⟩
  exact Empty.elim before

/-- A terminal failure has an outcome but no invented post-state. -/
def terminalContract : Solanalib.Contracts.Model Nat Unit Unit Empty Unit where
  requires := fun _ _ => True
  post := fun _ _ outcome => match outcome with
    | .terminated () => True
    | .returned _ _ | .unwound _ _ => False

/-- A reference that terminates with the explicit terminal outcome of the contract. -/
def terminalRun : Nat → Unit →
    Solanalib.Contracts.Model.Outcome Nat Unit Empty Unit → Prop :=
  fun _ _ outcome => outcome = .terminated ()

/-- A failure-only reference can satisfy a contract that specifies that failure. -/
theorem terminal_reference : terminalContract.Holds terminalRun := by
  intro _ _ outcome _ step
  cases step
  exact True.intro

/-- Nonvacuity does not require a successful normal return. -/
theorem terminal_has_execution : terminalContract.HasExecution terminalRun :=
  ⟨7, (), .terminated (), True.intro, rfl⟩

end SolanalibTest.Specs.Core.Nonvacuity
