/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.OwnedArrayFacts
public import Solanalib.Specs.Core.OwnedArrayReference

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Owned.Array

/-- An arbitrary mathematical construction interpretation together with its
local completion law. Source ownership, destructor, allocator and callback
bindings remain independent obligations; the index assumes no complete result
or progress theorem for its supplied dependencies. -/
structure ConstructionIndex where
  /-- Actual state shared by construction, evaluation and cleanup. -/
  State : Type
  /-- Owned values or handles returned by the expressions. -/
  Element : Type
  /-- Logical identity of the completed vector. -/
  Resource : Type
  /-- Actual unwind reasons from dependencies or evaluators. -/
  Unwind : Type
  /-- Terminal reasons, with no invented post-state. -/
  Terminal : Type
  /-- Actual supplied construction and cleanup dependencies. -/
  provider : Provider State Element Resource Unwind Terminal
  /-- The actual expression interpretation at each requested index. -/
  evaluate : Callback.Run State Nat Element Unwind Terminal
  /-- Current-vector observation and primitive vector operations. -/
  vectors : VectorOps State Element Resource Unwind Terminal
  /-- Local completion guarantee, separate from the result of the whole constructor. -/
  currentLaw : provider.CurrentLaw vectors

/-- Generic construction preserves the complete operational relation on every
finite exit. A returned resource additionally exposes the exact expression
prefix, requested count and its actual current ordered contents. The trace
already checks expression bounds, the completion count and cleanup permutations;
this partial-correctness contract needs no additional scheduling precondition.
Completeness of a source dependency interpretation remains a separate obligation. -/
def construction_contract : Family where
  Index := ConstructionIndex
  State := ConstructionIndex.State
  Args := fun _ => Nat
  Value := ConstructionIndex.Resource
  Unwind := ConstructionIndex.Unwind
  Terminal := ConstructionIndex.Terminal
  contract := fun interpretation =>
    { requires := fun _ _ => True
      post := fun before count outcome =>
        interpretation.provider.run count interpretation.evaluate before outcome ∧
          match outcome with
          | .returned resource after =>
            ∃ values ready,
              PrefixTrace interpretation.provider count interpretation.evaluate [] before values
                ready ∧
              values.length = count ∧ interpretation.vectors.current after resource = some values
          | .unwound _ _ | .terminated _ => True }

/-- The reference family is the same operational engine instantiated with the
selected providers, evaluator and state; it adds no fabricated finite exit. -/
def construction_run : FamilyRun construction_contract :=
  fun interpretation before count outcome =>
    interpretation.provider.run count interpretation.evaluate before outcome

/-- Closed correctness for every indexed constructor, using only the local
completion law to derive the successful ordered-current-content conclusion. -/
theorem construction_reference : FamilyReference construction_contract construction_run := by
  intro interpretation before count outcome _ execution
  refine ⟨execution, ?_⟩
  cases outcome with
  | returned resource after =>
    exact Provider.run_returned_current interpretation.currentLaw execution
  | unwound reason after => trivial
  | terminated reason => trivial

/-- Closed concrete index with an existing live vector and three actual pure
expressions, two of which return equal values at distinct positions. -/
def construction_sample : construction_contract.Index where
  State := VectorState Nat
  Element := Nat
  Resource := Nat
  Unwind := Empty
  Terminal := Empty
  provider := natReference
  evaluate := natReferenceEvaluate
  vectors := vectorReference
  currentLaw := natReference_currentLaw

/-- The closed sample satisfies the unconditional precondition. -/
theorem construction_satisfiable :
    FamilySatisfiable construction_contract construction_sample :=
  ⟨natReferenceInitial, (3 : Nat), trivial⟩

/-- The same closed index has a complete positive three-expression execution,
returning fresh handle 1 and actual contents [7, 7, 9]. -/
theorem construction_has_execution :
    FamilyHasExecution construction_contract construction_run construction_sample :=
  ⟨natReferenceInitial, (3 : Nat), .returned (1 : Nat) natReferenceAfter,
    trivial, natReference_executes⟩

/-- The concrete successful execution also satisfies the full generic
postcondition, including its exact expression trace and current vector values. -/
theorem construction_sample_post :
    (construction_contract.contract construction_sample).post natReferenceInitial (3 : Nat)
      (.returned (1 : Nat) natReferenceAfter) :=
  construction_reference construction_sample natReferenceInitial (3 : Nat)
    (.returned (1 : Nat) natReferenceAfter)
    trivial natReference_executes

end Solanalib.Specs.Core.Owned.Array
