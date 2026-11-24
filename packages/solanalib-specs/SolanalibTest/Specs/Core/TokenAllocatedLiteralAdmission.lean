/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.TokenAllocatedLiteralAdmission

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.OnchainAllocated

/-- The initial literal of the source still has all four expressions to evaluate. -/
def prematureTypes : Types :=
  { Witness.sampleTypes with infoLiteral := { Witness.sampleTypes.infoLiteral with
      work := fun before _ outcome => outcome = .returned .finish before } }

/-- Reuse the sample collector and CPI; only literal control is changed. -/
def prematureDependencies : Dependencies prematureTypes :=
  ⟨Witness.sampleDependencies.collect, Witness.sampleDependencies.invoke⟩

/-- A real finite finish request is rejected before the local count check
could erase its continuation. No complete constructor outcome is assumed. -/
theorem premature_finish_rejected :
    prematureTypes.infoLiteral.work Witness.initialState (4, [])
      (.returned .finish Witness.initialState) ∧
    ¬ (family.contract ⟨prematureTypes, prematureDependencies⟩).requires
      Witness.initialState Onchain.witnessArgs := by
  refine ⟨rfl, ?_⟩
  rintro ⟨_, admitted, _⟩
  have impossible := admitted.literalReady.finish_count .initial Witness.initialState []
    Witness.initialState (by decide) rfl
  cases impossible

/-- An evaluate-only provider eventually requests an expression past the end. -/
def overrunTypes : Types :=
  { Witness.sampleTypes with infoLiteral := { Witness.sampleTypes.infoLiteral with
      work := fun before _ outcome => outcome = .returned .evaluate before } }

/-- Reuse the sample collector and CPI; only literal control is changed. -/
def overrunDependencies : Dependencies overrunTypes :=
  ⟨Witness.sampleDependencies.collect, Witness.sampleDependencies.invoke⟩

/-- The source callback at index four is absent. The contract rejects the
actual finite command that would select it after four completed expressions. -/
theorem out_of_range_evaluate_rejected :
    overrunTypes.infoLiteral.work Witness.initialState
      (4, List.replicate 4 Onchain.witnessInfo) (.returned .evaluate Witness.initialState) ∧
    (∀ produced, ¬ initialInfoAt overrunTypes Onchain.witnessArgs
      Witness.initialState 4 produced) ∧
    ¬ (family.contract ⟨overrunTypes, overrunDependencies⟩).requires
      Witness.initialState Onchain.witnessArgs := by
  refine ⟨rfl, fun _ impossible => impossible, ?_⟩
  rintro ⟨_, admitted, _⟩
  have impossible := admitted.literalReady.evaluate_bound .initial Witness.initialState
    (List.replicate 4 Onchain.witnessInfo) Witness.initialState (by decide) rfl
  exact (Nat.lt_irrefl 4) impossible

/-- This provider can perform the normal evaluation schedule or unwind,
but supplies an empty cleanup order even after an expression returned. -/
def omittedTypes : Types :=
  { Witness.sampleTypes with infoLiteral := { Witness.sampleTypes.infoLiteral with
      work := fun before input outcome => Witness.sampleTypes.infoLiteral.work before input outcome
        ∨
        outcome = .unwound (31 : Nat) before
      cleanupOrder := fun _ _ => [] } }

/-- Reuse the sample collector and CPI; only literal control is changed. -/
def omittedDependencies : Dependencies omittedTypes :=
  ⟨Witness.sampleDependencies.collect, Witness.sampleDependencies.invoke⟩

/-- The real work unwind and unchanged partial close show the cleanup-order
failure independently of any complete constructor result. Admission rejects it. -/
theorem omitted_cleanup_rejected :
    omittedTypes.infoLiteral.work Witness.initialState (4, [Onchain.witnessInfo])
      (.unwound (31 : Nat) Witness.initialState) ∧
    (∀ final, ¬ omittedTypes.literalProvider.close [Onchain.witnessInfo] .work
      Witness.initialState (31 : Nat) final) ∧
    ¬ (family.contract ⟨omittedTypes, omittedDependencies⟩).requires
      Witness.initialState Onchain.witnessArgs := by
  refine ⟨Or.inr rfl, ?_, ?_⟩
  · rintro final ⟨permutation, _⟩
    have impossible := permutation.length_eq
    change 0 = 1 at impossible
    cases impossible
  · rintro ⟨_, admitted, _⟩
    have impossible := (admitted.literalReady.cleanup_order .initial Witness.initialState
      [Onchain.witnessInfo] (by decide)).length_eq
    change 0 = 1 at impossible
    cases impossible

/-- Work and storage retirement have separate observable auxiliary effects. -/
def changed (amount : Nat) (state : Witness.State) : Witness.State :=
  (state.1, { state.2 with invocations := state.2.invocations + amount })

/-- All actual work exits are abnormal; no termination or allocation success
is added by the control laws. The empty-prefix storage cleanup still runs. -/
def effectTypes : Types :=
  { Witness.sampleTypes with infoLiteral := { Witness.sampleTypes.infoLiteral with
      work := fun before _ outcome =>
        outcome = .unwound (51 : Nat) (changed 3 before) ∨ outcome = .terminated (91 : Nat)
      retire := fun before _ outcome => outcome = .returned () (changed 2 before) } }

theorem effects_admitted : LiteralAdmission.Ready effectTypes := by
  constructor
  · intro _ _ _ _ _ called
    rcases called with impossible | impossible <;> cases impossible
  · intro _ _ _ _ _ called
    rcases called with impossible | impossible <;> cases impossible
  · intro _ _ _ _
    exact List.Perm.refl _

/-- An actual storage-retirement return preserves the original work unwind,
both state changes, and exact zero-completed-expression metadata. -/
theorem work_unwind_retains_cleanup_effects :
    effectTypes.literalProvider.runDetailed 4 (initialInfoAt effectTypes Onchain.witnessArgs)
      Witness.initialState
      (.unwound (⟨0, .work⟩, (51 : Nat)) (changed 2 (changed 3 Witness.initialState))) := by
  have drops : Owned.DropReturns
      (effectTypes.literalProvider.cleanupActions [] [])
      (changed 3 Witness.initialState) (changed 2 (changed 3 Witness.initialState)) :=
    .cons _ _ _ _ _ rfl (.nil _)
  exact effects_admitted.work_unwind .initial (by decide)
    (Or.inl rfl) (drops.cleanup_unwound effectTypes.doubleUnwind (51 : Nat))

/-- The actual terminal alternative of the same provider bypasses storage cleanup
and has no fabricated post-state. -/
theorem work_terminal_bypasses_cleanup :
    effectTypes.literalProvider.runDetailed 4 (initialInfoAt effectTypes Onchain.witnessArgs)
      Witness.initialState (.terminated (91 : Nat)) :=
  .workTerminal [] Witness.initialState (91 : Nat) (Or.inr rfl)

/-- The full source sample still inhabits the same registered family after
all three literal-control laws and the other admission checks are required. -/
theorem full_sample_executes : FamilyHasExecution family reference Witness.sample :=
  Witness.has_execution

end SolanalibTest.Specs.Core.TokenAllocatedLiteralAdmission
