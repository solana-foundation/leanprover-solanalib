/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.context

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.OwnedContext

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorContextOwned

/-- The versioned primary contract preserves the arbitrary moved payload and
all seed grouping while returning a fresh, currently empty vector owner. -/
theorem fields_from_contract (types : Types) (before after : types.State)
    (args : AnchorContext.NewWithSignerArgs types.Accounts)
    (context : Value types.Accounts types.Resource)
    (post : (Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_contract.contract
      types).post
      before args (.returned context after)) :
    context.accounts = args.accounts ∧ context.programId = args.programId ∧
      context.signerSeeds = args.signerSeeds ∧
      types.remaining.current after context.remaining = some [] ∧
      types.remaining.current before context.remaining = none := by
  obtain ⟨same, current, fresh⟩ := post
  have first := congrArg Prod.fst same
  change context = (newWithSigner types before args).1 at first
  exact ⟨by rw [first]; rfl, by rw [first]; rfl, by rw [first]; rfl, current, fresh⟩

def nonemptyBefore : sample.State := [some [AccountInfo.sampleInfo]]
def created := newWithSigner sample nonemptyBefore sampleArgs

/-- A pre-existing vector is not reused as the newly created empty vector. -/
theorem distinct_from_existing_vector : created.1.remaining = (1 : Nat) ∧
    sample.remaining.current created.2 (0 : Nat) = some [AccountInfo.sampleInfo] ∧
    sample.remaining.current created.2 created.1.remaining = some [] := ⟨rfl, rfl, rfl⟩

def afterPush : sample.State := [some [AccountInfo.sampleInfo], some [AccountInfo.sampleInfo]]

theorem push_later_uses_same_owner : sample.remaining.push created.2
    (created.1.remaining, AccountInfo.sampleInfo) (.returned () afterPush) := ⟨[], rfl, rfl⟩

/-- Current observation follows later vector mutations; it does not silently
classify every context as empty because its constructor used Vec::new. -/
theorem observation_after_push : (observe sample afterPush created.1).map
    AnchorContext.Value.remainingAccounts = some [AccountInfo.sampleInfo] := rfl

theorem source_constructor_execution :
    (Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_contract.contract sample).post
      nonemptyBefore sampleArgs (.returned created.1 created.2) :=
  realizes sample nonemptyBefore sampleArgs
    ⟨Owned.vectorReference_laws.empty_current nonemptyBefore,
      Owned.vectorReference_laws.empty_fresh nonemptyBefore⟩

/-- Empty construction is unchanged, but this unused drop fails to retire
its owner. The context constructor imposes no condition on that operation. -/
def emptyProvider : Types :=
  { sample with remaining := { sample.remaining with
    drop := Callback.ofFunction fun state _ => .returned () state } }

theorem unused_drop_law_fails : ¬ emptyProvider.remaining.Laws := by
  intro laws
  have retired := laws.drop_current [some []] (0 : Nat) [some []] ⟨[], rfl⟩ rfl
  change some ([] : List AccountInfo.Value) = none at retired
  cases retired

theorem empty_provider_ready :
    (Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_contract.contract
      emptyProvider).requires
      nonemptyBefore sampleArgs :=
  ⟨rfl, rfl⟩

/-- The exact registered constructor executes with the two empty-call facts,
even though the provider fails a law for a later, uncalled operation. -/
theorem empty_provider_execution : FamilyHasExecution
    Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_contract
    Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_run emptyProvider :=
  ⟨nonemptyBefore, sampleArgs, .returned created.1 created.2, empty_provider_ready, rfl⟩

/-- Both primitive guarantees are consumed by the current/fresh post of the
actual constructor; no unused drop law is required to obtain it. -/
theorem empty_provider_post_without_drop_law :
    ¬ emptyProvider.remaining.Laws ∧
    (Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_contract.contract
      emptyProvider).post
      nonemptyBefore sampleArgs (.returned created.1 created.2) :=
  ⟨unused_drop_law_fails, realizes emptyProvider nonemptyBefore sampleArgs empty_provider_ready⟩

def nonemptyProvider : Types :=
  { sample with remaining := { sample.remaining with
    empty := fun (before : Owned.VectorState AccountInfo.Value) =>
      (before.length, before ++ [some [AccountInfo.sampleInfo]]) } }

/-- A fresh primitive result is insufficient when its current contents are
nonempty. The primitive still has its explicit result outside admission. -/
theorem nonempty_result_fails_current :
    nonemptyProvider.remaining.empty [] = ((0 : Nat), [some [AccountInfo.sampleInfo]]) ∧
    nonemptyProvider.remaining.current [] (0 : Nat) = none ∧
    ¬ (Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_contract.contract
      nonemptyProvider).requires
      [] sampleArgs := by
  refine ⟨rfl, rfl, ?_⟩
  intro ready
  have wrong := ready.current
  change some [AccountInfo.sampleInfo] = some [] at wrong
  cases wrong

def reusingProvider : Types :=
  { sample with remaining := { sample.remaining with empty := fun before => ((0 : Nat), before) } }

/-- Current emptiness is insufficient if the returned identity was already
live. The unchanged primitive result is rejected only by the freshness fact. -/
theorem reused_owner_fails_freshness :
    reusingProvider.remaining.empty [some []] = ((0 : Nat), [some []]) ∧
    reusingProvider.remaining.current [some []] (0 : Nat) = some [] ∧
    ¬ (Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_contract.contract
      reusingProvider).requires
      [some []] sampleArgs := by
  refine ⟨rfl, rfl, ?_⟩
  intro ready
  have reused := ready.fresh
  change some ([] : List AccountInfo.Value) = none at reused
  cases reused

end SolanalibTest.Specs.AnchorLang.OwnedContext
