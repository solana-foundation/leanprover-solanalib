/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OracleSwitchboard

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SwitchboardOnDemand.on_demand.accounts.pull_feed.PullFeedAccountData

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Oracle.Switchboard

/-- The parser consumes an existing data guard. Its successful reference
denotes the live 3200-byte payload; validation errors release it. Every result
preserves the borrow-state invariant and retires the input token. The source
shared-reference mode and slice extent require separate interpretation. -/
def parse_contract : Solanalib.Contracts.Model State Args (Except ParseError FeedRef) :=
  .returning Ready
    (fun before args result after => parse before args = some (result, after) ∧
      after.Valid ∧ after.resolve args.guard = none)

/-- Invalid model representations have no invented ordinary SDK exit. -/
def parse_run (before : State) (args : Args) :
    Outcome State (Except ParseError FeedRef) Empty Empty → Prop
  | .returned result after => parse before args = some (result, after)
  | .unwound reason _ | .terminated reason => nomatch reason

/-- The input invariant supplies validity and token retirement at every exit. -/
theorem parse_reference : parse_contract.Holds parse_run := by
  intro before args outcome ready executed
  cases outcome with
  | returned result after =>
    exact ⟨executed, parse_valid_consumes before args result after ready executed⟩
  | unwound reason _ | terminated reason => cases reason

/-- The concrete account bytes and acquired input guard meet the precondition. -/
theorem sample_ready : Ready (sampleState sampleBytes) sampleArgs := by
  refine ⟨sampleState_valid _, ⟨⟨0⟩, .shared, 0, .whole⟩, ⟨0, sampleBytes⟩,
    rfl, rfl⟩

/-- The admitted parser produces an actual finite reference exit. -/
theorem parse_hasExecution : parse_contract.HasExecution parse_run := by
  obtain ⟨result, after, executed⟩ := parse_exists _ _ sample_ready
  exact ⟨sampleState sampleBytes, sampleArgs, .returned result after, sample_ready, executed⟩

/-- The actual shared-guard execution witnesses a satisfiable precondition. -/
theorem parse_satisfiable : parse_contract.Satisfiable := parse_hasExecution.satisfiable

end Solanalib.Specs.SwitchboardOnDemand.on_demand.accounts.pull_feed.PullFeedAccountData
