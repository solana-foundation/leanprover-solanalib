/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoContracts
public import Solanalib.Specs.Core.BorrowValid

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountInfo

/-- At a typed present cell, the getter either reports the actual borrow
conflict/saturation or reads the selected value and releases its temporary guard. -/
theorem observe_typed (observation : Observation) (state : State) (info : Value)
    (cell : Borrow.Cell Content) (value : Nat)
    (present : state.lookupCell (observation.handle info) = some cell)
    (project : observation.project cell.value = some value) :
    observe observation state info = (.borrowFailed, state) ∨
      ∃ after, observe observation state info = (.value value, after) := by
  by_cases busy : state.exclusiveCount (observation.handle info) ≠ 0
  · exact Or.inl (by simp [observe, Borrow.acquire, present, busy])
  by_cases saturated : cell.policy.sharedLimit ≤ state.sharedCount (observation.handle info)
  · exact Or.inl (by simp [observe, Borrow.acquire, present, busy, saturated])
  let issued := state.issue (observation.handle info) .shared View.whole
  have acquired : Borrow.acquire state (observation.handle info) .shared View.whole =
      (.ok issued.1, issued.2) := by
    simp [Borrow.acquire, present, busy, saturated, issued]
  have current := Borrow.acquire_current acquired present
  have released := Borrow.release_after_acquire acquired
  exact Or.inr ⟨{ issued.2 with slots := issued.2.slots.set issued.1.id none },
    by simp [observe, acquired, current, project, released]⟩

/-- A present selected typed cell excludes the malformed-model branch of the getter. -/
theorem observe_not_malformed (observation : Observation)
    (state : State) (info : Value) (ready : ObservationReady observation state info) :
    (observe observation state info).1 ≠ .malformed := by
  obtain ⟨cell, value, present, project⟩ := ready
  rcases observe_typed observation state info cell value present project with bad | ⟨after, good⟩
  · simp [bad]
  · simp [good]

/-- Every permitted input has a finite mathematical getter observation, including
the configured panic strategy. This is not a Rust termination theorem. -/
theorem observe_reference_exists (observation : Observation) (state : State) (args : Args)
    (ready : ObservationReady observation state args.info) :
    ∃ outcome, observeReference observation state args outcome := by
  have wellTyped := observe_not_malformed observation state args.info ready
  cases step : observe observation state args.info with
  | mk result after =>
    cases result with
    | malformed => simp [step] at wellTyped
    | value value => exact ⟨.returned value after, by simp [observeReference, observePost, step]⟩
    | borrowFailed =>
      cases strategy : args.profile.aborts with
      | false => exact ⟨.unwound .borrowFailed after, by simp [observeReference, observePost, step,
        strategy]⟩
      | true => exact ⟨.terminated .borrowFailed, by simp [observeReference, observePost, step,
        strategy]⟩

end Solanalib.Specs.Core.AccountInfo
