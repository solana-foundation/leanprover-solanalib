/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OwnedArrayFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Owned.Array

universe u v w x y

/-- A concrete sequence of normal element/storage drops yields the exact
surviving original unwind with its completed-prefix metadata. -/
theorem Provider.close_of_dropReturns {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    {provider : Provider State Element Resource Unwind Terminal}
    (conforms : provider.Conforms) (values : List Element) (site : FailureSite)
    (before after : State) (reason : Unwind)
    (drops : DropReturns
      (provider.cleanupActions values (provider.cleanupOrder before values)) before after) :
    provider.close values site before reason (.unwound (⟨values.length, site⟩, reason) after) :=
  ⟨conforms.cleanup_permutation before values, .unwound reason after,
    drops.cleanup_unwound provider.double reason, rfl⟩

/-- Detailed unwind progress always lies between the entry prefix and total
count. An evaluator failure is before the final count; a completion failure is
at it. These are exact trace facts, independent of a chosen allocation schedule. -/
theorem Trace.unwound_progress {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    {provider : Provider State Element Resource Unwind Terminal} {count : Nat}
    {evaluate : Callback.Run State Nat Element Unwind Terminal}
    {values : List Element} {before : State}
    {outcome : Outcome State Resource (Failure × Unwind) Terminal}
    (execution : Trace provider count evaluate values before outcome)
    {failure : Failure} {reason : Unwind} {after : State}
    (unwound : outcome = .unwound (failure, reason) after) (bounded : values.length ≤ count) :
    values.length ≤ failure.completed ∧ failure.completed ≤ count ∧
      (failure.site = .evaluate → failure.completed < count) ∧
      (failure.site = .finish → failure.completed = count) := by
  induction execution generalizing failure reason after with
  | again values before middle outcome work rest induction => exact induction unwound bounded
  | next values before ready middle value outcome bound work expression rest induction =>
    have extendedBound : (values ++ [value]).length ≤ count := by
      simp only [List.length_append, List.length_singleton]
      omega
    obtain ⟨low, high, evaluation, finish⟩ := induction unwound extendedBound
    refine ⟨?_, high, evaluation, finish⟩
    simp only [List.length_append, List.length_singleton] at low
    omega
  | workUnwind values before middle original outcome work closed =>
    rw [unwound] at closed
    obtain ⟨rfl, _⟩ := Provider.close_unwound closed
    exact ⟨Nat.le_refl _, bounded, (by intro impossible; cases impossible),
      (by intro impossible; cases impossible)⟩
  | workTerminal => cases unwound
  | evaluateUnwind values before ready middle original outcome bound work expression closed =>
    rw [unwound] at closed
    obtain ⟨rfl, _⟩ := Provider.close_unwound closed
    exact ⟨Nat.le_refl _, bounded, (fun _ => bound), (by intro impossible; cases impossible)⟩
  | evaluateTerminal => cases unwound
  | finishReturn => cases unwound
  | finishUnwind values before ready middle original outcome complete work finished closed =>
    rw [unwound] at closed
    obtain ⟨rfl, _⟩ := Provider.close_unwound closed
    exact ⟨Nat.le_refl _, bounded, (by intro impossible; cases impossible), (fun _ => complete)⟩
  | finishTerminal => cases unwound

/-- If no expression can unwind, surviving constructor failures cannot claim
an expression failure site. This is the extra fact used by move-only prefixes
with a final non-unwinding clone; count alone would not suffice otherwise. -/
theorem Trace.unwound_not_evaluate {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    {provider : Provider State Element Resource Unwind Terminal} {count : Nat}
    {evaluate : Callback.Run State Nat Element Unwind Terminal}
    (noUnwind : ∀ before index reason after, ¬ evaluate before index (.unwound reason after))
    {values : List Element} {before : State}
    {outcome : Outcome State Resource (Failure × Unwind) Terminal}
    (execution : Trace provider count evaluate values before outcome)
    {failure : Failure} {reason : Unwind} {after : State}
    (unwound : outcome = .unwound (failure, reason) after) : failure.site ≠ .evaluate := by
  induction execution generalizing failure reason after with
  | again values before middle outcome work rest induction => exact induction unwound
  | next values before ready middle value outcome bound work expression rest induction =>
    exact induction unwound
  | workUnwind values before middle original outcome work closed =>
    rw [unwound] at closed
    obtain ⟨rfl, _⟩ := Provider.close_unwound closed
    intro impossible
    cases impossible
  | workTerminal => cases unwound
  | evaluateUnwind values before ready middle original outcome bound work expression closed =>
    exact False.elim (noUnwind ready values.length original middle expression)
  | evaluateTerminal => cases unwound
  | finishReturn => cases unwound
  | finishUnwind values before ready middle original outcome complete work finished closed =>
    rw [unwound] at closed
    obtain ⟨rfl, _⟩ := Provider.close_unwound closed
    intro impossible
    cases impossible
  | finishTerminal => cases unwound

end Solanalib.Specs.Core.Owned.Array
