/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OwnedArrayLaws

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Owned.Array

universe u v w x y

/-- Cleanup begun during an unwind either preserves that exact unwind reason
with its actual final state, or terminates. It cannot turn failure into success. -/
theorem cleanup_unwound_shape {State : Type u} {Value : Type v}
    {Unwind : Type x} {Terminal : Type y}
    (double : DoubleUnwind State Unwind Terminal)
    (drops : List (DropAction State Unwind Terminal))
    {before : State} {reason : Unwind} {final : Outcome State Value Unwind Terminal}
    (execution : cleanup double drops (.unwound reason before) final) :
    (∃ after, final = .unwound reason after) ∨ (∃ terminal, final = .terminated terminal) := by
  induction drops generalizing before with
  | nil => exact Or.inl ⟨before, execution⟩
  | cons action rest induction =>
    obtain ⟨dropped, _, remaining⟩ := execution
    cases dropped with
    | returned returnedUnit after =>
      cases returnedUnit
      exact induction remaining
    | unwound later after =>
      obtain ⟨terminal, _, result⟩ := remaining
      exact Or.inr ⟨terminal, result⟩
    | terminated terminal => exact Or.inr ⟨terminal, remaining⟩

/-- Erasing progress after annotation is an exact identity on finite exits. -/
theorem erase_annotate {State : Type u} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y} (failure : Failure)
    (outcome : Outcome State Resource Unwind Terminal) :
    erase (annotate failure outcome) = outcome := by
  cases outcome <;> rfl

/-- Constructor unwind cleanup cannot produce a returned vector. -/
theorem Provider.close_ne_returned {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (provider : Provider State Element Resource Unwind Terminal)
    (values : List Element) (site : FailureSite) (before : State) (reason : Unwind)
    (resource : Resource) (after : State) :
    ¬ provider.close values site before reason (.returned resource after) := by
  rintro ⟨_, pending, cleaned, result⟩
  rcases cleanup_unwound_shape provider.double _ cleaned with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · cases result
  · cases result

/-- Surviving unwind metadata names the exact prefix and original failure
site; destructor state changes cannot invent a different progress count. -/
theorem Provider.close_unwound {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    {provider : Provider State Element Resource Unwind Terminal}
    {values : List Element} {site : FailureSite} {before after : State}
    {reason original : Unwind} {failure : Failure}
    (execution : provider.close values site before reason (.unwound (failure, original) after)) :
    failure = ⟨values.length, site⟩ ∧ original = reason := by
  obtain ⟨_, pending, cleaned, result⟩ := execution
  rcases cleanup_unwound_shape provider.double _ cleaned with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · cases result
    exact ⟨rfl, rfl⟩
  · cases result

/-- Normal construction before completion, retaining all work and expression
after-states. Each expression index is the length of the preceding returned
prefix, so this trace records exact order and once-only evaluation. -/
inductive PrefixTrace {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (provider : Provider State Element Resource Unwind Terminal) (count : Nat)
    (evaluate : Callback.Run State Nat Element Unwind Terminal) :
    List Element → State → List Element → State → Prop
  /-- End the prefix before the separate completion work. -/
  | stop (values : List Element) (state : State) :
      PrefixTrace provider count evaluate values state values state
  /-- Include a finite internal construction chunk without re-evaluation. -/
  | again (values finalValues : List Element) (before middle after : State)
      (work : provider.work before (count, values) (.returned .again middle))
      (rest : PrefixTrace provider count evaluate values middle finalValues after) :
      PrefixTrace provider count evaluate values before finalValues after
  /-- Include one exact indexed expression and its actual returned value. -/
  | next (values finalValues : List Element) (before ready middle after : State)
      (value : Element) (bound : values.length < count)
      (work : provider.work before (count, values) (.returned .evaluate ready))
      (expression : evaluate ready values.length (.returned value middle))
      (rest : PrefixTrace provider count evaluate (values ++ [value]) middle finalValues after) :
      PrefixTrace provider count evaluate values before finalValues after

/-- A normal prefix only appends actual returned values; it cannot replace,
deduplicate, reorder, or remove values that were already evaluated. -/
theorem PrefixTrace.extends {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    {provider : Provider State Element Resource Unwind Terminal} {count : Nat}
    {evaluate : Callback.Run State Nat Element Unwind Terminal}
    {values finalValues : List Element} {before after : State}
    (execution : PrefixTrace provider count evaluate values before finalValues after) :
    ∃ extra, finalValues = values ++ extra := by
  induction execution with
  | stop values state => exact ⟨[], (List.append_nil values).symm⟩
  | again values finalValues before middle after work rest induction => exact induction
  | next values finalValues before ready middle after value bound work expression rest induction =>
    obtain ⟨extra, result⟩ := induction
    exact ⟨value :: extra, by simpa only [List.append_assoc, List.singleton_append] using result⟩

/-- Every returned construction decomposes into its exact indexed expression
trace and one actual completion. Unwind cleanup cannot masquerade as success. -/
theorem Trace.returned_decomposition {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    {provider : Provider State Element Resource Unwind Terminal} {count : Nat}
    {evaluate : Callback.Run State Nat Element Unwind Terminal}
    {values : List Element} {before : State}
    {outcome : Outcome State Resource (Failure × Unwind) Terminal}
    (execution : Trace provider count evaluate values before outcome)
    {resource : Resource} {after : State} (returned : outcome = .returned resource after) :
    ∃ finalValues ready completing,
      PrefixTrace provider count evaluate values before finalValues ready ∧
      finalValues.length = count ∧
      provider.work ready (count, finalValues) (.returned .finish completing) ∧
      provider.finish completing finalValues (.returned resource after) := by
  induction execution generalizing resource after with
  | again values before middle outcome work rest induction =>
    obtain ⟨finalValues, ready, completing, trace, complete, workFinish, finish⟩ := induction
      returned
    exact ⟨finalValues, ready, completing,
      .again values finalValues before middle ready work trace, complete, workFinish, finish⟩
  | next values before ready middle value outcome bound work expression rest induction =>
    obtain ⟨finalValues, last, completing, trace, complete, workFinish, finish⟩ := induction
      returned
    exact ⟨finalValues, last, completing,
      .next values finalValues before ready middle last value bound work expression trace,
      complete, workFinish, finish⟩
  | workUnwind values before middle reason outcome work closed =>
    rw [returned] at closed
    exact False.elim (provider.close_ne_returned values .work middle reason resource after closed)
  | workTerminal => cases returned
  | evaluateUnwind values before ready middle reason outcome bound work expression closed =>
    rw [returned] at closed
    exact False.elim (provider.close_ne_returned values .evaluate middle reason resource after
      closed)
  | evaluateTerminal => cases returned
  | finishReturn values before ready middle result complete work finished =>
    cases returned
    exact ⟨values, before, ready, .stop values before, complete, work, finished⟩
  | finishUnwind values before ready middle reason outcome complete work finished closed =>
    rw [returned] at closed
    exact False.elim (provider.close_ne_returned values .finish middle reason resource after closed)
  | finishTerminal => cases returned

/-- Append actual completion to an exact normal prefix. -/
theorem PrefixTrace.finish {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    {provider : Provider State Element Resource Unwind Terminal} {count : Nat}
    {evaluate : Callback.Run State Nat Element Unwind Terminal}
    {values finalValues : List Element} {before ready completing after : State}
    {resource : Resource}
    (execution : PrefixTrace provider count evaluate values before finalValues ready)
    (complete : finalValues.length = count)
    (work : provider.work ready (count, finalValues) (.returned .finish completing))
    (finished : provider.finish completing finalValues (.returned resource after)) :
    Trace provider count evaluate values before (.returned resource after) := by
  induction execution with
  | stop => exact .finishReturn _ _ _ _ _ complete work finished
  | again values finalValues before middle last workChunk rest induction =>
    exact .again values before middle _ workChunk (induction complete work finished)
  | next values finalValues before ready middle last value bound workChunk expression rest
    induction =>
    exact .next values before ready middle value _ bound workChunk expression
      (induction complete work finished)

/-- Success exposes the exact ordered returned values and current vector
resource, under the local current-content law of the completion dependency. -/
theorem Provider.run_returned_current {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    {provider : Provider State Element Resource Unwind Terminal}
    {vectors : VectorOps State Element Resource Unwind Terminal}
    (law : provider.CurrentLaw vectors) {count : Nat}
    {evaluate : Callback.Run State Nat Element Unwind Terminal}
    {before after : State} {resource : Resource}
    (execution : provider.run count evaluate before (.returned resource after)) :
    ∃ values ready,
      PrefixTrace provider count evaluate [] before values ready ∧
      values.length = count ∧ vectors.current after resource = some values := by
  obtain ⟨detailed, trace, result⟩ := execution
  cases detailed with
  | returned actual actualState =>
    cases result
    obtain ⟨values, ready, completing, ordered, complete, _, finished⟩ :=
      trace.returned_decomposition rfl
    exact ⟨values, ready, ordered, complete, law.finish_current _ _ _ _ finished⟩
  | unwound => cases result
  | terminated => cases result

end Solanalib.Specs.Core.Owned.Array
