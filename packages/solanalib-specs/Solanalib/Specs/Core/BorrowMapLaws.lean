/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorrowMap

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borrow

universe u v w x y z a

variable {Content : Type u} {View : Type v} {Aux : Type w}
variable {Failure : Type x} {Unwind : Type y} {Terminal : Type z} {Value : Type a}

/-- A convenient callback frame for effects that leave all guard slots unchanged.
The footprint premise still accounts for the actual mutations of the held cell. -/
theorem CallbackFrame.of_slots {footprint : Footprint Content View}
    {before after : State Content View} {guard : Guard}
    (valid : after.Valid) (slots : after.slots = before.slots)
    (policies : ∀ handle, (after.lookupCell handle).map Cell.policy =
      (before.lookupCell handle).map Cell.policy)
    (changes : ∀ slot old next, before.resolve guard = some slot →
      before.lookupCell slot.cell = some old → after.lookupCell slot.cell = some next →
      footprint slot.mode slot.view old.value next.value) :
    CallbackFrame footprint before after guard := by
  refine ⟨valid, History.of_slots_eq slots, ?_, ?_, changes⟩
  · intro handle old present
    have policy := policies handle
    cases found : after.lookupCell handle with
    | none => simp [found, present] at policy
    | some cell =>
      refine ⟨cell, rfl, ?_⟩
      simpa [found, present] using policy
  · simp [State.resolve, State.lookupSlot, slots]

/-- A no-effect callback is admissible whenever its footprint admits equality. -/
theorem CallbackFrame.refl (state : State Content View) (guard : Guard)
    (valid : state.Valid) (footprint : Footprint Content View)
    (same : ∀ mode view value, footprint mode view value value) :
    CallbackFrame footprint state state guard := by
  apply CallbackFrame.of_slots valid rfl (fun _ => rfl)
  intro slot old next live oldFound nextFound
  have equal : old = next := by rw [oldFound] at nextFound; cases nextFound; rfl
  subst next
  exact same slot.mode slot.view old.value

/-- A transferred guard reads its chosen descriptor from the current cell value. -/
theorem transfer_current {state : State Content View} {guard : Guard} {slot : Slot View}
    {cell : Cell Content} (live : state.resolve guard = some slot)
    (present : state.lookupCell slot.cell = some cell) (view : View) :
    current (transfer state guard view).2 ⟨guard.id, guard.generation + 1⟩ =
      .ok (view, cell.value) := by
  have found : (transfer state guard view).2.lookupCell slot.cell = some cell := by
    simpa [State.lookupCell, transfer_cells] using present
  simp [current, transfer_resolves live view, found]

/-- Source-bound unwind cleanup retains the borrow invariant. -/
theorem unwindState_valid (policy : UnwindPolicy) {state : State Content View}
    (valid : state.Valid) (guard : Guard) (original : View) :
    (unwindState policy state guard original).Valid := by
  cases policy
  · exact release_valid valid guard
  · exact transfer_valid valid guard original

/-- Source-bound unwind cleanup also preserves all previously retired tokens. -/
theorem unwindState_history (policy : UnwindPolicy) (state : State Content View)
    (guard : Guard) (original : View) : History state (unwindState policy state guard original) :=
      by
  cases policy
  · exact release_history state guard
  · exact transfer_history state guard original

/-- Every state-carrying finite exit satisfies the live-lease invariant. -/
def ValidExit (outcome : Outcome (World Content View Aux) Value Unwind Terminal) : Prop :=
  match outcome with
  | .returned _ after | .unwound _ after => after.1.Valid
  | .terminated _ => True

/-- The actual state of an exit preserves the earlier token history. -/
def HistoryExit (before : State Content View)
    (outcome : Outcome (World Content View Aux) Value Unwind Terminal) : Prop :=
  match outcome with
  | .returned _ after | .unwound _ after => History before after.1
  | .terminated _ => True

/-- Normal and unwinding completion retain validity from the state of the callback. -/
theorem finishTryMap_valid {footprint : Footprint Content View} {before : State Content View}
    {guard : Guard} {produced : Outcome (World Content View Aux) (Except Failure View) Unwind
      Terminal}
    (admissible : CallbackAdmissible footprint before guard produced)
    (policy : UnwindPolicy) (original : View) :
    ValidExit (finishTryMap policy guard original produced) := by
  cases produced with
  | returned result after =>
    cases result <;>
      exact transfer_valid admissible.valid guard _
  | unwound reason after => exact unwindState_valid policy admissible.valid guard original
  | terminated reason => trivial

/-- Normal and unwinding completion compose the admitted token history of the callback. -/
theorem finishTryMap_history {footprint : Footprint Content View} {before : State Content View}
    {guard : Guard} {produced : Outcome (World Content View Aux) (Except Failure View) Unwind
      Terminal}
    (admissible : CallbackAdmissible footprint before guard produced)
    (policy : UnwindPolicy) (original : View) :
    HistoryExit before (finishTryMap policy guard original produced) := by
  cases produced with
  | returned result after =>
    cases result <;>
      exact admissible.history.trans (transfer_history after.1 guard _)
  | unwound reason after =>
    exact admissible.history.trans (unwindState_history policy after.1 guard original)
  | terminated reason => trivial

/-- With universal callback admission as an explicit precondition, every finite
mapping exit from a valid input is a valid state or a terminal exit. -/
theorem tryMap_valid {policy : UnwindPolicy} {footprint : Footprint Content View}
    {callback : MapCallback Content View Aux Failure Unwind Terminal}
    {before : World Content View Aux} {guard : Guard}
    {outcome : Outcome (World Content View Aux) (TryMapResult Failure) Unwind Terminal}
    (valid : before.1.Valid)
    (admissible : MapCallback.Admissible footprint callback before guard)
    (step : tryMap policy callback before guard outcome) :
    ValidExit outcome := by
  cases live : before.1.resolve guard with
  | none =>
    simp only [tryMap, live] at step
    cases step
    exact valid
  | some slot =>
    cases present : before.1.lookupCell slot.cell with
    | none =>
      simp only [tryMap, live, present] at step
      cases step
      exact valid
    | some cell =>
      simp only [tryMap, live, present] at step
      obtain ⟨produced, called, rfl⟩ := step
      exact finishTryMap_valid (admissible slot cell live present produced called) policy _

/-- An admitted callback and source-bound cleanup cannot revive an earlier
consumed token. The universal frame premise is not inferred from the execution. -/
theorem tryMap_history {policy : UnwindPolicy} {footprint : Footprint Content View}
    {callback : MapCallback Content View Aux Failure Unwind Terminal}
    {before : World Content View Aux} {guard : Guard}
    {outcome : Outcome (World Content View Aux) (TryMapResult Failure) Unwind Terminal}
    (admissible : MapCallback.Admissible footprint callback before guard)
    (step : tryMap policy callback before guard outcome) : HistoryExit before.1 outcome := by
  cases live : before.1.resolve guard with
  | none =>
    simp only [tryMap, live] at step
    cases step
    exact History.refl before.1
  | some slot =>
    cases present : before.1.lookupCell slot.cell with
    | none =>
      simp only [tryMap, live, present] at step
      cases step
      exact History.refl before.1
    | some cell =>
      simp only [tryMap, live, present] at step
      obtain ⟨produced, called, rfl⟩ := step
      exact finishTryMap_history (admissible slot cell live present produced called) policy _

/-- Any normal mapping completion consumes the original input token, including
the callback-error branch that returns a replacement for the same view. -/
theorem finish_return_retired {footprint : Footprint Content View}
    {before after : State Content View} {guard : Guard} {slot : Slot View}
    (frame : CallbackFrame footprint before after guard)
    (live : before.resolve guard = some slot) (result : Except Failure View) :
    Retired (transfer after guard (match result with | .ok view => view | .error _ => slot.view)).2
      guard := transfer_retired (frame.resolve live) _

end Solanalib.Specs.Core.Borrow
