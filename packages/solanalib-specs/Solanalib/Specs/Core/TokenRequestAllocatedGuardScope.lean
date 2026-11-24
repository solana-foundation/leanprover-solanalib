/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedGuard

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedGuard

open AccountInfo.GuardCallback

/-- Protocol-only changes frame a retained guard when they keep its exact
token and every current cell. This helper adds no permission to mutate cells. -/
theorem stateFrame_of_cells {before after : AccountInfo.State} {guard : Borrow.Guard}
    (valid : after.Valid) (history : Borrow.History before after)
    (cells : after.cells = before.cells) (held : after.resolve guard = before.resolve guard) :
    StateFrame before after guard := by
  refine ⟨valid, history, ?_, held, ?_⟩
  · intro handle old present
    exact ⟨old, by simpa only [Borrow.State.lookupCell, cells] using present, rfl⟩
  · intro slot old next _ oldFound nextFound
    have inBefore : before.lookupCell slot.cell = some next := by
      simpa only [Borrow.State.lookupCell, cells] using nextFound
    have same : next = old := Option.some.inj (inBefore.symm.trans oldFound)
    cases same
    rfl

/-- Distinct simultaneously live tokens necessarily have distinct guard ids;
two generations of one id cannot both be live. -/
theorem live_ids_distinct {state : AccountInfo.State} {one two : Borrow.Guard}
    {first second : Borrow.Slot AccountInfo.View}
    (liveOne : state.resolve one = some first) (liveTwo : state.resolve two = some second)
    (different : one ≠ two) : one.id ≠ two.id := by
  intro sameId
  have firstFacts := Borrow.State.resolve_some_iff.mp liveOne
  have secondFacts := Borrow.State.resolve_some_iff.mp liveTwo
  have sameSlot : first = second := Option.some.inj
    (firstFacts.1.symm.trans (sameId ▸ secondFacts.1))
  have sameGeneration : one.generation = two.generation :=
    firstFacts.2.symm.trans (sameSlot ▸ secondFacts.2)
  apply different
  cases one
  cases two
  cases sameId
  cases sameGeneration
  rfl

/-- Releasing an owned inner guard preserves any distinct live outer guard.
The consumed guard is not silently resurrected or exempted by cell aliasing. -/
theorem release_other {before : AccountInfo.State} {held released : Borrow.Guard}
    {slot : Borrow.Slot AccountInfo.View} (valid : before.Valid)
    (live : before.resolve held = some slot) (different : held ≠ released) :
    StateFrame before (Borrow.release before released).2 held := by
  apply stateFrame_of_cells (Borrow.release_valid valid released)
    (Borrow.release_history before released) (Borrow.release_cells before released)
  cases found : before.resolve released with
  | none => simp only [Borrow.release, found]
  | some owned =>
    have ids := live_ids_distinct live found different
    simp only [Borrow.release_live found, Borrow.State.resolve, Borrow.State.lookupSlot,
      List.getElem?_set_ne (Ne.symm ids)]

/-- A fresh local borrow retains every preexisting guard. The actual acquire
operation, including its checked errors, supplies the protocol transition. -/
theorem acquire_other {before : AccountInfo.State} {guard : Borrow.Guard}
    {slot : Borrow.Slot AccountInfo.View} (valid : before.Valid)
    (live : before.resolve guard = some slot) (handle : Borrow.Handle)
    (mode : Borrow.Mode) (view : AccountInfo.View) :
    StateFrame before (Borrow.acquire before handle mode view).2 guard := by
  have old := Borrow.State.lookupSlot_bound (Borrow.State.resolve_some_iff.mp live).1
  have retained (selected : Borrow.Mode) :
      (before.issue handle selected view).2.resolve guard = before.resolve guard := by
    simp only [Borrow.State.resolve, Borrow.State.issue_lookup_old before handle selected view old]
  apply stateFrame_of_cells (Borrow.acquire_valid valid handle mode view)
    (Borrow.acquire_history before handle mode view)
  · unfold Borrow.acquire
    split
    · rfl
    · cases mode <;> simp only <;> split
      all_goals first | rfl | (split <;> rfl)
  · unfold Borrow.acquire
    split
    · rfl
    · cases mode <;> simp only <;> split
      all_goals first | rfl | exact retained _ | (split <;> first | rfl | exact retained _)

/-- The singleton source DataRef destructor is exactly checked release of the
pending outcome. Ordinary errors and unwinds keep their reasons and effects;
termination bypasses the destructor. Invalid guard cleanup stays undefined. -/
theorem data_cleanup_iff {Extra Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind (World Extra) Unwind Terminal)
    (reference : AllocatedControl.DataRef)
    (pending final : Outcome (World Extra) Value Unwind Terminal) :
    Owned.cleanup double [reference.drop] pending final ↔
      releaseOutcome reference.guard pending = some final := by
  cases pending with
  | terminated reason =>
    simp only [Owned.cleanup, releaseOutcome, Option.some.injEq, eq_comm]
  | returned value state =>
    cases released : Borrow.release state.1 reference.guard with
    | mk result after =>
      cases result with
      | error error => simp only [Owned.cleanup, AllocatedControl.DataRef.drop,
          releaseOutcome, released, false_and, exists_false, reduceCtorEq]
      | ok done =>
        cases done
        simp only [Owned.cleanup, AllocatedControl.DataRef.drop, releaseOutcome,
          released, exists_eq_left, Option.some.injEq, eq_comm]
  | unwound reason state =>
    cases released : Borrow.release state.1 reference.guard with
    | mk result after =>
      cases result with
      | error error => simp only [Owned.cleanup, AllocatedControl.DataRef.drop,
          releaseOutcome, released, false_and, exists_false, reduceCtorEq]
      | ok done =>
        cases done
        simp only [Owned.cleanup, AllocatedControl.DataRef.drop, releaseOutcome,
          released, exists_eq_left, Option.some.injEq, eq_comm]

/-- Raw Token scope cleanup is the common checked guard scope; neither side
filters a callback by a frame postcondition. -/
theorem data_scope_iff {Extra Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind (World Extra) Unwind Terminal)
    (reference : AllocatedControl.DataRef)
    (body : AllocatedControl.Run (World Extra) Value Unwind Terminal)
    (before : World Extra) (final : Outcome (World Extra) (Except Error Value) Unwind Terminal) :
    AllocatedControl.scope double [reference.drop] body before final ↔
      withGuard reference.guard (fun state (_ : Unit) => body state) before () final := by
  simp only [AllocatedControl.scope, withGuard, data_cleanup_iff]

/-- From primitive-derived admission, every real body exit has a real checked
scope exit. This theorem assumes a supplied exit, not callback termination. -/
theorem data_scope_retains {Extra Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind (World Extra) Unwind Terminal)
    {reference : AllocatedControl.DataRef}
    {body : AllocatedControl.Run (World Extra) Value Unwind Terminal}
    {before : World Extra} {slot : Borrow.Slot AccountInfo.View}
    {pending : Outcome (World Extra) (Except Error Value) Unwind Terminal}
    (admitted : Admissible reference.guard (fun state (_ : Unit) => body state) before ())
    (live : before.1.resolve reference.guard = some slot) (run : body before pending) :
    ∃ final, releaseOutcome reference.guard pending = some final ∧
      AllocatedControl.scope double [reference.drop] body before final := by
  obtain ⟨final, released, scopeRun⟩ := admitted.retain live run
  exact ⟨final, released, (data_scope_iff double reference body before final).mpr scopeRun⟩

/-- A real primitive return is followed by a current read in its actual
after-state; a real abnormal exit passes through unchanged. Admission proves
the read cannot disappear because that primitive invalidated the held guard. -/
theorem perform_read_retains {Extra Args Value Unwind Terminal : Type}
    {call : Callback.Run (World Extra) Args Value Unwind Terminal}
    (law : Preserves call) {before : World Extra} {args : Args}
    {reference : AllocatedControl.DataRef} {bytes : Bytes}
    (valid : before.1.Valid) (read : reference.read before = some bytes)
    {pending : Outcome (World Extra) Value Unwind Terminal} (called : call before args pending) :
    ∃ final, AllocatedControl.bind
      (AllocatedControl.perform (fun state => call state args))
      (fun _ => AllocatedControl.inspect reference.read) before final ∧
      Frame before reference.guard final := by
  obtain ⟨slot, _, live, _⟩ := read_live read
  have frame := law before args valid reference.guard slot live (by simp) pending called
  cases pending with
  | returned value after =>
    refine ⟨.returned (.ok bytes) after, ?_, frame⟩
    exact ⟨.returned (.ok value) after, ⟨.returned value after, called, rfl⟩,
      bytes, read_preserved read frame, rfl⟩
  | unwound reason after =>
    exact ⟨.unwound reason after,
      ⟨.unwound reason after, ⟨.unwound reason after, called, rfl⟩, rfl⟩, frame⟩
  | terminated reason =>
    exact ⟨.terminated reason,
      ⟨.terminated reason, ⟨.terminated reason, called, rfl⟩, rfl⟩, trivial⟩

/-- A primitive followed by a reference read and release retains every actual
finite primitive exit. It does not require any complete enclosing-body exit. -/
theorem perform_read_scope_retains {Extra Args Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind (World Extra) Unwind Terminal)
    {call : Callback.Run (World Extra) Args Value Unwind Terminal}
    (law : Preserves call) {before : World Extra} {args : Args}
    {reference : AllocatedControl.DataRef} {bytes : Bytes}
    (valid : before.1.Valid) (read : reference.read before = some bytes)
    {pending : Outcome (World Extra) Value Unwind Terminal} (called : call before args pending) :
    ∃ observed final, AllocatedControl.bind
        (AllocatedControl.perform (fun state => call state args))
        (fun _ => AllocatedControl.inspect reference.read) before observed ∧
      releaseOutcome reference.guard observed = some final ∧
      AllocatedControl.scope double [reference.drop]
        (AllocatedControl.bind (AllocatedControl.perform (fun state => call state args))
          (fun _ => AllocatedControl.inspect reference.read)) before final := by
  obtain ⟨observed, readRun, frame⟩ := perform_read_retains law valid read called
  obtain ⟨slot, _, live, _⟩ := read_live read
  obtain ⟨final, released⟩ := frame.release_exists live
  exact ⟨observed, final, readRun, released,
    observed, readRun, (data_cleanup_iff double reference observed final).mpr released⟩

/-- The local destructor may retire its one actual owned token. Every distinct
live token, even an alias of the same data cell, survives that real release. -/
theorem data_drop_frames {Extra Unwind Terminal : Type}
    (reference : AllocatedControl.DataRef) :
    PreservesExcept (fun (_ : World Extra) (_ : Unit) => [reference.guard])
      (fun state (_ : Unit) => reference.drop (Unwind := Unwind) (Terminal := Terminal) state) := by
  intro before _ valid guard slot live outside outcome dropped
  have different : guard ≠ reference.guard := by simpa only [List.mem_singleton] using outside
  unfold AllocatedControl.DataRef.drop at dropped
  cases actual : Borrow.release before.1 reference.guard with
  | mk result after =>
    cases result with
    | error _ => simp only [actual] at dropped
    | ok done =>
      cases done
      simp only [actual] at dropped
      cases dropped
      change StateFrame before.1 after guard
      simpa only [actual] using release_other valid live different

/-- Source-ordered cleanup composes the pointwise frames of its actual drop
calls. These are primitive laws before each call, not a postcondition filter
on the complete cleanup trace. A second unwind retains its terminal policy. -/
theorem cleanup_frame {Extra Value Unwind Terminal : Type}
    {before : World Extra} {guard : Borrow.Guard} {slot : Borrow.Slot AccountInfo.View}
    (live : before.1.resolve guard = some slot)
    (double : Owned.DoubleUnwind (World Extra) Unwind Terminal)
    (drops : List (Owned.DropAction (World Extra) Unwind Terminal))
    (laws : ∀ drop ∈ drops, ∀ state, state.1.Valid → ∀ current,
      state.1.resolve guard = some current →
        Admissible guard (fun currentState (_ : Unit) => drop currentState) state ())
    {pending final : Outcome (World Extra) Value Unwind Terminal}
    (framed : Frame before guard pending)
    (cleaned : Owned.cleanup double drops pending final) : Frame before guard final := by
  induction drops generalizing pending with
  | nil => cases cleaned; exact framed
  | cons drop rest induction =>
    have headLaw := laws drop (by simp)
    have restLaws : ∀ action ∈ rest, ∀ state, state.1.Valid → ∀ current,
        state.1.resolve guard = some current →
          Admissible guard (fun currentState (_ : Unit) => action currentState) state () := by
      intro action member
      exact laws action (by simp only [List.mem_cons]; exact Or.inr member)
    cases pending with
    | returned value state =>
      obtain ⟨dropped, called, continued⟩ := cleaned
      have next := headLaw state framed.valid slot (framed.resolve live) dropped called
      cases dropped with
      | returned done after =>
        cases done
        exact induction restLaws (Frame.prepend framed next) continued
      | unwound reason after =>
        exact induction restLaws (Frame.prepend framed next) continued
      | terminated reason => cases continued; trivial
    | unwound original state =>
      obtain ⟨dropped, called, continued⟩ := cleaned
      have next := headLaw state framed.valid slot (framed.resolve live) dropped called
      cases dropped with
      | returned done after =>
        cases done
        exact induction restLaws (Frame.prepend framed next) continued
      | unwound reason after =>
        obtain ⟨terminal, _, same⟩ := continued
        cases same
        trivial
      | terminated reason => cases continued; trivial
    | terminated reason => cases cleaned; trivial

end Solanalib.Specs.Core.Token.AllocatedGuard
