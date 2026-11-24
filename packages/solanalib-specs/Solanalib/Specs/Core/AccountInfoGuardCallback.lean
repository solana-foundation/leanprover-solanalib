/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfo
public import Solanalib.Specs.Core.BorrowMapLaws
public import Solanalib.Specs.Core.Callback

/-!
Callback admission for an AccountInfo data guard held by its caller. The raw
callback and cleanup relations do not test this admission or erase a finite
exit for violating it. A source interpretation supplies the universal law at
each actual callback input, before dependent reads or guard cleanup.

Checked cleanup remains partial on an invalid guard. That is an invalid model
representation, not a source error or a fabricated destructor. The laws below
prove cleanup exists for every exit of an admitted callback at a live guard.
-/

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountInfo.GuardCallback

/-- AccountInfo changes only the diagnostic of an acquisition error. A successful
result is exactly the common guard acquisition, including its current state. -/
theorem tryBorrow_acquire {state during : State} {handle : Borrow.Handle}
    {mode : Borrow.Mode} {guard : Borrow.Guard}
    (acquired : tryBorrow mode handle state = (.ok guard, during)) :
    Borrow.acquire state handle mode View.whole = (.ok guard, during) := by
  cases raw : Borrow.acquire state handle mode View.whole with
  | mk result after =>
    cases result with
    | error failure => simp [tryBorrow, raw, Except.mapError] at acquired
    | ok token =>
      simpa only [tryBorrow, raw, Except.mapError, Prod.mk.injEq, Except.ok.injEq] using acquired

/-- A successful data-borrow token is live at exactly the selected cell and mode. -/
theorem tryBorrow_live {state during : State} {handle : Borrow.Handle}
    {mode : Borrow.Mode} {guard : Borrow.Guard}
    (acquired : tryBorrow mode handle state = (.ok guard, during)) :
    during.resolve guard = some ⟨handle, mode, 0, .whole⟩ :=
  (Borrow.acquire_success (tryBorrow_acquire acquired)).1

/-- Borrowing preserves the common protocol invariant on every checked branch. -/
theorem tryBorrow_valid {state : State} (valid : state.Valid)
    (mode : Borrow.Mode) (handle : Borrow.Handle) : (tryBorrow mode handle state).2.Valid :=
  Borrow.acquire_valid valid handle mode View.whole

/-- A present data cell supplies its current bytes after successful acquisition;
no condition on the unrelated lamports cell or source profile is needed. -/
theorem data_current {state during : State} {info : AccountInfo.Value}
    {mode : Borrow.Mode} {guard : Borrow.Guard}
    (typed : ∃ bytes policy, state.lookupCell info.data = some ⟨.data bytes, policy⟩)
    (acquired : tryBorrow mode info.data state = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) := by
  obtain ⟨bytes, policy, present⟩ := typed
  exact ⟨bytes, Borrow.acquire_current (tryBorrow_acquire acquired) present⟩

/-- A protocol-valid state with the same current cells retains the typing and target-width premises
of AccountInfo. Guard history may have advanced. -/
theorem valid_of_cells {before after : State} {profile : Profile} {info : AccountInfo.Value}
    (valid : Valid profile before info) (afterValid : after.Valid)
    (cells : after.cells = before.cells) : Valid profile after info := by
  refine ⟨valid.1, afterValid, valid.2.2.1, ?_, ?_⟩
  · simpa only [Borrow.State.lookupCell, cells] using valid.2.2.2.1
  · simpa only [Borrow.State.lookupCell, cells] using valid.2.2.2.2

/-- AccountInfo cells together with arbitrary captured state. -/
abbrev World (Aux : Type) := Borrow.World Content View Aux

/-- A caller-held data guard protects its current contents. Other cells and
captured state may change during a dependency call. -/
def footprint : Borrow.Footprint Content View := fun _ _ before after => after = before

/-- Protocol history, cell policies, the exact held token, and its current
contents survive a state-bearing callback exit. -/
abbrev StateFrame (before after : State) (guard : Borrow.Guard) :=
  Borrow.CallbackFrame footprint before after guard

/-- A callback that leaves the borrow store unchanged meets the frame. -/
theorem StateFrame.refl (state : State) (guard : Borrow.Guard) (valid : state.Valid) :
    StateFrame state state guard :=
  Borrow.CallbackFrame.refl state guard valid footprint (fun _ _ _ => rfl)

/-- Actual callback frames compose; no assumption about a later outcome is
used to excuse an earlier callback that invalidates the held guard. -/
theorem StateFrame.trans {first middle last : State} {guard : Borrow.Guard}
    (one : StateFrame first middle guard) (two : StateFrame middle last guard) :
    StateFrame first last guard := by
  refine ⟨two.valid, one.history.trans two.history, ?_, two.held.trans one.held, ?_⟩
  · intro handle old present
    obtain ⟨intermediate, found, policy⟩ := one.cells handle old present
    obtain ⟨next, nextFound, nextPolicy⟩ := two.cells handle intermediate found
    exact ⟨next, nextFound, nextPolicy.trans policy⟩
  · intro slot old next live oldFound nextFound
    obtain ⟨intermediate, found, _⟩ := one.cells slot.cell old oldFound
    exact (two.changes slot intermediate next (one.resolve live) found nextFound).trans
      (one.changes slot old intermediate live oldFound found)

/-- Each returned or unwound exit carries its actual frame. A terminal exit
has no post-state to constrain and never acquires an invented one. -/
def Frame {Aux Value Unwind Terminal : Type} (before : World Aux) (guard : Borrow.Guard)
    (outcome : Outcome (World Aux) Value Unwind Terminal) : Prop :=
  match outcome with
  | .returned _ after | .unwound _ after => StateFrame before.1 after.1 guard
  | .terminated _ => True

/-- Admission quantifies every finite exit at this exact call input. It is a
precondition on the provider, not a restriction on the operational relation.
It neither assumes nor manufactures a callback outcome. -/
def Admissible {Aux Args Value Unwind Terminal : Type} (guard : Borrow.Guard)
    (run : Callback.Run (World Aux) Args Value Unwind Terminal)
    (before : World Aux) (args : Args) : Prop :=
  ∀ outcome, run before args outcome → Frame before guard outcome

/-- Mapping only a return value leaves the frame unchanged on every exit. -/
theorem Frame.map {Aux Value Next Unwind Terminal : Type} (f : Value → Next)
    {before : World Aux} {guard : Borrow.Guard}
    {outcome : Outcome (World Aux) Value Unwind Terminal}
    (frame : Frame before guard outcome) : Frame before guard (Outcome.map f outcome) := by
  cases outcome <;> exact frame

/-- A preceding state frame composes with any later framed finite exit. -/
theorem Frame.prepend {Aux Value Unwind Terminal : Type}
    {before middle : World Aux} {guard : Borrow.Guard}
    {outcome : Outcome (World Aux) Value Unwind Terminal}
    (first : StateFrame before.1 middle.1 guard)
    (next : Frame middle guard outcome) : Frame before guard outcome := by
  cases outcome with
  | returned _ _ => exact StateFrame.trans first next
  | unwound _ _ => exact StateFrame.trans first next
  | terminated _ => trivial

/-- Return-value mapping preserves universal callback admission. -/
theorem Admissible.map {Aux Args Value Next Unwind Terminal : Type} (f : Value → Next)
    {guard : Borrow.Guard} {run : Callback.Run (World Aux) Args Value Unwind Terminal}
    {before : World Aux} {args : Args} (admitted : Admissible guard run before args) :
    Admissible guard (Callback.map f run) before args := by
  rintro outcome ⟨produced, called, rfl⟩
  exact (admitted produced called).map f

/-- A bind is admitted by framing the first callback at its actual input and
the continuation at every actual returned input. The first premise still
applies if a dependent read in the continuation has no outcome. -/
theorem Admissible.bind {Aux Args Value Next Unwind Terminal : Type}
    {guard : Borrow.Guard} {run : Callback.Run (World Aux) Args Value Unwind Terminal}
    {next : Value → World Aux → Outcome (World Aux) Next Unwind Terminal → Prop}
    {before : World Aux} {args : Args}
    (first : Admissible guard run before args)
    (continuations : ∀ value after, run before args (.returned value after) →
      Admissible guard (fun state (_ : Unit) => next value state) after ()) :
    Admissible guard (Callback.bind run next) before args := by
  rintro outcome ⟨produced, called, continued⟩
  have frame := first produced called
  cases produced with
  | returned value after =>
    exact Frame.prepend frame (continuations value after called outcome continued)
  | unwound reason after => cases continued; exact frame
  | terminated reason => cases continued; trivial

/-- Checked source-local cleanup acts on the actual exit state of the dependency.
An invalid token yields no interpreted destructor, rather than rolling back
effects or inventing successful cleanup. -/
def releaseOutcome {Aux Value Unwind Terminal : Type} (guard : Borrow.Guard) :
    Outcome (World Aux) Value Unwind Terminal →
      Option (Outcome (World Aux) Value Unwind Terminal)
  | .returned value after => match Borrow.release after.1 guard with
    | (.ok (), released) => some (.returned value (released, after.2))
    | (.error _, _) => none
  | .unwound reason after => match Borrow.release after.1 guard with
    | (.ok (), released) => some (.unwound reason (released, after.2))
    | (.error _, _) => none
  | .terminated reason => some (.terminated reason)

/-- The raw local scope retains every callback exit whose actual guard can be
released. Frame admission belongs to the precondition of its caller. -/
def withGuard {Aux Args Value Unwind Terminal : Type} (guard : Borrow.Guard)
    (run : Callback.Run (World Aux) Args Value Unwind Terminal) :
    Callback.Run (World Aux) Args Value Unwind Terminal :=
  fun before args outcome => ∃ produced,
    run before args produced ∧ releaseOutcome guard produced = some outcome

/-- A normal return, including an ordinary error value, releases the live
guard and keeps the complete current cells and auxiliary effects of the callback. -/
theorem releaseOutcome_returned {Aux Value Unwind Terminal : Type}
    {guard : Borrow.Guard} {slot : Borrow.Slot View} {after : World Aux}
    (live : after.1.resolve guard = some slot) (value : Value) :
    releaseOutcome (Unwind := Unwind) (Terminal := Terminal) guard (.returned value after) =
      some (.returned value ((Borrow.release after.1 guard).2, after.2)) := by
  simp only [releaseOutcome, Borrow.release_live live]

/-- Unwinding releases a live guard in the actual unwind state and retains the
original unwind reason. This release cannot supply a second unwind. -/
theorem releaseOutcome_unwound {Aux Value Unwind Terminal : Type}
    {guard : Borrow.Guard} {slot : Borrow.Slot View} {after : World Aux}
    (live : after.1.resolve guard = some slot) (reason : Unwind) :
    releaseOutcome (Value := Value) (Terminal := Terminal) guard (.unwound reason after) =
      some (.unwound reason ((Borrow.release after.1 guard).2, after.2)) := by
  simp only [releaseOutcome, Borrow.release_live live]

/-- Termination passes through exactly, with no state or cleanup event. -/
theorem releaseOutcome_terminated {Aux Value Unwind Terminal : Type}
    (guard : Borrow.Guard) (reason : Terminal) :
    releaseOutcome (Aux := Aux) (Value := Value) (Unwind := Unwind) guard
      (.terminated reason) = some (.terminated reason) := rfl

/-- A live input and a framed finite exit suffice for actual checked cleanup.
This consumes admission to rule out an empty local scope after a real exit. -/
theorem Frame.release_exists {Aux Value Unwind Terminal : Type}
    {before : World Aux} {guard : Borrow.Guard} {slot : Borrow.Slot View}
    {produced : Outcome (World Aux) Value Unwind Terminal}
    (live : before.1.resolve guard = some slot) (frame : Frame before guard produced) :
    ∃ outcome, releaseOutcome guard produced = some outcome := by
  cases produced with
  | returned value after => exact ⟨_, releaseOutcome_returned (frame.resolve live) value⟩
  | unwound reason after => exact ⟨_, releaseOutcome_unwound (frame.resolve live) reason⟩
  | terminated reason => exact ⟨.terminated reason, rfl⟩

/-- Raw retention requires only the real callback exit and checked cleanup;
even a footprint violation remains observable when the guard is still live. -/
theorem withGuard_of_callback {Aux Args Value Unwind Terminal : Type}
    {guard : Borrow.Guard} {run : Callback.Run (World Aux) Args Value Unwind Terminal}
    {before : World Aux} {args : Args}
    {produced outcome : Outcome (World Aux) Value Unwind Terminal}
    (called : run before args produced) (released : releaseOutcome guard produced = some outcome) :
    withGuard guard run before args outcome := ⟨produced, called, released⟩

/-- At an admitted live input every actual finite callback exit has an exact
scope exit. No existence assumption replaces the supplied callback execution. -/
theorem Admissible.retain {Aux Args Value Unwind Terminal : Type}
    {guard : Borrow.Guard} {run : Callback.Run (World Aux) Args Value Unwind Terminal}
    {before : World Aux} {args : Args} {slot : Borrow.Slot View}
    (admitted : Admissible guard run before args) (live : before.1.resolve guard = some slot)
    {produced : Outcome (World Aux) Value Unwind Terminal} (called : run before args produced) :
    ∃ outcome, releaseOutcome guard produced = some outcome ∧ withGuard guard run before args
      outcome := by
  obtain ⟨outcome, released⟩ := (admitted produced called).release_exists live
  exact ⟨outcome, released, withGuard_of_callback called released⟩

/-- With explicit live-guard admission, a scope has a finite exit exactly when
the invoked callback does. Termination and ordinary errors are included. -/
theorem Admissible.hasOutcome_iff {Aux Args Value Unwind Terminal : Type}
    {guard : Borrow.Guard} {run : Callback.Run (World Aux) Args Value Unwind Terminal}
    {before : World Aux} {args : Args} {slot : Borrow.Slot View}
    (admitted : Admissible guard run before args) (live : before.1.resolve guard = some slot) :
    (∃ outcome, withGuard guard run before args outcome) ↔ ∃ produced, run before args produced :=
      by
  constructor
  · rintro ⟨outcome, produced, called, _⟩
    exact ⟨produced, called⟩
  · rintro ⟨produced, called⟩
    obtain ⟨outcome, _, retained⟩ := admitted.retain live called
    exact ⟨outcome, retained⟩

end Solanalib.Specs.Core.AccountInfo.GuardCallback
