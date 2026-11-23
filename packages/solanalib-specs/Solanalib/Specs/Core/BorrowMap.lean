/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorrowValid

/-!
Finite callback outcomes for guard mapping. A callback receives a mathematical
cell handle and view descriptor and may change captured cells and auxiliary
state. Its explicit universal precondition preserves the held lease, cell
identities, and the selected footprint of the adapter. Shared callbacks are not
assumed pure. The operational relation forwards every finite callback outcome;
it does not filter outcomes by that precondition.

The source binding must justify the callback relation, view interpretation,
footprint, and unwind destruction order for its exact interface version.
`release` and `retainLease` below are distinct source-binding choices, not an
assumption that a destructor ran. Termination has no invented post-state;
absence of finite callback outcomes can represent divergence.
-/

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borrow

universe u v w x y z

/-- The entire borrow store together with arbitrary captured auxiliary state. -/
abbrev World (Content : Type u) (View : Type v) (Aux : Type w) := State Content View × Aux

/-- The precise changes to the held view allowed by its interpretation. A shared data view
may still admit captured writes to unrelated account-header fields. -/
abbrev Footprint (Content : Type u) (View : Type v) :=
  Mode → View → Content → Content → Prop

variable {Content : Type u} {View : Type v}

/-- Admissible finite effects of a callback while one guard is held. All other
cells and auxiliary state may change, subject to identity and protocol validity.
The callback cannot consume the guard of its caller or revive an old generation. -/
structure CallbackFrame (footprint : Footprint Content View)
    (before after : State Content View) (guard : Guard) : Prop where
  /-- The actual final borrow state of the callback satisfies the protocol invariant. -/
  valid : after.Valid
  /-- Callback effects cannot revive previously consumed tokens. -/
  history : History before after
  /-- Existing cell identities and their policies survive arbitrary captured effects. -/
  cells : ∀ handle old, before.lookupCell handle = some old →
    ∃ next, after.lookupCell handle = some next ∧ next.policy = old.policy
  /-- The held guard of the caller retains its exact live record during the callback. -/
  held : after.resolve guard = before.resolve guard
  /-- Changes to the held cell satisfy the view-specific footprint of the adapter. -/
  changes : ∀ slot old next, before.resolve guard = some slot →
    before.lookupCell slot.cell = some old → after.lookupCell slot.cell = some next →
    footprint slot.mode slot.view old.value next.value

/-- Explicit source destruction behavior for an owned guard during callback
unwinding. Retention models a leaked/manually suppressed lease and still consumes
the input token. A versioned adapter records why its chosen policy applies. -/
inductive UnwindPolicy where
  /-- Guard destruction releases the held lease after the callback unwinds. -/
  | release
  /-- Suppressed destruction leaves the lease held but consumes the input token. -/
  | retainLease
  deriving DecidableEq, Repr

/-- The finite relation of a callback; ordinary errors belong to its returned value. -/
abbrev MapCallback (Content : Type u) (View : Type v) (Aux : Type w)
    (Failure : Type x) (Unwind : Type y) (Terminal : Type z) :=
  World Content View Aux → Handle → View →
    Outcome (World Content View Aux) (Except Failure View) Unwind Terminal → Prop

/-- A checked mapping either rejects an invalid guard, returns a mapped guard,
or returns the callback error together with the transferred original view. -/
abbrev TryMapResult (Failure : Type x) := Except Error (Except (Failure × Guard) Guard)

variable {Aux : Type w}
variable {Failure : Type x} {Unwind : Type y} {Terminal : Type z}

/-- Apply the source-bound cleanup to the actual final store of an unwinding callback. -/
def unwindState (policy : UnwindPolicy) (state : State Content View)
    (guard : Guard) (original : View) : State Content View :=
  match policy with
  | .release => (release state guard).2
  | .retainLease => (transfer state guard original).2

/-- Complete one finite callback outcome. Both normal branches keep its actual
world; `Err` retains the original view but does not undo mutable callback writes. -/
def finishTryMap (policy : UnwindPolicy) (guard : Guard) (original : View)
    (produced : Outcome (World Content View Aux) (Except Failure View) Unwind Terminal) :
    Outcome (World Content View Aux) (TryMapResult Failure) Unwind Terminal :=
  match produced with
  | .returned result after =>
    let view := match result with | .ok mapped => mapped | .error _ => original
    let moved := transfer after.1 guard view
    .returned
      (match moved.1 with
        | .error error => .error error
        | .ok next => .ok (match result with
          | .ok _ => .ok next
          | .error error => .error (error, next)))
      (moved.2, after.2)
  | .unwound reason after =>
    .unwound reason (unwindState policy after.1 guard original, after.2)
  | .terminated reason => .terminated reason

/-- The callback frame applies to every exit that supplies a state. -/
def CallbackAdmissible (footprint : Footprint Content View) (before : State Content View)
    (guard : Guard)
    (produced : Outcome (World Content View Aux) (Except Failure View) Unwind Terminal) : Prop :=
  match produced with
  | .returned _ after | .unwound _ after => CallbackFrame footprint before after.1 guard
  | .terminated _ => True

/-- Universal callback admission at the actual resolved input of this call. Every
finite callback exit must meet the frame, including errors and unwinds. Invalid
guard/cell inputs do not call the callback. This is a soundness precondition,
not a filter on individual outcomes or an assumption that any exit exists. -/
def MapCallback.Admissible (footprint : Footprint Content View)
    (callback : MapCallback Content View Aux Failure Unwind Terminal)
    (before : World Content View Aux) (guard : Guard) : Prop :=
  ∀ slot cell, before.1.resolve guard = some slot →
    before.1.lookupCell slot.cell = some cell →
    ∀ produced, callback before slot.cell slot.view produced →
      CallbackAdmissible footprint before.1 guard produced

/-- The unfiltered finite mapping relation, including invalid-input errors and
every callback error, unwind or terminal exit. Soundness contracts must require
`MapCallback.Admissible`; the relation itself never erases an inadmissible exit.
No callback outcome is assumed to exist. Projection validity remains an
additional Rust-binding obligation. -/
def tryMap (policy : UnwindPolicy)
    (callback : MapCallback Content View Aux Failure Unwind Terminal)
    (before : World Content View Aux) (guard : Guard) :
    Outcome (World Content View Aux) (TryMapResult Failure) Unwind Terminal → Prop :=
  match before.1.resolve guard with
  | none => fun outcome => outcome = .returned (.error .invalidGuard) before
  | some slot => match before.1.lookupCell slot.cell with
    | none => fun outcome => outcome = .returned (.error .missingCell) before
    | some _ => fun outcome => ∃ produced,
      callback before slot.cell slot.view produced ∧
      outcome = finishTryMap policy guard slot.view produced

/-- At an actual live input, mapping is exactly finishing one callback outcome,
with no frame-based restriction on which outcomes are retained. -/
theorem tryMap_iff_of_live (policy : UnwindPolicy)
    (callback : MapCallback Content View Aux Failure Unwind Terminal)
    {before : World Content View Aux} {guard : Guard} {slot : Slot View} {cell : Cell Content}
    (live : before.1.resolve guard = some slot)
    (present : before.1.lookupCell slot.cell = some cell)
    (outcome : Outcome (World Content View Aux) (TryMapResult Failure) Unwind Terminal) :
    tryMap policy callback before guard outcome ↔
      ∃ produced, callback before slot.cell slot.view produced ∧
        outcome = finishTryMap policy guard slot.view produced := by
  simp only [tryMap, live, present]

/-- Every actual finite callback outcome has its corresponding mapping outcome,
independently of whether a source interpretation proves admissibility. -/
theorem tryMap_of_callback (policy : UnwindPolicy)
    {callback : MapCallback Content View Aux Failure Unwind Terminal}
    {before : World Content View Aux} {guard : Guard} {slot : Slot View} {cell : Cell Content}
    (live : before.1.resolve guard = some slot)
    (present : before.1.lookupCell slot.cell = some cell)
    {produced : Outcome (World Content View Aux) (Except Failure View) Unwind Terminal}
    (called : callback before slot.cell slot.view produced) :
    tryMap policy callback before guard (finishTryMap policy guard slot.view produced) :=
  (tryMap_iff_of_live policy callback live present _).mpr ⟨produced, called, rfl⟩

/-- A live mapping has a finite outcome exactly when its invoked callback does.
Inadmissibility cannot turn a nonempty callback into an empty reference relation. -/
theorem tryMap_hasOutcome_iff (policy : UnwindPolicy)
    (callback : MapCallback Content View Aux Failure Unwind Terminal)
    {before : World Content View Aux} {guard : Guard} {slot : Slot View} {cell : Cell Content}
    (live : before.1.resolve guard = some slot)
    (present : before.1.lookupCell slot.cell = some cell) :
    (∃ outcome, tryMap policy callback before guard outcome) ↔
      ∃ produced, callback before slot.cell slot.view produced := by
  constructor
  · rintro ⟨outcome, step⟩
    obtain ⟨produced, called, _⟩ := (tryMap_iff_of_live policy callback live present outcome).mp
      step
    exact ⟨produced, called⟩
  · rintro ⟨produced, called⟩
    exact ⟨finishTryMap policy guard slot.view produced,
      tryMap_of_callback policy live present called⟩

/-- The guard held by a callback remains live with its exact original record. -/
theorem CallbackFrame.resolve {footprint : Footprint Content View}
    {before after : State Content View} {guard : Guard} {slot : Slot View}
    (frame : CallbackFrame footprint before after guard)
    (live : before.resolve guard = some slot) : after.resolve guard = some slot := by
  rw [frame.held, live]

/-- Finite callback effects preserve the policy of the held cell and obey the explicit
footprint, even when other cells or captured auxiliary state have changed. -/
theorem CallbackFrame.current {footprint : Footprint Content View}
    {before after : State Content View} {guard : Guard} {slot : Slot View} {old : Cell Content}
    (frame : CallbackFrame footprint before after guard)
    (live : before.resolve guard = some slot) (present : before.lookupCell slot.cell = some old) :
    ∃ next, after.lookupCell slot.cell = some next ∧ next.policy = old.policy ∧
      footprint slot.mode slot.view old.value next.value := by
  obtain ⟨next, found, policy⟩ := frame.cells slot.cell old present
  exact ⟨next, found, policy, frame.changes slot old next live present found⟩

/-- An invalid input produces its exact checked error without running a callback. -/
theorem tryMap_invalid {before : World Content View Aux} {guard : Guard}
    (dead : before.1.resolve guard = none) (policy : UnwindPolicy)
    (callback : MapCallback Content View Aux Failure Unwind Terminal) :
    tryMap policy callback before guard (.returned (.error .invalidGuard) before) := by
  simp [tryMap, dead]

/-- On a normal callback error, every changed cell and the actual captured state
are retained; only the generation of the guard token changes. -/
theorem finishTryMap_error (policy : UnwindPolicy) (guard : Guard) (original : View)
    (error : Failure) (after : World Content View Aux) {slot : Slot View}
    (live : after.1.resolve guard = some slot) :
    finishTryMap (Unwind := Unwind) (Terminal := Terminal) policy guard original
      (.returned (.error error) after) =
      .returned (.ok (.error (error, ⟨guard.id, guard.generation + 1⟩)))
        ((transfer after.1 guard original).2, after.2) := by
  simp [finishTryMap, transfer_live live original]

/-- A successful callback transfers the same lease to its selected descriptor. -/
theorem finishTryMap_ok (policy : UnwindPolicy) (guard : Guard) (original mapped : View)
    (after : World Content View Aux) {slot : Slot View}
    (live : after.1.resolve guard = some slot) :
    finishTryMap (Failure := Failure) (Unwind := Unwind) (Terminal := Terminal)
      policy guard original (.returned (.ok mapped) after) =
      .returned (.ok (.ok ⟨guard.id, guard.generation + 1⟩))
        ((transfer after.1 guard mapped).2, after.2) := by
  simp [finishTryMap, transfer_live live mapped]

/-- Neither normal mapping branch rolls back any callback-written contents. -/
theorem finish_return_cells (guard : Guard) (original : View) (result : Except Failure View)
    (after : World Content View Aux) :
    (transfer after.1 guard (match result with | .ok v => v | .error _ => original)).2.cells =
      after.1.cells := transfer_cells _ _ _

/-- Both source-bound unwind policies preserve the actual cell contents of the callback. -/
theorem unwindState_cells (policy : UnwindPolicy) (state : State Content View)
    (guard : Guard) (original : View) :
    (unwindState policy state guard original).cells = state.cells := by
  cases policy
  · exact release_cells state guard
  · exact transfer_cells state guard original

/-- Unwinding consumes the owned input guard even if the source retains its lease. -/
theorem unwindState_retired (policy : UnwindPolicy) {state : State Content View}
    {guard : Guard} {slot : Slot View} (live : state.resolve guard = some slot) (original : View) :
    Retired (unwindState policy state guard original) guard := by
  cases policy
  · exact release_retired live
  · exact transfer_retired live original

/-- A terminal callback exit is forwarded with no fabricated state or cleanup. -/
theorem finishTryMap_terminated (policy : UnwindPolicy) (guard : Guard) (original : View)
    (reason : Terminal) :
    finishTryMap (Content := Content) (Aux := Aux) (Failure := Failure) (Unwind := Unwind)
      policy guard original (.terminated reason) = .terminated reason := rfl

end Solanalib.Specs.Core.Borrow
