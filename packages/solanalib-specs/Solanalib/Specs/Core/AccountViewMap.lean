/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewGuard

/-!
Finite models of the source guard-mapping operations. Mapping moves an identified
lease to the target descriptor of the callback. It does not grant target permission:
the interpreted callback must return a valid reference in its actual final world.
Both ordinary success and error retain every permitted callback effect.

AccountView 1.0.0 and 2.0.0 suppress the input guard destructor before calling the
closure. Their adapters therefore select retainLease on unwind. The common Borrow
protocol remains parameterized; no generic destructor behavior is changed here.
-/

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- Source type and target-interpretation parameters for fallible mapping. -/
structure TryMapProfile where
  /-- The interpretation and access footprint of the reference targets. -/
  target : GuardProfile
  /-- The ordinary error payload returned alongside the original guard. -/
  Failure : Type
  /-- The reason carried by a finite unwinding exit. -/
  Unwind : Type
  /-- The reason carried by a terminal exit with no resulting world. -/
  Terminal : Type

/-- The actual source arguments: an owned guard and a potentially effectful
callback over the full account pool and captured state. -/
structure TryMapArgs (profile : TryMapProfile) where
  /-- The ownership token consumed by the source mapping operation. -/
  guard : Guard
  /-- The outcomes of the supplied callback over the complete captured world. -/
  callback : Borrow.MapCallback Account profile.target.View profile.target.Aux
    profile.Failure profile.Unwind profile.Terminal

/-- The source error order is (original guard, callback error). -/
abbrev TryMapResult (profile : TryMapProfile) := Except (Guard × profile.Failure) Guard

/-- Returned target validity is a callback obligation. A lease on the original
account alone supplies no permission for an external or differently typed target. -/
def TryMapProfile.CallbackValid (profile : TryMapProfile)
    (handle : Handle) (original : profile.target.View)
    (produced : Outcome profile.target.World (Except profile.Failure profile.target.View)
      profile.Unwind profile.Terminal) : Prop :=
  match produced with
  | .returned result after =>
    PoolWellFormed after.1 ∧ profile.target.ViewValid after handle
      (match result with | .ok mapped => mapped | .error _ => original)
  | .unwound _ after => PoolWellFormed after.1
  | .terminated _ => True

/-- The safe source callback preserves the held lease and token history, obeys
the target footprint, and supplies the validity of every returned reference. This is
a quantified premise over all its finite exits, not an assumed return value. -/
def TryMapProfile.CallbackSafe (profile : TryMapProfile) (before : profile.target.World)
    (args : TryMapArgs profile) : Prop :=
  ∀ slot cell, before.1.resolve args.guard = some slot →
    before.1.lookupCell slot.cell = some cell →
    ∀ produced, args.callback before slot.cell slot.view produced →
      Borrow.CallbackAdmissible profile.target.footprint before.1 args.guard produced ∧
        profile.CallbackValid slot.cell slot.view produced

/-- The existing source precondition supplies universal admission to the common
protocol. No callback frame is inferred from a filtered execution relation. -/
theorem TryMapProfile.CallbackSafe.admissible (profile : TryMapProfile)
    {before : profile.target.World} {args : TryMapArgs profile}
    (safe : profile.CallbackSafe before args) :
    Borrow.MapCallback.Admissible profile.target.footprint args.callback before args.guard :=
  fun slot cell live present produced called => (safe slot cell live present produced called).1

/-- Move to the next ownership token without changing the lease identity. -/
def nextGuard (guard : Guard) : Guard := ⟨guard.id, guard.generation + 1⟩

/-- The complete source-visible effect of one callback exit. A normal error
returns the original target under the new token and keeps all callback writes. -/
def finishSourceMap (profile : TryMapProfile) (guard : Guard) (original : profile.target.View)
    (produced : Outcome profile.target.World (Except profile.Failure profile.target.View)
      profile.Unwind profile.Terminal) :
    Outcome profile.target.World (TryMapResult profile) profile.Unwind profile.Terminal :=
  match produced with
  | .returned result after =>
    let target := match result with | .ok mapped => mapped | .error _ => original
    let returned := match result with
      | .ok _ => .ok (nextGuard guard)
      | .error error => .error (nextGuard guard, error)
    .returned returned ((Borrow.transfer after.1 guard target).2, after.2)
  | .unwound reason after =>
    .unwound reason (Borrow.unwindState .retainLease after.1 guard original, after.2)
  | .terminated reason => .terminated reason

/-- Embed source results in the checked common protocol, reversing only the
documented error-pair order. Invalid protocol tokens have no source result. -/
def protocolOutcome (profile : TryMapProfile)
    (outcome : Outcome profile.target.World (TryMapResult profile)
      profile.Unwind profile.Terminal) :
    Outcome profile.target.World (Borrow.TryMapResult profile.Failure)
      profile.Unwind profile.Terminal :=
  match outcome with
  | .returned result after => .returned
      (.ok (match result with | .ok guard => .ok guard | .error (guard, error) => .error (error,
        guard)))
      after
  | .unwound reason after => .unwound reason after
  | .terminated reason => .terminated reason

/-- Checked protocol outcomes retain all source result and state information. -/
theorem protocolOutcome_injective (profile : TryMapProfile) :
    Function.Injective (protocolOutcome profile) := by
  intro left right equal
  cases left with
  | returned left before =>
    cases right with
    | returned right after =>
      cases left <;> cases right <;> simp_all [protocolOutcome, Prod.ext_iff, and_comm]
    | unwound _ _ | terminated _ => cases equal
  | unwound reason before =>
    cases right <;> simp_all [protocolOutcome]
  | terminated reason =>
    cases right <;> simp_all [protocolOutcome]

/-- Source finishing is exactly the shared protocol once the callback preserves
its live input guard. No parallel guard implementation is introduced. -/
theorem protocol_finish (profile : TryMapProfile) {before : profile.target.World}
    {guard : Guard} {slot : Borrow.Slot profile.target.View}
    (live : before.1.resolve guard = some slot)
    (produced : Outcome profile.target.World (Except profile.Failure profile.target.View)
      profile.Unwind profile.Terminal)
    (frame : Borrow.CallbackAdmissible profile.target.footprint before.1 guard produced) :
    protocolOutcome profile (finishSourceMap profile guard slot.view produced) =
      Borrow.finishTryMap .retainLease guard slot.view produced := by
  cases produced with
  | returned result after =>
    have held := frame.resolve live
    cases result with
    | ok target =>
      rw [Borrow.finishTryMap_ok _ _ _ _ _ held]
      rfl
    | error error =>
      rw [Borrow.finishTryMap_error _ _ _ _ _ held]
      rfl
  | unwound _ _ | terminated _ => rfl

/-- Source-facing fallible mapping preserves the exact world of the callback and
returns an identified guard, including in its ordinary error branch. -/
def genericTryMapContract (profile : TryMapProfile) (mode : Mode) :
    Solanalib.Contracts.Model profile.target.World (TryMapArgs profile) (TryMapResult profile)
      profile.Unwind profile.Terminal where
  requires := fun before args =>
    (∃ slot cell, before.1.resolve args.guard = some slot ∧
      before.1.lookupCell slot.cell = some cell ∧ slot.mode = mode) ∧
    profile.CallbackSafe before args
  post := fun before args outcome => ∃ slot cell produced,
    before.1.resolve args.guard = some slot ∧ before.1.lookupCell slot.cell = some cell ∧
    args.callback before slot.cell slot.view produced ∧
    Borrow.CallbackAdmissible profile.target.footprint before.1 args.guard produced ∧
    profile.CallbackValid slot.cell slot.view produced ∧
    outcome = finishSourceMap profile args.guard slot.view produced

/-- The reference uses the unfiltered shared mapping protocol with the explicit ManuallyDrop unwind
behavior of the source. Universal callback admission belongs to
the contract precondition, not the operational relation. -/
def genericTryMapRun (profile : TryMapProfile) (before : profile.target.World)
    (args : TryMapArgs profile)
    (outcome : Outcome profile.target.World (TryMapResult profile)
      profile.Unwind profile.Terminal) : Prop :=
  Borrow.tryMap .retainLease args.callback before args.guard
    (protocolOutcome profile outcome)

/-- Every actual callback exit at an admitted live input has its exact source
outcome. This includes ordinary errors, unwinds and terminal exits. -/
theorem genericTryMap_of_callback (profile : TryMapProfile)
    {before : profile.target.World} {args : TryMapArgs profile}
    {slot : Borrow.Slot profile.target.View} {cell : Borrow.Cell Account}
    (live : before.1.resolve args.guard = some slot)
    (present : before.1.lookupCell slot.cell = some cell)
    (safe : profile.CallbackSafe before args)
    {produced : Outcome profile.target.World (Except profile.Failure profile.target.View)
      profile.Unwind profile.Terminal}
    (called : args.callback before slot.cell slot.view produced) :
    genericTryMapRun profile before args (finishSourceMap profile args.guard slot.view produced) :=
      by
  have frame := (TryMapProfile.CallbackSafe.admissible profile safe)
    slot cell live present produced called
  unfold genericTryMapRun
  rw [protocol_finish profile live produced frame]
  exact Borrow.tryMap_of_callback .retainLease live present called

/-- At an admitted live input, the source reference has a finite exit exactly
when its invoked callback does. Callback admission asserts no progress itself. -/
theorem genericTryMap_hasOutcome_iff (profile : TryMapProfile)
    {before : profile.target.World} {args : TryMapArgs profile}
    {slot : Borrow.Slot profile.target.View} {cell : Borrow.Cell Account}
    (live : before.1.resolve args.guard = some slot)
    (present : before.1.lookupCell slot.cell = some cell)
    (safe : profile.CallbackSafe before args) :
    (∃ outcome, genericTryMapRun profile before args outcome) ↔
      ∃ produced, args.callback before slot.cell slot.view produced := by
  constructor
  · rintro ⟨outcome, step⟩
    obtain ⟨produced, called, _⟩ :=
      (Borrow.tryMap_iff_of_live .retainLease args.callback live present _).mp step
    exact ⟨produced, called⟩
  · rintro ⟨produced, called⟩
    exact ⟨finishSourceMap profile args.guard slot.view produced,
      genericTryMap_of_callback profile live present safe called⟩

/-- Every admitted common-protocol execution satisfies the source contract. -/
theorem genericTryMap_reference (profile : TryMapProfile) (mode : Mode) :
    (genericTryMapContract profile mode).Holds (genericTryMapRun profile) := by
  intro before args outcome ready execution
  obtain ⟨⟨slot, cell, live, present, _⟩, callbackSafe⟩ := ready
  change Borrow.tryMap _ _ _ _ _ at execution
  simp only [Borrow.tryMap, live, present] at execution
  obtain ⟨produced, callback, equal⟩ := execution
  have frame := (TryMapProfile.CallbackSafe.admissible profile callbackSafe)
    slot cell live present produced callback
  refine ⟨slot, cell, produced, live, present, callback, frame,
    (callbackSafe slot cell live present produced callback).2, ?_⟩
  apply protocolOutcome_injective profile
  exact equal.trans (protocol_finish profile live produced frame).symm

/-- The fallible mapping contract is generic over source target/error/exit types. -/
def tryMapFamily (mode : Mode) : Family where
  Index := TryMapProfile
  State := fun profile => profile.target.World
  Args := TryMapArgs
  Value := TryMapResult
  Unwind := TryMapProfile.Unwind
  Terminal := TryMapProfile.Terminal
  contract := fun profile => genericTryMapContract profile mode

/-- The common mapping protocol as the family reference relation. -/
def tryMapRun (mode : Mode) : FamilyRun (tryMapFamily mode) := genericTryMapRun

theorem tryMapFamily_reference (mode : Mode) :
    FamilyReference (tryMapFamily mode) (tryMapRun mode) :=
  fun profile => genericTryMap_reference profile mode

/-- The infallible source interface has no ordinary callback error type. -/
structure MapProfile where
  /-- The interpretation and access footprint of the reference targets. -/
  target : GuardProfile
  /-- The reason carried by a finite unwinding exit. -/
  Unwind : Type
  /-- The reason carried by a terminal exit with no resulting world. -/
  Terminal : Type

/-- Embed an infallible callback using an empty ordinary error type. -/
def MapProfile.fallible (profile : MapProfile) : TryMapProfile :=
  ⟨profile.target, Empty, profile.Unwind, profile.Terminal⟩

/-- Lift the result of an infallible map without altering any exit or state. -/
def mapOutcome (profile : MapProfile)
    (outcome : Outcome profile.target.World Guard profile.Unwind profile.Terminal) :
    Outcome profile.target.World (TryMapResult profile.fallible) profile.Unwind profile.Terminal :=
  match outcome with
  | .returned guard after => .returned (.ok guard) after
  | .unwound reason after => .unwound reason after
  | .terminated reason => .terminated reason

/-- Infallible mapping is the same protocol with an uninhabited error type. -/
def genericMapContract (profile : MapProfile) (mode : Mode) :
    Solanalib.Contracts.Model profile.target.World (TryMapArgs profile.fallible) Guard
      profile.Unwind profile.Terminal where
  requires := (genericTryMapContract profile.fallible mode).requires
  post := fun before args outcome =>
    (genericTryMapContract profile.fallible mode).post before args (mapOutcome profile outcome)

/-- A byte-range instance with a concrete ordinary error type for existence witnesses. -/
def tryMapSample : TryMapProfile := ⟨sliceProfile, Unit, Empty, Empty⟩

/-- Identity callbacks are useful concrete witnesses; the generic contracts do
not require other callbacks to be pure, returning, or successful. -/
def identityMapArgs (profile : TryMapProfile) (guard : Guard) : TryMapArgs profile :=
  ⟨guard, fun before _ view outcome => outcome = .returned (.ok view) before⟩

/-- The unchanged byte world satisfies the explicit callback frame. -/
theorem sliceFrame_refl {state : State} (valid : state.Valid) (guard : Guard) :
    Borrow.CallbackFrame sliceFootprint state state guard :=
  Borrow.CallbackFrame.refl state guard valid sliceFootprint
    (fun _ _ _ => ⟨rfl, rfl, fun _ => rfl⟩)

/-- An identity byte callback supplies a valid target and does not mutate its
captured world. This proves the callback premise of the concrete witness. -/
theorem identityMap_safe (Failure : Type) (mode : Mode) :
    (⟨sliceProfile, Failure, Empty, Empty⟩ : TryMapProfile).CallbackSafe
      (witnessGuardState mode, ())
      (identityMapArgs ⟨sliceProfile, Failure, Empty, Empty⟩ witnessGuard) := by
  intro slot cell live present produced callback
  change produced = .returned (.ok slot.view) (witnessGuardState mode, ()) at callback
  subst produced
  have ready := witness_guard_ready mode
  obtain ⟨valid, currentSlot, currentCell, currentLive, currentPresent, _, range⟩ := ready
  change (witnessGuardState mode).resolve witnessGuard = some slot at live
  change (witnessGuardState mode).lookupCell slot.cell = some cell at present
  have slotsEqual : slot = currentSlot := by rw [currentLive] at live; cases live; rfl
  subst slot
  have cellsEqual : cell = currentCell := by rw [currentPresent] at present; cases present; rfl
  subst cell
  exact ⟨sliceFrame_refl valid.1 _, valid, currentCell, currentPresent, range⟩

/-- Fallible mapping has a permitted successful execution in both lease modes. -/
theorem tryMapFamily_execution (mode : Mode) :
    FamilyHasExecution (tryMapFamily mode) (tryMapRun mode) tryMapSample := by
  let before := (witnessGuardState mode, ())
  let args := identityMapArgs tryMapSample witnessGuard
  refine ⟨before, args, .returned (.ok (nextGuard witnessGuard))
    ((Borrow.transfer before.1 witnessGuard ⟨0, 0⟩).2, ()), ?_, ?_⟩
  · exact ⟨⟨_, _, rfl, rfl, rfl⟩, identityMap_safe Unit mode⟩
  · exact genericTryMap_of_callback tryMapSample
      (before := before) (args := args)
      (slot := ⟨witnessHandle, mode, 0, ⟨0, 0⟩⟩)
      (cell := ⟨Account.empty, Borrow.Policy.accountView⟩)
      (produced := .returned (.ok ⟨0, 0⟩) before)
      rfl rfl (identityMap_safe Unit mode) rfl

theorem tryMapFamily_satisfiable (mode : Mode) :
    FamilySatisfiable (tryMapFamily mode) tryMapSample :=
  (tryMapFamily_execution mode).satisfiable

end Solanalib.Specs.Core.AccountView
