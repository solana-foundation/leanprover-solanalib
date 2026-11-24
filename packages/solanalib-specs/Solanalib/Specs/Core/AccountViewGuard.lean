/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewWitness
public import Solanalib.Specs.Core.BorrowMapLaws
public import Solanalib.Specs.Core.Family

/-!
The lifetime of a data lease and the target of a mapped reference are separate.
GuardProfile interprets arbitrary target descriptors against current account
contents and captured storage. A Rust projection is not assumed to return a byte
slice, remain in the leased account, or copy its target.

The profile supplies the validity and footprint obligations of the represented
Rust reference type. It does not supply a proof of an SDK implementation. The
whole-account byte profile below connects ordinary data acquisition to this
generic reference interface.
-/

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- Interpretation of typed reference targets and their allowed held-account
effects. Validity depends on current contents and captured storage, never on a
snapshot taken when the guard was acquired. A source binding must justify the ownership, aliasing,
lifetime and footprint interpretation of the
reference type. -/
structure GuardProfile where
  /-- Descriptors for source and mapped targets, which need not be account byte slices. -/
  View : Type
  /-- Captured storage and other callback state outside the account pool. -/
  Aux : Type
  /-- The current permission and interpretation condition for a target descriptor. -/
  valid : List (Borrow.Cell Account) → Aux → Handle → View → Prop
  /-- The allowed change to the account whose lease the guard retains. -/
  footprint : Borrow.Footprint Account View

/-- A generic reference world retains the same account cells and lease protocol. -/
abbrev GuardProfile.World (profile : GuardProfile) :=
  Borrow.World Account profile.View profile.Aux

/-- A currently meaningful target descriptor in the supplied interpretation. -/
def GuardProfile.ViewValid (profile : GuardProfile) (world : profile.World)
    (handle : Handle) (view : profile.View) : Prop :=
  profile.valid world.1.cells world.2 handle view

/-- A live source reference with its exact lease mode and interpreted target. -/
def GuardProfile.Ready (profile : GuardProfile) (mode : Mode)
    (world : profile.World) (guard : Guard) : Prop :=
  PoolWellFormed world.1 ∧ ∃ slot cell,
    world.1.resolve guard = some slot ∧ world.1.lookupCell slot.cell = some cell ∧
    slot.mode = mode ∧ profile.ViewValid world slot.cell slot.view

/-- Read the current target of a reference through an arbitrary typed interpretation.
The existing token must still resolve; mapped or released tokens cannot read a
stale target. No target value is copied into the reference itself. -/
def DataRef.project (profile : GuardProfile) {Value : Type}
    (read : List (Borrow.Cell Account) → profile.Aux → Handle → profile.View → Value)
    (reference : DataRef) (world : profile.World) : Except Borrow.Error Value :=
  match world.1.resolve reference.guard with
  | none => .error .invalidGuard
  | some slot => match world.1.lookupCell slot.cell with
    | none => .error .missingCell
    | some _ => .ok (read world.1.cells world.2 slot.cell slot.view)

/-- Shared data projections preserve the bytes behind their held range while
allowing captured changes to unrelated header fields. Exclusive callbacks may
write the data immediately. Both modes retain the live data extent. -/
def sliceFootprint : Borrow.Footprint Account Slice :=
  fun mode view before after =>
    after.dataLen = before.dataLen ∧ after.backing.length = before.backing.length ∧
    (mode = .shared → after.read view = before.read view)

/-- Ordinary account-data references instantiate the generic target vocabulary
with byte ranges. Header metadata is not part of the held byte footprint. -/
def sliceProfileWithAux (Aux : Type) : GuardProfile where
  View := Slice
  Aux := Aux
  valid := fun cells _ handle view =>
    ∃ cell, cells[handle.cell]? = some cell ∧ view.ValidFor cell.value
  footprint := sliceFootprint

/-- The byte-profile instance without additional captured storage. -/
def sliceProfile : GuardProfile := sliceProfileWithAux Unit

/-- The ordinary data-reference precondition is exactly the byte-profile
instance of the generic typed-reference precondition. -/
theorem sliceProfileWithAux_ready {Aux : Type} (state : State) (aux : Aux)
    (mode : Mode) (guard : Guard) :
    (sliceProfileWithAux Aux).Ready mode (state, aux) guard ↔ GuardReady state mode guard := by
  constructor
  · rintro ⟨wellFormed, slot, cell, live, present, kind, next, nextPresent, range⟩
    have same : next = cell := by
      change state.lookupCell slot.cell = some next at nextPresent
      change state.lookupCell slot.cell = some cell at present
      rw [present] at nextPresent
      cases nextPresent
      rfl
    subst next
    exact ⟨wellFormed, slot, cell, live, present, kind, range⟩
  · rintro ⟨wellFormed, slot, cell, live, present, kind, range⟩
    exact ⟨wellFormed, slot, cell, live, present, kind, cell, present, range⟩

/-- Ordinary whole-data acquisition supplies the precondition of the sample profile. -/
theorem sliceProfile_ready (state : State) (mode : Mode) (guard : Guard) :
    sliceProfile.Ready mode (state, ()) guard ↔ GuardReady state mode guard :=
  sliceProfileWithAux_ready state () mode guard

/-- Generic dereference constructs a reference to the existing target without
changing its world or issuing a second lease. Constructing the descriptor does
not establish that its guard or interpreted target is readable. -/
def genericDerefContract (profile : GuardProfile) (_mode : Mode) (writable : Bool) :
    Solanalib.Contracts.Model profile.World Guard DataRef :=
  .returning (fun _ _ => True)
    (fun before guard value after => after = before ∧ value = ⟨guard, writable⟩)

/-- Generic guard destruction consumes its identity in the common registry and
preserves all current account contents and captured state. -/
def genericReleaseContract (profile : GuardProfile) (_mode : Mode) :
    Solanalib.Contracts.Model profile.World Guard Unit :=
  .returning (fun before guard => ∃ slot, before.1.resolve guard = some slot)
    (fun before guard _ after =>
      Borrow.release before.1 guard = (.ok (), after.1) ∧ after.2 = before.2)

/-- All source target types share the same dereference operation. -/
def derefFamily (mode : Mode) (writable : Bool) : Family where
  Index := GuardProfile
  State := GuardProfile.World
  Args := fun _ => Guard
  Value := fun _ => DataRef
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun profile => genericDerefContract profile mode writable

/-- Actual reference relation for the generic dereference family. -/
def derefRun (mode : Mode) (writable : Bool) : FamilyRun (derefFamily mode writable) :=
  fun _ => returnsOf (fun before guard => (⟨guard, writable⟩, before))

/-- Dereference correctness covers every supplied target interpretation. -/
theorem derefFamily_reference (mode : Mode) (writable : Bool) :
    FamilyReference (derefFamily mode writable) (derefRun mode writable) := by
  intro profile
  apply (Solanalib.Contracts.Model.realized_iff_holds _ _).mp
  intro before guard _
  exact ⟨rfl, rfl⟩

/-- The byte-profile reference gives a concrete execution for each access mode. -/
theorem derefFamily_execution (mode : Mode) (writable : Bool) :
    FamilyHasExecution (derefFamily mode writable) (derefRun mode writable) sliceProfile := by
  refine ⟨(witnessGuardState mode, ()), witnessGuard,
    .returned ⟨witnessGuard, writable⟩ (witnessGuardState mode, ()), trivial, rfl⟩

theorem derefFamily_satisfiable (mode : Mode) (writable : Bool) :
    FamilySatisfiable (derefFamily mode writable) sliceProfile :=
  (derefFamily_execution mode writable).satisfiable

/-- All mapped target types share the same lease destruction operation. -/
def releaseFamily (mode : Mode) : Family where
  Index := GuardProfile
  State := GuardProfile.World
  Args := fun _ => Guard
  Value := fun _ => Unit
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun profile => genericReleaseContract profile mode

/-- The generic release reference performs the actual registry operation. -/
def releaseRun (mode : Mode) : FamilyRun (releaseFamily mode) :=
  fun _ => returnsOf (fun before guard => ((), ((Borrow.release before.1 guard).2, before.2)))

/-- Destruction is correct for every interpreted reference type. -/
theorem releaseFamily_reference (mode : Mode) :
    FamilyReference (releaseFamily mode) (releaseRun mode) := by
  intro profile
  apply (Solanalib.Contracts.Model.realized_iff_holds _ _).mp
  intro before guard ready
  obtain ⟨slot, live⟩ := ready
  change Borrow.release before.1 guard = (.ok (), (Borrow.release before.1 guard).2) ∧ _
  exact ⟨by rw [Borrow.release_live live], rfl⟩

/-- A live byte guard provides a concrete successful destruction. -/
theorem releaseFamily_execution (mode : Mode) :
    FamilyHasExecution (releaseFamily mode) (releaseRun mode) sliceProfile := by
  refine ⟨(witnessGuardState mode, ()), witnessGuard,
    .returned () ((Borrow.release (witnessGuardState mode) witnessGuard).2, ()), ?_, rfl⟩
  exact ⟨_, rfl⟩

theorem releaseFamily_satisfiable (mode : Mode) :
    FamilySatisfiable (releaseFamily mode) sliceProfile :=
  (releaseFamily_execution mode).satisfiable

end Solanalib.Specs.Core.AccountView
