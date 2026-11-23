/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.PinocchioAccount
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.PinocchioAccount

/-- Typed mappings may point into either leased field or separate captured
storage. The lease identity and the reference target are distinct. -/
structure GuardProfile where
  Target : Type
  Aux : Type

abbrev GuardProfile.World (profile : GuardProfile) :=
  Borrow.World Content profile.Target profile.Aux

structure Reference where
  guard : Guard
  writable : Bool
  deriving DecidableEq, Repr

/-- Reading follows the current target under the still-live guard. No data
snapshot can outlive a release or a consumed mapping generation. -/
def Reference.read (profile : GuardProfile) {Value : Type}
    (project : profile.World → Handle → profile.Target → Value)
    (world : profile.World) (reference : Reference) : Option Value := do
  let slot ← world.1.resolve reference.guard
  pure (project world slot.cell slot.view)

def derefContract (profile : GuardProfile) (writable : Bool) :
    Solanalib.Contracts.Model profile.World Guard Reference :=
  .returning (fun _ _ => True)
    (fun before guard result after => after = before ∧ result = ⟨guard, writable⟩)

def derefFamily (writable : Bool) : Family where
  Index := GuardProfile
  State := GuardProfile.World
  Args := fun _ => Guard
  Value := fun _ => Reference
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun profile => derefContract profile writable

def derefRun (writable : Bool) : FamilyRun (derefFamily writable) :=
  fun _ => returnsOf (fun before guard => (⟨guard, writable⟩, before))

def guardSample : GuardProfile := ⟨View, List Header⟩

theorem deref_reference (writable : Bool) :
    FamilyReference (derefFamily writable) (derefRun writable) := by
  intro profile
  apply (Solanalib.Contracts.Model.realized_iff_holds _ _).mp
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem deref_hasExecution (writable : Bool) :
    FamilyHasExecution (derefFamily writable) (derefRun writable) guardSample :=
  ⟨sampleState, ⟨0, 0⟩, .returned ⟨⟨0, 0⟩, writable⟩ sampleState, trivial, rfl⟩

/-- Drop releases the same lease after mapping, independent of target type.
The original field identity determines which nibble is restored. -/
def dropContract (profile : GuardProfile) : Solanalib.Contracts.Model profile.World Guard Unit :=
  .returning (fun before guard => ∃ slot, before.1.resolve guard = some slot)
    (fun before guard _ after =>
      Borrow.release before.1 guard = (.ok (), after.1) ∧ after.2 = before.2 ∧
      after.1.resolve guard = none ∧ after.1.cells = before.1.cells)

def dropFamily : Family where
  Index := GuardProfile
  State := GuardProfile.World
  Args := fun _ => Guard
  Value := fun _ => Unit
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := dropContract

def dropRun : FamilyRun dropFamily :=
  fun _ => returnsOf (fun before guard => ((), ((Borrow.release before.1 guard).2, before.2)))

theorem drop_reference : FamilyReference dropFamily dropRun := by
  intro profile
  apply (Solanalib.Contracts.Model.realized_iff_holds _ _).mp
  rintro before guard ⟨slot, live⟩
  exact ⟨by simp [Borrow.release, live], rfl,
    Borrow.release_consumes live, Borrow.release_cells _ _⟩

def sampleGuard : Guard := ⟨0, 0⟩
def sampleGuardState : State := (acquire .data .exclusive sampleState sampleHandle).2

theorem drop_hasExecution : FamilyHasExecution dropFamily dropRun guardSample :=
  ⟨sampleGuardState, sampleGuard,
    .returned () ((Borrow.release sampleGuardState.1 sampleGuard).2, sampleGuardState.2),
    ⟨_, rfl⟩, rfl⟩

/-- The concrete target type of the closure, captured state and abnormal exits are
family indices. The footprint describes permitted changes to the held field. -/
structure MapProfile where
  target : GuardProfile
  Unwind : Type
  Terminal : Type
  footprint : Borrow.Footprint Content target.Target

structure MapArgs (profile : MapProfile) where
  guard : Guard
  callback : profile.target.World → Handle → profile.target.Target →
    Outcome profile.target.World profile.target.Target profile.Unwind profile.Terminal → Prop

def mapFrame (profile : MapProfile) (before : profile.target.World) (guard : Guard)
    (produced : Outcome profile.target.World profile.target.Target profile.Unwind profile.Terminal)
      : Prop :=
  match produced with
  | .returned _ after | .unwound _ after => Borrow.CallbackFrame profile.footprint before.1 after.1
    guard
  | .terminated _ => True

def mapSafe (profile : MapProfile) (before : profile.target.World) (args : MapArgs profile) : Prop
  :=
  ∀ slot cell, before.1.resolve args.guard = some slot →
    before.1.lookupCell slot.cell = some cell →
    ∀ produced, args.callback before slot.cell slot.view produced → mapFrame profile before
      args.guard produced

def nextGuard (guard : Guard) : Guard := ⟨guard.id, guard.generation + 1⟩

/-- ManuallyDrop is installed before calling the closure. On unwind the held
lease leaks; the consumed source token advances generation and is not reusable.
Normal return transfers the same lease to the actual returned target. -/
def finishMap (profile : MapProfile) (guard : Guard) (original : profile.target.Target)
    (produced : Outcome profile.target.World profile.target.Target profile.Unwind profile.Terminal)
      :
    Outcome profile.target.World Guard profile.Unwind profile.Terminal :=
  match produced with
  | .returned target after =>
    .returned (nextGuard guard) ((Borrow.transfer after.1 guard target).2, after.2)
  | .unwound reason after =>
    .unwound reason (Borrow.unwindState .retainLease after.1 guard original, after.2)
  | .terminated reason => .terminated reason

/-- The operational relation retains each actual callback exit, without
filtering it by the universal callback-frame assumption. -/
def mapRunAt (profile : MapProfile) (before : profile.target.World) (args : MapArgs profile)
    (outcome : Outcome profile.target.World Guard profile.Unwind profile.Terminal) : Prop :=
  ∃ slot cell produced, before.1.resolve args.guard = some slot ∧
    before.1.lookupCell slot.cell = some cell ∧ args.callback before slot.cell slot.view produced ∧
    outcome = finishMap profile args.guard slot.view produced

def mapContract (profile : MapProfile) :
    Solanalib.Contracts.Model profile.target.World (MapArgs profile) Guard profile.Unwind
      profile.Terminal where
  requires := mapSafe profile
  post := fun before args outcome => ∃ slot cell produced,
    before.1.resolve args.guard = some slot ∧ before.1.lookupCell slot.cell = some cell ∧
    args.callback before slot.cell slot.view produced ∧ mapFrame profile before args.guard produced
      ∧
    outcome = finishMap profile args.guard slot.view produced

def mapFamily : Family where
  Index := MapProfile
  State := fun profile => profile.target.World
  Args := MapArgs
  Value := fun _ => Guard
  Unwind := MapProfile.Unwind
  Terminal := MapProfile.Terminal
  contract := mapContract

def mapRun : FamilyRun mapFamily := mapRunAt

theorem map_reference : FamilyReference mapFamily mapRun := by
  rintro profile before args outcome safe ⟨slot, cell, produced, live, present, called, finished⟩
  exact ⟨slot, cell, produced, live, present, called,
    safe slot cell live present produced called, finished⟩

/-- Every finite callback execution at an existing guard is retained, including
unwind and termination. No normal-return or purity assumption is imposed. -/
theorem map_retains (profile : MapProfile) (before : profile.target.World) (args : MapArgs profile)
    (slot : Borrow.Slot profile.target.Target) (cell : Borrow.Cell Content)
    (live : before.1.resolve args.guard = some slot) (present : before.1.lookupCell slot.cell =
      some cell)
    (produced : Outcome profile.target.World profile.target.Target profile.Unwind profile.Terminal)
    (called : args.callback before slot.cell slot.view produced) :
    mapRunAt profile before args (finishMap profile args.guard slot.view produced) :=
  ⟨slot, cell, produced, live, present, called, rfl⟩

def mapSample : MapProfile := ⟨guardSample, Empty, Unit, fun _ _ before after => after = before⟩
def mapSampleArgs : MapArgs mapSample :=
  ⟨sampleGuard, fun _ _ _ outcome => outcome = .terminated ()⟩

/-- This closed execution witnesses the real terminal branch without requiring
a fabricated post-state or cleanup after the closure terminates. -/
theorem map_hasExecution : FamilyHasExecution mapFamily mapRun mapSample := by
  refine ⟨sampleGuardState, mapSampleArgs, .terminated (), ?_, ?_⟩
  · intro slot cell live present produced called
    cases called
    trivial
  · exact ⟨_, _, .terminated (), rfl, rfl, rfl, rfl⟩

end Solanalib.Specs.Core.PinocchioAccount
