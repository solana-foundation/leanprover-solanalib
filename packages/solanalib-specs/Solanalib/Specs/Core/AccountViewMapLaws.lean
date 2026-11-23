/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewMap
public import Solanalib.Specs.Core.AccountViewLifecycle

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- Either ordinary try_map branch returns the replacement ownership token. -/
def resultGuard (profile : TryMapProfile) : TryMapResult profile → Guard
  | .ok guard => guard
  | .error (guard, _) => guard

/-- An admitted target permission transfers to the returned guard while the
original lease identity, account and mode remain unchanged. -/
theorem mapped_guardReady (profile : GuardProfile) {world : profile.World}
    {guard : Guard} {slot : Borrow.Slot profile.View} {cell : Borrow.Cell Account}
    {mode : Mode} (wellFormed : PoolWellFormed world.1)
    (live : world.1.resolve guard = some slot)
    (present : world.1.lookupCell slot.cell = some cell) (kind : slot.mode = mode)
    (target : profile.View) (permission : profile.ViewValid world slot.cell target) :
    profile.Ready mode ((Borrow.transfer world.1 guard target).2, world.2) (nextGuard guard) := by
  refine ⟨wellFormed.transfer guard target, _, cell, Borrow.transfer_resolves live target,
    ?_, kind, ?_⟩
  · simpa [Borrow.State.lookupCell, Borrow.transfer_cells] using present
  · simpa only [GuardProfile.ViewValid, Borrow.transfer_cells] using permission

/-- Normal success and normal error both return a usable interpreted reference.
The input token is consumed in both branches, preventing duplicate release or
access through an earlier mapped token. -/
theorem tryMap_returned_guardReady (profile : TryMapProfile) (mode : Mode)
    {before after : profile.target.World} {args : TryMapArgs profile}
    {result : TryMapResult profile}
    (ready : (genericTryMapContract profile mode).requires before args)
    (post : (genericTryMapContract profile mode).ensures before args result after) :
    profile.target.Ready mode after (resultGuard profile result) ∧
      Borrow.Retired after.1 args.guard := by
  obtain ⟨⟨oldSlot, _, oldLive, _, oldMode⟩, _⟩ := ready
  obtain ⟨slot, cell, produced, live, present, _, frame, valid, equal⟩ := post
  have slots : slot = oldSlot := by rw [oldLive] at live; cases live; rfl
  subst slot
  cases produced with
  | returned value changed =>
    obtain ⟨next, nextPresent, _, _⟩ := frame.current live present
    have held := frame.resolve live
    cases value with
    | ok target =>
      cases equal
      exact ⟨mapped_guardReady profile.target valid.1 held nextPresent oldMode target valid.2,
        Borrow.transfer_retired held target⟩
    | error error =>
      cases equal
      exact ⟨mapped_guardReady profile.target valid.1 held nextPresent oldMode oldSlot.view valid.2,
        Borrow.transfer_retired held oldSlot.view⟩
  | unwound _ _ | terminated _ => cases equal

/-- The ManuallyDrop unwind of the source keeps the lease but retires the owned input
token. The actual changed cells and auxiliary state survive that unwind. -/
theorem tryMap_unwind_retired (profile : TryMapProfile) (mode : Mode)
    {before after : profile.target.World} {args : TryMapArgs profile} {reason : profile.Unwind}
    (post : (genericTryMapContract profile mode).post before args (.unwound reason after)) :
    PoolWellFormed after.1 ∧ Borrow.Retired after.1 args.guard := by
  obtain ⟨slot, _, produced, live, _, _, frame, valid, equal⟩ := post
  cases produced with
  | returned _ _ | terminated _ => cases equal
  | unwound _ changed =>
    cases equal
    exact ⟨valid.transfer args.guard slot.view,
      Borrow.unwindState_retired .retainLease (frame.resolve live) slot.view⟩

/-- The infallible interface inherits the same target-permission and ownership
transfer theorem without replacing its generic callback by a pure function. -/
theorem map_returned_guardReady (profile : MapProfile) (mode : Mode)
    {before after : profile.target.World} {args : TryMapArgs profile.fallible} {guard : Guard}
    (ready : (genericMapContract profile mode).requires before args)
    (post : (genericMapContract profile mode).ensures before args guard after) :
    profile.target.Ready mode after guard ∧ Borrow.Retired after.1 args.guard :=
  tryMap_returned_guardReady profile.fallible mode ready post

/-- Normal mapping preserves the final cells of the callback, including writes made
before Err. No old data snapshot is restored by the SDK model. -/
theorem finishSourceMap_cells (profile : TryMapProfile) (guard : Guard)
    (original : profile.target.View) (result : Except profile.Failure profile.target.View)
    (changed : profile.target.World) :
    finishSourceMap profile guard original (.returned result changed) =
      .returned
        (match result with
        | .ok _ => .ok (nextGuard guard)
        | .error error => .error (nextGuard guard, error))
        ((Borrow.transfer changed.1 guard
          (match result with | .ok target => target | .error _ => original)).2, changed.2) ∧
    (Borrow.transfer changed.1 guard
      (match result with | .ok target => target | .error _ => original)).2.cells = changed.1.cells
        :=
  ⟨rfl, Borrow.transfer_cells _ _ _⟩

/-- The dereference of the whole-data instance remains the current
byte observation of the complete model. The generic interface does not introduce a copied target. -/
theorem sliceReference_project (reference : DataRef) (state : State) :
    reference.project sliceProfile
      (fun cells _ handle view =>
        (((cells[handle.cell]?).map Borrow.Cell.value).getD Account.empty).read view)
      (state, ()) = reference.read state := by
  unfold DataRef.project DataRef.read guardRead Borrow.current
  dsimp only [sliceProfile, sliceProfileWithAux]
  cases live : state.resolve reference.guard with
  | none => simp [Except.map]
  | some slot =>
    cases present : state.lookupCell slot.cell with
    | none => simp [present, Except.map]
    | some cell =>
      simp only [present, Except.map]
      change Except.ok
          ((((state.cells[slot.cell.cell]?).map Borrow.Cell.value).getD Account.empty).read
            slot.view) =
        Except.ok (cell.value.read slot.view)
      change state.cells[slot.cell.cell]? = some cell at present
      simp [present]

end Solanalib.Specs.Core.AccountView
