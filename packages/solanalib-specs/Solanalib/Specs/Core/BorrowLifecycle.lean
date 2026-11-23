/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorrowCompatibility

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borrow

universe u v

variable {Content : Type u} {View : Type v}
variable {state : State Content View} {guard : Guard} {slot : Slot View}

/-- Successful and rejected acquisitions both preserve every current cell. -/
theorem acquire_cells (state : State Content View) (handle : Handle) (mode : Mode) (view : View) :
    (acquire state handle mode view).2.cells = state.cells := by
  cases present : state.lookupCell handle with
  | none => simp [acquire, present]
  | some cell =>
    cases mode with
    | shared =>
      simp only [acquire, present]
      split
      · rfl
      · split <;> rfl
    | exclusive =>
      simp only [acquire, present]
      split <;> rfl

/-- A valid registry contains no leases on a missing cell. -/
theorem State.count_missing (valid : state.Valid) {handle : Handle}
    (missing : state.lookupCell handle = none) (mode : Mode) : state.count handle mode = 0 := by
  apply List.countP_eq_zero.mpr
  intro entry member
  cases entry with
  | none => simp
  | some value =>
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    rintro ⟨same, _⟩
    obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
    have live : state.lookupSlot id = some value :=
      (state.lookupSlot_some_iff id value).mpr found
    obtain ⟨cell, present⟩ := valid.1 id value live
    rw [same, missing] at present
    cases present

/-- Appending a fresh cell preserves every existing lease invariant. -/
theorem State.insert_valid (valid : state.Valid) (policy : Policy) (value : Content) :
    (state.insert policy value).2.Valid := by
  constructor
  · intro id slot found
    obtain ⟨cell, present⟩ := valid.1 id slot found
    exact ⟨cell, by
      rw [State.insert_lookup_old state policy value slot.cell (State.lookupCell_bound present)]
      exact present⟩
  · intro handle cell present
    by_cases old : handle.cell < state.cells.length
    · rw [State.insert_lookup_old state policy value handle old] at present
      exact valid.2 handle cell present
    · have missing : state.lookupCell handle = none := by
        simp [State.lookupCell, old]
      have ex : state.exclusiveCount handle = 0 := State.count_missing valid missing .exclusive
      have sh : state.sharedCount handle = 0 := State.count_missing valid missing .shared
      change state.exclusiveCount handle ≤ 1 ∧
        (state.exclusiveCount handle = 1 → state.sharedCount handle = 0) ∧
        state.sharedCount handle ≤ cell.policy.sharedLimit
      simp [ex, sh]

/-- A newly inserted cell starts free even when other cells have live guards. -/
theorem State.insert_fresh_free (valid : state.Valid) (policy : Policy) (value : Content) :
    (state.insert policy value).2.lease (state.insert policy value).1 = .free := by
  have missing : state.lookupCell (state.insert policy value).1 = none := by
    simp [State.insert, State.lookupCell]
  have ex : state.exclusiveCount (state.insert policy value).1 = 0 :=
    State.count_missing valid missing .exclusive
  have sh : state.sharedCount (state.insert policy value).1 = 0 :=
    State.count_missing valid missing .shared
  change state.lease (state.insert policy value).1 = .free
  simp [State.lease, ex, sh]

/-- Direct modification retains validity; its adapter still supplies authorization. -/
theorem modifyCell_valid (valid : state.Valid) (handle : Handle) (update : Content → Content) :
    (modifyCell state handle update).2.Valid := by
  unfold modifyCell
  split
  · exact valid
  · exact replaceCell_valid valid handle _

/-- Direct modification cannot revive any retired token. -/
theorem modifyCell_history (state : State Content View) (handle : Handle)
    (update : Content → Content) : History state (modifyCell state handle update).2 := by
  unfold modifyCell
  split
  · exact History.refl state
  · exact replaceCell_history state handle _

/-- A valid shared holder excludes exclusive access and contributes one live share. -/
theorem shared_excludes_exclusive (valid : state.Valid) (live : state.resolve guard = some slot)
    (mode : slot.mode = .shared) :
    state.exclusiveCount slot.cell = 0 ∧ 0 < state.sharedCount slot.cell := by
  have found := (state.resolve_some_iff.mp live).1
  obtain ⟨cell, present⟩ := valid.1 guard.id slot found
  obtain ⟨bound, excludes, _⟩ := valid.2 slot.cell cell present
  have positive : 0 < state.sharedCount slot.cell := by
    simpa [State.sharedCount, mode] using State.slot_count_positive found
  exact ⟨by omega, positive⟩

/-- Releasing an identified live guard implements exactly the canonical lease
release observation, for both modes and every per-cell acquisition policy. -/
theorem release_observation (valid : state.Valid) (live : state.resolve guard = some slot) :
    (state.lease slot.cell).release = some ((release state guard).2.lease slot.cell) := by
  cases mode : slot.mode with
  | shared =>
    obtain ⟨ex, positive⟩ := shared_excludes_exclusive valid live mode
    have afterEx : (release state guard).2.exclusiveCount slot.cell = 0 := by
      simpa [State.exclusiveCount, release_count live, mode] using ex
    have afterSh : (release state guard).2.sharedCount slot.cell = state.sharedCount slot.cell - 1
      := by
      simp [State.sharedCount, release_count live, mode]
    cases count : state.sharedCount slot.cell with
    | zero => omega
    | succ n =>
      cases n <;> simp [State.lease, ex, afterEx, afterSh, count, Solanalib.Runtime.Lease.release]
  | exclusive =>
    rw [release_exclusive_free valid live mode]
    simp [State.lease, (exclusive_sole valid live mode).1, Solanalib.Runtime.Lease.release]

end Solanalib.Specs.Core.Borrow
