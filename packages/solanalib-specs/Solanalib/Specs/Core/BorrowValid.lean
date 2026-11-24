/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorrowHistory

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borrow

universe u v

variable {Content : Type u} {View : Type v}
variable {state : State Content View} {guard : Guard} {slot : Slot View}

/-- Cells with no issued guards meet the complete borrow invariant. -/
theorem State.valid_empty_slots (cells : List (Cell Content)) :
    (⟨cells, []⟩ : State Content View).Valid := by
  constructor
  · intro id slot present
    simp [State.lookupSlot] at present
  · intro handle cell present
    simp [State.exclusiveCount, State.sharedCount, State.count]

/-- Releasing a live slot subtracts exactly its own contribution. -/
theorem release_count (live : state.resolve guard = some slot) (handle : Handle) (mode : Mode) :
    (release state guard).2.count handle mode = state.count handle mode -
      (if slot.cell = handle ∧ slot.mode = mode then 1 else 0) := by
  have present := (state.lookupSlot_some_iff guard.id slot).mp
    (state.resolve_some_iff.mp live).1
  obtain ⟨bound, entry⟩ := List.getElem?_eq_some_iff.mp present
  simp [release_live live, State.count, List.countP_set bound, entry]

/-- Releasing cannot increase the shared or exclusive count of any cell. -/
theorem release_count_le (state : State Content View) (guard : Guard)
    (handle : Handle) (mode : Mode) :
    (release state guard).2.count handle mode ≤ state.count handle mode := by
  cases live : state.resolve guard with
  | none => simp [release, live]
  | some slot => rw [release_count live]; exact Nat.sub_le _ _

/-- Mapping retains the actual shared and exclusive lease count of every cell. -/
theorem transfer_count (state : State Content View) (guard : Guard)
    (view : View) (handle : Handle) (mode : Mode) :
    (transfer state guard view).2.count handle mode = state.count handle mode := by
  cases live : state.resolve guard with
  | none => simp [transfer, live]
  | some slot =>
    have found := (state.resolve_some_iff.mp live).1
    have present := (state.lookupSlot_some_iff guard.id slot).mp found
    obtain ⟨bound, entry⟩ := List.getElem?_eq_some_iff.mp present
    simp only [transfer_live live view, State.count, List.countP_set bound, entry]
    by_cases selected : slot.cell = handle ∧ slot.mode = mode
    · have positive := State.slot_count_positive found
      have lower : 0 < state.count handle mode := by simpa [selected.1, selected.2] using positive
      simp only [selected]
      change state.count handle mode - 1 + 1 = state.count handle mode
      omega
    · simp [selected]

/-- A mapping preserves the canonical lease observation, including alias conflicts. -/
theorem transfer_lease (state : State Content View) (guard : Guard)
    (view : View) (handle : Handle) :
    (transfer state guard view).2.lease handle = state.lease handle := by
  simp only [State.lease, State.exclusiveCount, State.sharedCount, transfer_count]
  rfl

/-- Replacement leaves the existence and policy of every cell unchanged. -/
theorem replaceCell_policy (state : State Content View) (handle query : Handle) (value : Content) :
    ((replaceCell state handle value).2.lookupCell query).map Cell.policy =
      (state.lookupCell query).map Cell.policy := by
  cases present : state.lookupCell handle with
  | none => simp [replaceCell, present]
  | some cell =>
    by_cases same : handle.cell = query.cell
    · have handles : handle = query := by cases handle; cases query; simp_all
      subst query
      rw [replaceCell_lookup present]
      simp [present]
    · exact congrArg (Option.map Cell.policy)
        (replaceCell_other state handle query value (Ne.symm same))

/-- Unchanged slots and existence/policy lookups retain validity even when
contents change. This is the invariant needed by direct header replacements. -/
theorem State.valid_of_same_policies {before after : State Content View}
    (valid : before.Valid) (slots : after.slots = before.slots)
    (policies : ∀ handle, (after.lookupCell handle).map Cell.policy =
      (before.lookupCell handle).map Cell.policy) : after.Valid := by
  constructor
  · intro id value present
    have old : before.lookupSlot id = some value := by
      simpa [State.lookupSlot, slots] using present
    obtain ⟨cell, found⟩ := valid.1 id value old
    have bound := policies value.cell
    cases next : after.lookupCell value.cell with
    | none => simp [next, found] at bound
    | some later => exact ⟨later, rfl⟩
  · intro handle cell present
    have policy := policies handle
    cases old : before.lookupCell handle with
    | none => simp [old, present] at policy
    | some previous =>
      have equal : cell.policy = previous.policy := by simpa [old, present] using policy
      simpa [State.exclusiveCount, State.sharedCount, State.count, slots, equal] using
        valid.2 handle previous old

/-- Direct replacement preserves all live-lease invariants. Its separate
authorization/footprint requirements are not inferred from this structural fact. -/
theorem replaceCell_valid (valid : state.Valid) (handle : Handle) (value : Content) :
    (replaceCell state handle value).2.Valid :=
  State.valid_of_same_policies valid (replaceCell_slots state handle value)
    (fun query => replaceCell_policy state handle query value)

/-- An exclusive guarded update preserves the complete protocol invariant. -/
theorem write_valid (valid : state.Valid) (guard : Guard) (value : Content) :
    (write state guard value).2.Valid := by
  unfold write
  split
  · exact valid
  · split
    · exact replaceCell_valid valid _ value
    · exact valid

/-- Releasing a guard retains validity; the remaining counts determine freedom. -/
theorem release_valid (valid : state.Valid) (guard : Guard) : (release state guard).2.Valid := by
  cases live : state.resolve guard with
  | none => simpa [release, live] using valid
  | some slot =>
    constructor
    · intro id value present
      by_cases same : guard.id = id
      · subst id
        rw [release_lookup_none live] at present
        cases present
      · have old : state.lookupSlot id = some value := by
          simpa [release_live live, State.lookupSlot, List.getElem?_set_ne same] using present
        obtain ⟨cell, found⟩ := valid.1 id value old
        exact ⟨cell, by simpa [State.lookupCell, release_cells] using found⟩
    · intro handle cell present
      have old : state.lookupCell handle = some cell := by
        simpa [State.lookupCell, release_cells] using present
      obtain ⟨exclusiveBound, excludes, sharedBound⟩ := valid.2 handle cell old
      have exc := release_count_le state guard handle .exclusive
      have shr := release_count_le state guard handle .shared
      change (release state guard).2.exclusiveCount handle ≤ state.exclusiveCount handle at exc
      change (release state guard).2.sharedCount handle ≤ state.sharedCount handle at shr
      refine ⟨Nat.le_trans exc exclusiveBound, ?_, Nat.le_trans shr sharedBound⟩
      intro one
      have oldOne : state.exclusiveCount handle = 1 := by omega
      have none := excludes oldOne
      omega

/-- Mapping preserves the cell/mode of the guard and hence all lease invariants. -/
theorem transfer_valid (valid : state.Valid) (guard : Guard) (view : View) :
    (transfer state guard view).2.Valid := by
  cases live : state.resolve guard with
  | none => simpa [transfer, live] using valid
  | some slot =>
    have facts := state.resolve_some_iff.mp live
    have bound := State.lookupSlot_bound facts.1
    constructor
    · intro id value present
      by_cases same : guard.id = id
      · subst id
        have updated : value = { slot with generation := guard.generation + 1, view := view } := by
          simpa [transfer_live live view, State.lookupSlot, List.getElem?_set_self bound,
            eq_comm] using present
        subst value
        obtain ⟨cell, found⟩ := valid.1 guard.id slot facts.1
        exact ⟨cell, by simpa [State.lookupCell, transfer_cells] using found⟩
      · have old : state.lookupSlot id = some value := by
          simpa [transfer_live live view, State.lookupSlot, List.getElem?_set_ne same] using present
        obtain ⟨cell, found⟩ := valid.1 id value old
        exact ⟨cell, by simpa [State.lookupCell, transfer_cells] using found⟩
    · intro handle cell present
      have old : state.lookupCell handle = some cell := by
        simpa [State.lookupCell, transfer_cells] using present
      simpa [State.exclusiveCount, State.sharedCount, transfer_count] using valid.2 handle cell old

/-- The checked issuance premises suffice to preserve the full invariant. -/
theorem State.issue_valid (valid : state.Valid) (handle : Handle) (mode : Mode) (view : View)
    {cell : Cell Content} (present : state.lookupCell handle = some cell)
    (noExclusive : state.exclusiveCount handle = 0)
    (room : match mode with
      | .shared => state.sharedCount handle < cell.policy.sharedLimit
      | .exclusive => state.sharedCount handle = 0) :
    (state.issue handle mode view).2.Valid := by
  constructor
  · intro id value found
    by_cases old : id < state.slots.length
    · rw [State.issue_lookup_old state handle mode view old] at found
      obtain ⟨oldCell, oldFound⟩ := valid.1 id value found
      exact ⟨oldCell, oldFound⟩
    · have bound := State.lookupSlot_bound (guard := ⟨id, 0⟩) found
      have equal : id = state.slots.length := by simp [State.issue] at bound; omega
      subst id
      have valueEq : value = ⟨handle, mode, 0, view⟩ := by
        simpa [State.issue, State.lookupSlot, eq_comm] using found
      subst value
      exact ⟨cell, present⟩
  · intro query queryCell found
    have old : state.lookupCell query = some queryCell := found
    by_cases same : handle = query
    · subst query
      have cellsEqual : queryCell = cell := by rw [present] at old; cases old; rfl
      subst queryCell
      cases mode with
      | shared =>
        have ex : state.count handle .exclusive = 0 := noExclusive
        have sh : state.count handle .shared < cell.policy.sharedLimit := room
        simp [State.exclusiveCount, State.sharedCount, State.issue_count, ex]
        omega
      | exclusive =>
        have ex : state.count handle .exclusive = 0 := noExclusive
        have sh : state.count handle .shared = 0 := room
        simp [State.exclusiveCount, State.sharedCount, State.issue_count, ex, sh]
    · simpa [State.exclusiveCount, State.sharedCount, State.issue_count, same] using
        valid.2 query queryCell old

/-- Every checked acquisition, including each unchanged error state, preserves validity. -/
theorem acquire_valid (valid : state.Valid) (handle : Handle) (mode : Mode) (view : View) :
    (acquire state handle mode view).2.Valid := by
  cases present : state.lookupCell handle with
  | none => simpa [acquire, present] using valid
  | some cell =>
    cases mode with
    | shared =>
      simp only [acquire, present]
      split
      · exact valid
      · rename_i free
        split
        · exact valid
        · rename_i room
          apply State.issue_valid valid handle .shared view present
          · simpa using free
          · simpa using room
    | exclusive =>
      simp only [acquire, present]
      split
      · exact valid
      · rename_i free
        apply State.issue_valid valid handle .exclusive view present
        · simp_all
        · simp_all

end Solanalib.Specs.Core.Borrow
