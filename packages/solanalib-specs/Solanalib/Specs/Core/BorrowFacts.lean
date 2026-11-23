/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Borrow
import Init.Data.List.Nat.Count

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borrow

universe u v

variable {Content : Type u} {View : Type v}
variable {state : State Content View} {handle : Handle} {guard : Guard} {slot : Slot View}

/-- A present cell index is in the finite cell table. -/
theorem State.lookupCell_bound {cell : Cell Content}
    (present : state.lookupCell handle = some cell) : handle.cell < state.cells.length :=
  (List.getElem?_eq_some_iff.mp present).1

/-- A live slot is a present, non-tombstone entry in the finite table. -/
theorem State.lookupSlot_some_iff (id : Nat) (value : Slot View) :
    state.lookupSlot id = some value ↔ state.slots[id]? = some (some value) := by
  unfold State.lookupSlot
  cases state.slots[id]? with
  | none => simp
  | some entry => cases entry <;> simp

/-- A live guard identity is below the never-shrinking allocation frontier. -/
theorem State.lookupSlot_bound (present : state.lookupSlot guard.id = some slot) :
    guard.id < state.slots.length :=
  (List.getElem?_eq_some_iff.mp ((state.lookupSlot_some_iff guard.id slot).mp present)).1

/-- Resolving a token requires both the live record and its exact generation. -/
theorem State.resolve_some_iff :
    state.resolve guard = some slot ↔
      state.lookupSlot guard.id = some slot ∧ slot.generation = guard.generation := by
  constructor
  · intro live
    unfold State.resolve at live
    cases found : state.lookupSlot guard.id with
    | none => simp [found] at live
    | some value =>
      simp only [found, Option.bind_some] at live
      split at live
      · rename_i generation
        cases live
        exact ⟨rfl, generation⟩
      · cases live
  · rintro ⟨found, generation⟩
    simp [State.resolve, found, generation]

/-- Fresh acquisition resolves to exactly the issued cell, mode, and view. -/
theorem State.issue_resolves (state : State Content View) (handle : Handle)
    (mode : Mode) (view : View) :
    (state.issue handle mode view).2.resolve (state.issue handle mode view).1 =
      some ⟨handle, mode, 0, view⟩ := by
  simp [State.issue, State.resolve, State.lookupSlot]

/-- Issuing a fresh identity retains every existing slot, including tombstones. -/
theorem State.issue_lookup_old (state : State Content View) (handle : Handle)
    (mode : Mode) (view : View) {id : Nat} (old : id < state.slots.length) :
    (state.issue handle mode view).2.lookupSlot id = state.lookupSlot id := by
  simp [State.issue, State.lookupSlot, List.getElem?_append_left old]

/-- One issuance increments precisely the count for its cell and mode. -/
theorem State.issue_count (state : State Content View) (handle queried : Handle)
    (mode observed : Mode) (view : View) :
    (state.issue handle mode view).2.count queried observed =
      state.count queried observed + if handle = queried ∧ mode = observed then 1 else 0 := by
  simp [State.issue, State.count]

/-- A present slot contributes to the live count for its cell and mode. -/
theorem State.slot_count_positive (present : state.lookupSlot guard.id = some slot) :
    0 < state.count slot.cell slot.mode := by
  apply List.countP_pos_iff.mpr
  refine ⟨some slot, ?_, ?_⟩
  · exact List.mem_of_getElem? ((state.lookupSlot_some_iff guard.id slot).mp present)
  · simp

/-- The empty world has no dangling guards, conflicts, or saturated cells. -/
theorem State.empty_valid : (State.empty : State Content View).Valid := by
  constructor
  · intro id value present
    simp [State.empty, State.lookupSlot] at present
  · intro h cell present
    simp [State.empty, State.lookupCell] at present

/-- Releasing a live token changes only its registry slot. -/
theorem release_live (live : state.resolve guard = some slot) :
    release state guard =
      (.ok (), { state with slots := state.slots.set guard.id none }) := by
  simp [release, live]

/-- An invalid or consumed guard cannot be released again. -/
theorem release_invalid (dead : state.resolve guard = none) :
    release state guard = (.error .invalidGuard, state) := by
  simp [release, dead]

/-- A live release actually tombstones the stable identity. -/
theorem release_lookup_none (live : state.resolve guard = some slot) :
    (release state guard).2.lookupSlot guard.id = none := by
  have bound := State.lookupSlot_bound (state.resolve_some_iff.mp live).1
  simp [release_live live, State.lookupSlot, List.getElem?_set_self bound]

/-- The released token no longer resolves, so both use and double drop fail. -/
theorem release_consumes (live : state.resolve guard = some slot) :
    (release state guard).2.resolve guard = none := by
  simp [State.resolve, release_lookup_none live]

/-- A second drop has a checked error and leaves the complete post-release state. -/
theorem release_twice (live : state.resolve guard = some slot) :
    release (release state guard).2 guard =
      (.error .invalidGuard, (release state guard).2) :=
  release_invalid (release_consumes live)

/-- Released guards cannot observe cell contents. -/
theorem current_after_release (live : state.resolve guard = some slot) :
    current (release state guard).2 guard = .error .invalidGuard := by
  simp [current, release_consumes live]

/-- A successful transfer retains the stable id and advances just its generation. -/
theorem transfer_live (live : state.resolve guard = some slot) (view : View) :
    transfer state guard view =
      (.ok ⟨guard.id, guard.generation + 1⟩,
        { state with
          slots := state.slots.set guard.id
            (some { slot with generation := guard.generation + 1, view := view }) }) := by
  simp [transfer, live]

/-- The transferred token resolves to the same underlying cell and mode. -/
theorem transfer_resolves (live : state.resolve guard = some slot) (view : View) :
    (transfer state guard view).2.resolve ⟨guard.id, guard.generation + 1⟩ =
      some { slot with generation := guard.generation + 1, view := view } := by
  have bound := State.lookupSlot_bound (state.resolve_some_iff.mp live).1
  simp [transfer_live live view, State.resolve, State.lookupSlot,
    List.getElem?_set_self bound]

/-- The consumed input of a map cannot be reused with its original view. -/
theorem transfer_consumes (live : state.resolve guard = some slot) (view : View) :
    (transfer state guard view).2.resolve guard = none := by
  have bound := State.lookupSlot_bound (state.resolve_some_iff.mp live).1
  simp [transfer_live live view, State.resolve, State.lookupSlot,
    List.getElem?_set_self bound]

/-- A map does not change any cell contents or policies. -/
theorem transfer_cells (state : State Content View) (guard : Guard) (view : View) :
    (transfer state guard view).2.cells = state.cells := by
  unfold transfer
  split <;> rfl

/-- Release never rolls back a mutation performed while a guard was live. -/
theorem release_cells (state : State Content View) (guard : Guard) :
    (release state guard).2.cells = state.cells := by
  unfold release
  split <;> rfl

/-- Direct replacement preserves the entire guard registry, including generations. -/
theorem replaceCell_slots (state : State Content View) (handle : Handle) (value : Content) :
    (replaceCell state handle value).2.slots = state.slots := by
  unfold replaceCell
  split <;> rfl

/-- Replacement changes the actual current value and retains its policy. -/
theorem replaceCell_lookup {cell : Cell Content}
    (present : state.lookupCell handle = some cell) (value : Content) :
    (replaceCell state handle value).2.lookupCell handle =
      some { cell with value := value } := by
  simp only [replaceCell, present]
  exact List.getElem?_set_self (State.lookupCell_bound present)

/-- A write to one cell leaves distinct identified cells unchanged. -/
theorem replaceCell_other (state : State Content View) (handle other : Handle)
    (value : Content) (different : other.cell ≠ handle.cell) :
    (replaceCell state handle value).2.lookupCell other = state.lookupCell other := by
  unfold replaceCell
  split
  · rfl
  · simp [State.lookupCell, List.getElem?_set_ne (Ne.symm different)]

/-- A guarded write preserves the guard and reads its new value immediately. -/
theorem write_current (live : state.resolve guard = some slot)
    (exclusive : slot.mode = .exclusive) {cell : Cell Content}
    (present : state.lookupCell slot.cell = some cell) (value : Content) :
    current (write state guard value).2 guard = .ok (slot.view, value) := by
  have unchanged : (replaceCell state slot.cell value).2.resolve guard = some slot := by
    simpa only [State.resolve, State.lookupSlot, replaceCell_slots] using live
  simp [write, live, exclusive, current, unchanged, replaceCell_lookup present]

/-- The same handle alias has exactly the same lease observation. -/
theorem alias_lease (state : State Content View) (handle : Handle) :
    state.lease handle.alias = state.lease handle := rfl

/-- A successful checked acquisition issued exactly one fresh guard at the
requested cell/mode/view and retained the current contents of every cell. -/
theorem acquire_success {handle : Handle} {mode : Mode} {view : View}
    {next : Guard} {after : State Content View}
    (success : acquire state handle mode view = (.ok next, after)) :
    after.resolve next = some ⟨handle, mode, 0, view⟩ ∧
      after.cells = state.cells ∧
      ∃ cell, state.lookupCell handle = some cell := by
  cases present : state.lookupCell handle with
  | none => simp [acquire, present] at success
  | some cell =>
    cases mode with
    | shared =>
      simp only [acquire, present] at success
      split at success
      · cases success
      · split at success
        · cases success
        · cases success
          exact ⟨State.issue_resolves state handle .shared view, rfl, cell, rfl⟩
    | exclusive =>
      simp only [acquire, present] at success
      split at success
      · cases success
      · cases success
        exact ⟨State.issue_resolves state handle .exclusive view, rfl, cell, rfl⟩

/-- The acquired guard immediately observes the original current contents. -/
theorem acquire_current {handle : Handle} {mode : Mode} {view : View}
    {next : Guard} {after : State Content View} {cell : Cell Content}
    (success : acquire state handle mode view = (.ok next, after))
    (present : state.lookupCell handle = some cell) :
    current after next = .ok (view, cell.value) := by
  obtain ⟨live, cells, _⟩ := acquire_success success
  have found : after.lookupCell handle = some cell := by
    simpa [State.lookupCell, cells] using present
  simp [current, live, found]

/-- Every issued guard can be released once, independently of its data projection. -/
theorem release_after_acquire {handle : Handle} {mode : Mode} {view : View}
    {next : Guard} {after : State Content View}
    (success : acquire state handle mode view = (.ok next, after)) :
    release after next = (.ok (), { after with slots := after.slots.set next.id none }) :=
  release_live (acquire_success success).1

/-- The fresh cell has the exact inserted contents and policy. -/
theorem State.insert_lookup (state : State Content View) (policy : Policy) (value : Content) :
    (state.insert policy value).2.lookupCell (state.insert policy value).1 =
      some ⟨value, policy⟩ := by
  simp [State.insert, State.lookupCell]

/-- Adding a cell cannot change an existing identified cell. -/
theorem State.insert_lookup_old (state : State Content View) (policy : Policy) (value : Content)
    (handle : Handle) (bound : handle.cell < state.cells.length) :
    (state.insert policy value).2.lookupCell handle = state.lookupCell handle := by
  simp [State.insert, State.lookupCell, List.getElem?_append_left bound]

end Solanalib.Specs.Core.Borrow
