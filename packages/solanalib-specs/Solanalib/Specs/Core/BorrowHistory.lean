/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorrowFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borrow

universe u v

variable {Content : Type u} {View : Type v}

/-- Allowed evolution of an already allocated guard identity. A tombstone stays
dead; a live identity keeps its cell/mode and its generation cannot decrease. -/
def SlotHistory (before after : Option (Slot View)) : Prop :=
  match before, after with
  | none, none => True
  | none, some _ => False
  | some _, none => True
  | some old, some next =>
    next.cell = old.cell ∧ next.mode = old.mode ∧ old.generation ≤ next.generation

/-- A callback may acquire, transfer and release other guards, but it may not
reuse an allocated identity or revive a consumed generation. -/
structure History (before after : State Content View) : Prop where
  /-- Previously allocated stable guard identities remain allocated. -/
  frontier : before.slots.length ≤ after.slots.length
  /-- Each old identity remains dead or keeps its cell, mode, and advancing generation. -/
  entries : ∀ id, id < before.slots.length →
    SlotHistory (before.lookupSlot id) (after.lookupSlot id)

/-- A consumed token is either tombstoned or older than the live token for its identity. -/
def Retired (state : State Content View) (guard : Guard) : Prop :=
  guard.id < state.slots.length ∧
    match state.lookupSlot guard.id with
    | none => True
    | some slot => guard.generation < slot.generation

/-- An unchanged world respects every previously allocated identity. -/
theorem History.refl (state : State Content View) : History state state := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro id bound
  cases state.lookupSlot id <;> simp [SlotHistory]

/-- Changing only cell contents does not change the history of any token. -/
theorem History.of_slots_eq {before after : State Content View}
    (same : after.slots = before.slots) : History before after := by
  refine ⟨by simp [same], ?_⟩
  intro id bound
  have equal : after.lookupSlot id = before.lookupSlot id := by simp [State.lookupSlot, same]
  rw [equal]
  cases before.lookupSlot id <;> simp [SlotHistory]

/-- Identity and generation preservation composes across finite callback effects. -/
theorem History.trans {first middle last : State Content View}
    (one : History first middle) (two : History middle last) : History first last := by
  refine ⟨Nat.le_trans one.frontier two.frontier, ?_⟩
  intro id bound
  have left := one.entries id bound
  have right := two.entries id (Nat.lt_of_lt_of_le bound one.frontier)
  cases a : first.lookupSlot id <;> cases b : middle.lookupSlot id <;>
    cases c : last.lookupSlot id <;> simp_all [SlotHistory]
  omega

/-- A retired token cannot resolve to a live guard. -/
theorem Retired.unusable {state : State Content View} {guard : Guard}
    (retired : Retired state guard) : state.resolve guard = none := by
  unfold State.resolve
  cases found : state.lookupSlot guard.id with
  | none => simp
  | some slot =>
    have older : guard.generation < slot.generation := by
      simpa [Retired, found] using retired.2
    have different : slot.generation ≠ guard.generation := by omega
    simp [different]

/-- Once consumed, a token stays consumed under every admitted history extension. -/
theorem Retired.persists {before after : State Content View} {guard : Guard}
    (retired : Retired before guard) (history : History before after) : Retired after guard := by
  refine ⟨Nat.lt_of_lt_of_le retired.1 history.frontier, ?_⟩
  have step := history.entries guard.id retired.1
  cases old : before.lookupSlot guard.id <;> cases next : after.lookupSlot guard.id <;>
    simp_all [Retired, SlotHistory]
  omega

/-- A release marks its actual live token as permanently retired. -/
theorem release_retired {state : State Content View} {guard : Guard} {slot : Slot View}
    (live : state.resolve guard = some slot) : Retired (release state guard).2 guard := by
  have bound := State.lookupSlot_bound (state.resolve_some_iff.mp live).1
  refine ⟨?_, ?_⟩
  · simpa [release_live live] using bound
  · simp [release_lookup_none live]

/-- Mapping consumes the original token even though the same lease stays live. -/
theorem transfer_retired {state : State Content View} {guard : Guard} {slot : Slot View}
    (live : state.resolve guard = some slot) (view : View) :
    Retired (transfer state guard view).2 guard := by
  have bound := State.lookupSlot_bound (state.resolve_some_iff.mp live).1
  refine ⟨?_, ?_⟩
  · simpa [transfer_live live view] using bound
  · simp [transfer_live live view, State.lookupSlot, List.getElem?_set_self bound]

/-- Appending a new acquisition preserves all earlier histories. -/
theorem issue_history (state : State Content View) (handle : Handle)
    (mode : Mode) (view : View) : History state (state.issue handle mode view).2 := by
  refine ⟨by simp [State.issue], ?_⟩
  intro id bound
  rw [State.issue_lookup_old state handle mode view bound]
  cases state.lookupSlot id <;> simp [SlotHistory]

/-- Release preserves every other identity and never revives the released slot. -/
theorem release_history (state : State Content View) (guard : Guard) :
    History state (release state guard).2 := by
  cases live : state.resolve guard with
  | none => simpa [release, live] using History.refl state
  | some slot =>
    refine ⟨by simp [release_live live], ?_⟩
    intro id bound
    by_cases same : guard.id = id
    · subst id
      rw [release_lookup_none live]
      cases state.lookupSlot guard.id <;> trivial
    · simp only [release_live live, State.lookupSlot, List.getElem?_set_ne same]
      cases state.slots[id]? with
      | none => trivial
      | some entry => cases entry <;> simp [SlotHistory]

/-- Transfer advances one generation, retaining its cell and mode. -/
theorem transfer_history (state : State Content View) (guard : Guard) (view : View) :
    History state (transfer state guard view).2 := by
  cases live : state.resolve guard with
  | none => simpa [transfer, live] using History.refl state
  | some slot =>
    have facts := state.resolve_some_iff.mp live
    have bound := State.lookupSlot_bound facts.1
    refine ⟨by simp [transfer_live live view], ?_⟩
    intro id old
    by_cases same : guard.id = id
    · subst id
      simp [transfer_live live view, State.lookupSlot, List.getElem?_set_self bound,
        (state.lookupSlot_some_iff guard.id slot).mp facts.1, SlotHistory, facts.2]
    · simp only [transfer_live live view, State.lookupSlot, List.getElem?_set_ne same]
      cases state.slots[id]? with
      | none => trivial
      | some entry => cases entry <;> simp [SlotHistory]

/-- Direct content replacement cannot revive any consumed token. -/
theorem replaceCell_history (state : State Content View) (handle : Handle) (value : Content) :
    History state (replaceCell state handle value).2 :=
  History.of_slots_eq (replaceCell_slots state handle value)

/-- A guarded write changes contents without altering token history. -/
theorem write_history (state : State Content View) (guard : Guard) (value : Content) :
    History state (write state guard value).2 := by
  unfold write
  split
  · exact History.refl state
  · split
    · exact replaceCell_history state _ value
    · exact History.refl state

/-- Checked acquisition either leaves history unchanged or appends a fresh id. -/
theorem acquire_history (state : State Content View) (handle : Handle) (mode : Mode) (view : View) :
    History state (acquire state handle mode view).2 := by
  cases present : state.lookupCell handle with
  | none => simpa [acquire, present] using History.refl state
  | some cell =>
    cases mode with
    | shared =>
      simp only [acquire, present]
      split
      · exact History.refl state
      · split
        · exact History.refl state
        · exact issue_history state handle .shared view
    | exclusive =>
      simp only [acquire, present]
      split
      · exact History.refl state
      · exact issue_history state handle .exclusive view

/-- Cell insertion does not allocate or revive a guard identity. -/
theorem insert_history (state : State Content View) (policy : Policy) (value : Content) :
    History state (state.insert policy value).2 := History.of_slots_eq rfl

end Solanalib.Specs.Core.Borrow
