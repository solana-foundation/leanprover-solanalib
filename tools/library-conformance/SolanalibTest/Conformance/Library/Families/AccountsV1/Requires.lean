/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AccountsV1.Common
import Solanalib.Specs.Core.AccountViewMapFamily
import Solanalib.Specs.Core.AccountInfoContracts

/-!
# Decisions of the registered preconditions of family `AccountsV1`

Decidable instances for the predicates the registered contracts require, each
obtained from an iff lemma with a bounded form: quantifiers over guard
identities and cell handles range over the finite slot and cell lists, and
quantifiers over the value an `Option` holds become a match. Nothing here
restates a predicate; each instance decides the registered one.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AccountsV1

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-! ## Quantifiers over optional values -/

instance decForallSome {α : Type} (o : Option α) (P : α → Prop) [∀ x, Decidable (P x)] :
    Decidable (∀ x, o = some x → P x) :=
  match o with
  | none => isTrue fun _ h => by cases h
  | some y =>
    if h : P y then isTrue fun x hx => by cases hx; exact h
    else isFalse fun f => h (f y rfl)

instance decExistsSome {α : Type} (o : Option α) : Decidable (∃ x, o = some x) :=
  match o with
  | some y => isTrue ⟨y, rfl⟩
  | none => isFalse fun ⟨_, h⟩ => by cases h

instance decExistsSomeAnd {α : Type} (o : Option α) (P : α → Prop) [∀ x, Decidable (P x)] :
    Decidable (∃ x, o = some x ∧ P x) :=
  match o with
  | some y =>
    if h : P y then isTrue ⟨y, rfl, h⟩
    else isFalse fun ⟨x, hx, hp⟩ => by cases hx; exact h hp
  | none => isFalse fun ⟨_, h, _⟩ => by cases h

theorem forall_eq_iff {α : Type} {a : α} {P : α → Prop} : (∀ p, a = p → P p) ↔ P a :=
  ⟨fun h => h a rfl, fun h _ e => e ▸ h⟩

/-! ## Quantifiers over guard identities and cell handles -/

theorem lookupSlot_forall_iff {C V : Type} (s : Borrow.State C V) (Q : Borrow.Slot V → Prop) :
    (∀ id slot, s.lookupSlot id = some slot → Q slot) ↔
      ∀ e ∈ s.slots, ∀ slot, e = some slot → Q slot := by
  constructor
  · intro h e member slot same
    obtain ⟨id, at_id⟩ := List.mem_iff_getElem?.mp member
    exact h id slot (by simp [Borrow.State.lookupSlot, at_id, same])
  · intro h id slot found
    simp only [Borrow.State.lookupSlot, Option.bind_eq_some_iff] at found
    obtain ⟨e, at_id, same⟩ := found
    exact h e (List.mem_of_getElem? at_id) slot (by simpa using same)

theorem lookupCell_forall_iff {C V : Type} (s : Borrow.State C V)
    (R : Borrow.Handle → Borrow.Cell C → Prop) :
    (∀ h c, s.lookupCell h = some c → R h c) ↔
      ∀ k ∈ List.range s.cells.length, ∀ c, s.cells[k]? = some c → R ⟨k⟩ c := by
  constructor
  · intro h k _ c found
    exact h ⟨k⟩ c found
  · intro h handle c found
    obtain ⟨k⟩ := handle
    have bound : k < s.cells.length := (List.getElem?_eq_some_iff.mp found).1
    exact h k (List.mem_range.mpr bound) c found

/-- `Borrow.State.Valid`: live guards name existing cells; per cell at most one
exclusive lease, none beside shared ones, and shared ones within its policy. -/
instance validDecidable {C V : Type} (s : Borrow.State C V) : Decidable s.Valid :=
  decidable_of_iff _ (and_congr (lookupSlot_forall_iff s _) (lookupCell_forall_iff s _)).symm

instance slotHistoryDecidable {V : Type} [DecidableEq V] :
    (a b : Option (Borrow.Slot V)) → Decidable (Borrow.SlotHistory a b)
  | none, none => isTrue trivial
  | none, some _ => isFalse id
  | some _, none => isTrue trivial
  | some o, some n =>
    inferInstanceAs (Decidable (n.cell = o.cell ∧ n.mode = o.mode ∧ o.generation ≤ n.generation))

theorem history_iff {C V : Type} (before after : Borrow.State C V) :
    Borrow.History before after ↔
      before.slots.length ≤ after.slots.length ∧
        ∀ id ∈ List.range before.slots.length,
          Borrow.SlotHistory (before.lookupSlot id) (after.lookupSlot id) := by
  constructor
  · rintro ⟨frontier, entries⟩
    exact ⟨frontier, fun id member => entries id (List.mem_range.mp member)⟩
  · rintro ⟨frontier, entries⟩
    exact ⟨frontier, fun id bound => entries id (List.mem_range.mpr bound)⟩

instance historyDecidable {C V : Type} [DecidableEq V] (before after : Borrow.State C V) :
    Decidable (Borrow.History before after) :=
  decidable_of_iff _ (history_iff before after).symm

/-! ## AccountView guard mapping -/

namespace View

open Solanalib.Specs.Core.AccountView

instance accountValidDecidable (a : Account) : Decidable a.Valid := by
  unfold Account.Valid; infer_instance

instance sliceValidDecidable (v : Slice) (a : Account) : Decidable (v.ValidFor a) := by
  unfold Slice.ValidFor; infer_instance

instance poolWellFormedDecidable {V : Type} (s : Borrow.State Account V) :
    Decidable (PoolWellFormed s) := by
  unfold PoolWellFormed; infer_instance

instance sliceFootprintDecidable (m : Borrow.Mode) (v : Slice) (a b : Account) :
    Decidable (sliceFootprint m v a b) := by
  unfold sliceFootprint; infer_instance

theorem frame_iff {before after : State} {guard : Guard} :
    Borrow.CallbackFrame sliceFootprint before after guard ↔
      after.Valid ∧ Borrow.History before after ∧
      (∀ k ∈ List.range before.cells.length, ∀ old, before.cells[k]? = some old →
        ∃ next, after.lookupCell ⟨k⟩ = some next ∧ next.policy = old.policy) ∧
      after.resolve guard = before.resolve guard ∧
      (∀ slot, before.resolve guard = some slot → ∀ old, before.lookupCell slot.cell = some old →
        ∀ next, after.lookupCell slot.cell = some next →
          sliceFootprint slot.mode slot.view old.value next.value) := by
  constructor
  · rintro ⟨valid, history, cells, held, changes⟩
    exact ⟨valid, history, (lookupCell_forall_iff before _).mp cells, held,
      fun slot live old present next found => changes slot old next live present found⟩
  · rintro ⟨valid, history, cells, held, changes⟩
    exact ⟨valid, history, (lookupCell_forall_iff before _).mpr cells, held,
      fun slot old next live present found => changes slot live old present next found⟩

instance frameDecidable (before after : State) (guard : Guard) :
    Decidable (Borrow.CallbackFrame sliceFootprint before after guard) :=
  decidable_of_iff _ (frame_iff (before := before) (after := after) (guard := guard)).symm

/-- The callback frame of one exit, at the byte-range index. -/
instance admissibleDecidable {U T : Type} (before : State) (guard : Guard) :
    (produced : Outcome (State × Unit) (Except Empty Slice) U T) →
      Decidable (Borrow.CallbackAdmissible sliceFootprint before guard produced)
  | .returned _ after => frameDecidable before after.1 guard
  | .unwound _ after => frameDecidable before after.1 guard
  | .terminated _ => isTrue trivial

end View

end SolanalibTest.Conformance.Library.Families.AccountsV1
