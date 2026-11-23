/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Pinocchio09.AccountState
import Solanalib.Specs.Pinocchio.AccountInfo

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.Pinocchio09

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.PinocchioAccount
open AccountsV1

instance dataPresentDec (before : State) (handle : Handle) : Decidable (DataPresent before handle)
  :=
  match found : before.content handle .data with
  | some (.data data) => isTrue ⟨data, found⟩
  | some (.lamports _) => isFalse (by rintro ⟨data, h⟩; rw [found] at h; cases h)
  | none => isFalse (by rintro ⟨data, h⟩; rw [found] at h; cases h)

instance lamportsPresentDec (before : State) (handle : Handle) :
    Decidable (∃ value, before.content handle .lamports = some (.lamports value)) :=
  match found : before.content handle .lamports with
  | some (.lamports value) => isTrue ⟨value, rfl⟩
  | some (.data _) => isFalse (by rintro ⟨value, h⟩; cases h)
  | none => isFalse (by rintro ⟨value, h⟩; cases h)

theorem fieldPresent_iff (before : State) (handle : Handle) (field : Field) :
    FieldPresent before handle field ↔
      ∃ header, before.lookup handle = some header ∧
        ∃ cell, before.1.lookupCell (header.field field) = some cell := by
  constructor
  · rintro ⟨header, cell, h, c⟩; exact ⟨header, h, cell, c⟩
  · rintro ⟨header, h, cell, c⟩; exact ⟨header, cell, h, c⟩

instance fieldPresentDec (before : State) (handle : Handle) (field : Field) :
    Decidable (FieldPresent before handle field) :=
  decidable_of_iff _ (fieldPresent_iff before handle field).symm

/-- Mapping an exclusive byte view may change its bytes while preserving the
allocation, lengths, signed counter and every byte outside the current view. -/
def mapFootprint (mode : Mode) (view : View) (old next : Content) : Prop :=
  match mode, old, next with
  | .exclusive, .data old, .data next =>
    let range := match view with | .whole => (0, old.dataLen) | .bytes o n => (o, n)
    next.dataLen = old.dataLen ∧ next.entryLen = old.entryLen ∧
    next.resizeDelta = old.resizeDelta ∧ next.backing.length = old.backing.length ∧
    next.backing.take range.1 = old.backing.take range.1 ∧
    next.backing.drop (range.1 + range.2) = old.backing.drop (range.1 + range.2)
  | _, _, _ => next = old

instance mapFootprintDec (mode : Mode) (view : View) (old next : Content) :
    Decidable (mapFootprint mode view old next) := by
  unfold mapFootprint
  split <;> infer_instance

theorem frame_iff (before after : Borrow.State Content View) (guard : Guard) :
    Borrow.CallbackFrame mapFootprint before after guard ↔
      after.Valid ∧ Borrow.History before after ∧
      (∀ k ∈ List.range before.cells.length, ∀ old, before.cells[k]? = some old →
        ∃ next, after.lookupCell ⟨k⟩ = some next ∧ next.policy = old.policy) ∧
      after.resolve guard = before.resolve guard ∧
      (∀ slot, before.resolve guard = some slot → ∀ old, before.lookupCell slot.cell = some old →
        ∀ next, after.lookupCell slot.cell = some next →
          mapFootprint slot.mode slot.view old.value next.value) := by
  constructor
  · rintro ⟨valid, history, cells, held, changes⟩
    exact ⟨valid, history, (lookupCell_forall_iff before _).mp cells, held,
      fun slot live old present next found => changes slot old next live present found⟩
  · rintro ⟨valid, history, cells, held, changes⟩
    exact ⟨valid, history, (lookupCell_forall_iff before _).mpr cells, held,
      fun slot old next live present found => changes slot live old present next found⟩

instance mapFrameDec (before after : Borrow.State Content View) (guard : Guard) :
    Decidable (Borrow.CallbackFrame mapFootprint before after guard) :=
  decidable_of_iff _ (frame_iff before after guard).symm

abbrev mapProfile : MapProfile := ⟨guardProfile, String, Json, mapFootprint⟩

instance mapExitFrameDec (before : guardProfile.World) (guard : Guard) :
    (produced : Outcome guardProfile.World View String Json) →
      Decidable (mapFrame mapProfile before guard produced)
  | .returned _ after | .unwound _ after => mapFrameDec before.1 after.1 guard
  | .terminated _ => isTrue trivial

abbrev MapStep := guardProfile.World → Handle → View → Outcome guardProfile.World View String Json

def mapArgs (guard : Guard) (step : MapStep) : MapArgs mapProfile :=
  ⟨guard, fun before cell view produced => step before cell view = produced⟩

theorem mapReady_iff (before : guardProfile.World) (guard : Guard) (step : MapStep) :
    mapSafe mapProfile before (mapArgs guard step) ↔
      ∀ slot, before.1.resolve guard = some slot →
        ∀ cell, before.1.lookupCell slot.cell = some cell →
          mapFrame mapProfile before guard (step before slot.cell slot.view) := by
  constructor
  · intro safe slot live cell present
    exact safe slot cell live present _ rfl
  · intro safe slot cell live present produced called
    change step before slot.cell slot.view = produced at called
    cases called
    exact safe slot live cell present

def mapReadyDec (before : guardProfile.World) (guard : Guard) (step : MapStep) :
    Decidable ((mapFamily.contract mapProfile).requires before (mapArgs guard step)) :=
  decidable_of_iff _ (mapReady_iff before guard step).symm

end SolanalibTest.Conformance.Library.Families.Pinocchio09
