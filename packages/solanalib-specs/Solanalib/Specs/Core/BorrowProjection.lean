/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Borrow

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borrow

universe u v w

variable {Content : Type u} {Source : Type v} {Target : Type w}

/-- Changing the interpretation of a target does not change its lease,
generation, cell identity or acquisition mode. -/
def Slot.mapView (project : Source → Target) (slot : Slot Source) : Slot Target :=
  ⟨slot.cell, slot.mode, slot.generation, project slot.view⟩

/-- One physical guard world may serve an API that observes only lease counts
and another API that observes the complete typed target. Tombstones are retained. -/
def State.mapView (project : Source → Target) (state : State Content Source) :
    State Content Target :=
  ⟨state.cells, state.slots.map (Option.map (Slot.mapView project))⟩

theorem State.mapView_lookupCell (project : Source → Target) (state : State Content Source)
    (handle : Handle) : (state.mapView project).lookupCell handle = state.lookupCell handle := rfl

theorem State.mapView_lookupSlot (project : Source → Target) (state : State Content Source)
    (id : Nat) : (state.mapView project).lookupSlot id =
      (state.lookupSlot id).map (Slot.mapView project) := by
  simp only [State.mapView, State.lookupSlot, List.getElem?_map]
  cases state.slots[id]? <;> rfl

theorem State.mapView_resolve (project : Source → Target) (state : State Content Source)
    (guard : Guard) : (state.mapView project).resolve guard =
      (state.resolve guard).map (Slot.mapView project) := by
  simp only [State.resolve, State.mapView_lookupSlot]
  cases found : state.lookupSlot guard.id with
  | none => rfl
  | some slot =>
    simp only [Option.map_some, Option.bind_some, Slot.mapView]
    split <;> rfl

theorem State.mapView_count (project : Source → Target) (state : State Content Source)
    (handle : Handle) (mode : Mode) :
    (state.mapView project).count handle mode = state.count handle mode := by
  simp only [State.count, State.mapView, List.countP_map]
  congr 1
  funext entry
  cases entry <;> rfl

theorem State.mapView_sharedCount (project : Source → Target) (state : State Content Source)
    (handle : Handle) : (state.mapView project).sharedCount handle = state.sharedCount handle :=
  state.mapView_count project handle .shared

theorem State.mapView_exclusiveCount (project : Source → Target) (state : State Content Source)
    (handle : Handle) : (state.mapView project).exclusiveCount handle = state.exclusiveCount handle
      :=
  state.mapView_count project handle .exclusive

theorem State.mapView_lease (project : Source → Target) (state : State Content Source)
    (handle : Handle) : (state.mapView project).lease handle = state.lease handle := by
  simp only [State.lease, State.mapView_exclusiveCount, State.mapView_sharedCount]

/-- Lease well-formedness depends on cell identities and counts, so even a
non-injective target projection preserves and reflects the same protocol. -/
theorem State.mapView_valid (project : Source → Target) (state : State Content Source) :
    (state.mapView project).Valid ↔ state.Valid := by
  constructor
  · intro valid
    constructor
    · intro id slot found
      have mapped : (state.mapView project).lookupSlot id = some (slot.mapView project) := by
        rw [state.mapView_lookupSlot project id, found]
        rfl
      exact valid.1 id (slot.mapView project) mapped
    · intro handle cell present
      simpa only [State.mapView_lookupCell, State.mapView_exclusiveCount,
        State.mapView_sharedCount] using valid.2 handle cell present
  · intro valid
    constructor
    · intro id slot found
      rw [state.mapView_lookupSlot project id] at found
      obtain ⟨original, present, rfl⟩ := Option.map_eq_some_iff.mp found
      exact valid.1 id original present
    · intro handle cell present
      simpa only [State.mapView_lookupCell, State.mapView_exclusiveCount,
        State.mapView_sharedCount] using valid.2 handle cell present

theorem State.mapView_issue (project : Source → Target) (state : State Content Source)
    (handle : Handle) (mode : Mode) (view : Source) :
    (state.mapView project).issue handle mode (project view) =
      ((state.issue handle mode view).1, (state.issue handle mode view).2.mapView project) := by
  simp [State.issue, State.mapView, Slot.mapView]

theorem State.mapView_release (project : Source → Target) (state : State Content Source)
    (guard : Guard) :
    release (state.mapView project) guard =
      ((release state guard).1, (release state guard).2.mapView project) := by
  simp only [release, State.mapView_resolve]
  cases state.resolve guard with
  | none => rfl
  | some slot => simp [State.mapView, List.map_set]

theorem State.mapView_transfer (project : Source → Target) (state : State Content Source)
    (guard : Guard) (view : Source) :
    transfer (state.mapView project) guard (project view) =
      ((transfer state guard view).1, (transfer state guard view).2.mapView project) := by
  simp only [transfer, State.mapView_resolve]
  cases state.resolve guard with
  | none => rfl
  | some slot => simp [State.mapView, List.map_set, Slot.mapView]

/-- Contents are current on both sides, including after a guarded write. -/
theorem State.mapView_replace (project : Source → Target) (state : State Content Source)
    (handle : Handle) (value : Content) :
    replaceCell (state.mapView project) handle value =
      ((replaceCell state handle value).1, (replaceCell state handle value).2.mapView project) := by
  simp only [replaceCell, State.mapView_lookupCell]
  cases state.lookupCell handle <;> rfl

end Solanalib.Specs.Core.Borrow
