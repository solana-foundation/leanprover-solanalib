/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorrowProjection

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borrow

universe u v w

variable {Source : Type u} {Target : Type v} {View : Type w}

/-- Observing a cell through a different value type retains its acquisition
policy. The handle and every guard continue to name the same cell. -/
def Cell.mapContent (project : Source → Target) (cell : Cell Source) : Cell Target :=
  ⟨project cell.value, cell.policy⟩

/-- A content projection does not create a second lease world. It retains
the complete slot table, including target views, generations and tombstones. -/
def State.mapContent (project : Source → Target) (state : State Source View) :
    State Target View :=
  ⟨state.cells.map (Cell.mapContent project), state.slots⟩

theorem State.mapContent_lookupCell (project : Source → Target) (state : State Source View)
    (handle : Handle) : (state.mapContent project).lookupCell handle =
      (state.lookupCell handle).map (Cell.mapContent project) := by
  simp only [State.mapContent, State.lookupCell, List.getElem?_map]

theorem State.mapContent_lookupSlot (project : Source → Target) (state : State Source View)
    (id : Nat) : (state.mapContent project).lookupSlot id = state.lookupSlot id := rfl

theorem State.mapContent_resolve (project : Source → Target) (state : State Source View)
    (guard : Guard) : (state.mapContent project).resolve guard = state.resolve guard := rfl

theorem State.mapContent_count (project : Source → Target) (state : State Source View)
    (handle : Handle) (mode : Mode) :
    (state.mapContent project).count handle mode = state.count handle mode := rfl

theorem State.mapContent_sharedCount (project : Source → Target) (state : State Source View)
    (handle : Handle) :
    (state.mapContent project).sharedCount handle = state.sharedCount handle := rfl

theorem State.mapContent_exclusiveCount (project : Source → Target) (state : State Source View)
    (handle : Handle) :
    (state.mapContent project).exclusiveCount handle = state.exclusiveCount handle := rfl

theorem State.mapContent_lease (project : Source → Target) (state : State Source View)
    (handle : Handle) : (state.mapContent project).lease handle = state.lease handle := rfl

/-- Even a non-injective value observation preserves and reflects validity,
because policies, identities and the complete live lease table are retained. -/
theorem State.mapContent_valid (project : Source → Target) (state : State Source View) :
    (state.mapContent project).Valid ↔ state.Valid := by
  constructor
  · intro valid
    constructor
    · intro id slot found
      obtain ⟨cell, present⟩ := valid.1 id slot found
      rw [state.mapContent_lookupCell project slot.cell] at present
      obtain ⟨original, present, _⟩ := Option.map_eq_some_iff.mp present
      exact ⟨original, present⟩
    · intro handle cell present
      have projected : (state.mapContent project).lookupCell handle =
          some (cell.mapContent project) := by
        rw [state.mapContent_lookupCell project handle, present]
        rfl
      exact valid.2 handle (cell.mapContent project) projected
  · intro valid
    constructor
    · intro id slot found
      obtain ⟨cell, present⟩ := valid.1 id slot found
      refine ⟨cell.mapContent project, ?_⟩
      rw [state.mapContent_lookupCell project slot.cell, present]
      rfl
    · intro handle cell present
      rw [state.mapContent_lookupCell project handle] at present
      obtain ⟨original, found, rfl⟩ := Option.map_eq_some_iff.mp present
      exact valid.2 handle original found

theorem State.mapContent_issue (project : Source → Target) (state : State Source View)
    (handle : Handle) (mode : Mode) (view : View) :
    (state.mapContent project).issue handle mode view =
      ((state.issue handle mode view).1, (state.issue handle mode view).2.mapContent project) := rfl

theorem State.mapContent_acquire (project : Source → Target) (state : State Source View)
    (handle : Handle) (mode : Mode) (view : View) :
    acquire (state.mapContent project) handle mode view =
      ((acquire state handle mode view).1, (acquire state handle mode view).2.mapContent project)
        := by
  cases found : state.lookupCell handle with
  | none => simp [acquire, State.mapContent_lookupCell, found]
  | some cell =>
    cases mode with
    | shared =>
      by_cases busy : state.exclusiveCount handle ≠ 0
      · simp [acquire, State.mapContent_lookupCell, found,
          State.mapContent_exclusiveCount, busy]
      · by_cases full : cell.policy.sharedLimit ≤ state.sharedCount handle
        all_goals simp [acquire, State.mapContent_lookupCell, found, Cell.mapContent,
          State.mapContent_exclusiveCount, State.mapContent_sharedCount,
          busy, full, State.mapContent_issue]
    | exclusive =>
      by_cases busy : state.exclusiveCount handle ≠ 0 ∨ state.sharedCount handle ≠ 0
      all_goals simp [acquire, State.mapContent_lookupCell, found, Cell.mapContent,
        State.mapContent_exclusiveCount, State.mapContent_sharedCount,
        busy, State.mapContent_issue]

theorem State.mapContent_release (project : Source → Target) (state : State Source View)
    (guard : Guard) :
    release (state.mapContent project) guard =
      ((release state guard).1, (release state guard).2.mapContent project) := by
  simp only [release, State.mapContent_resolve]
  cases state.resolve guard <;> rfl

theorem State.mapContent_replace (project : Source → Target) (state : State Source View)
    (handle : Handle) (value : Source) :
    replaceCell (state.mapContent project) handle (project value) =
      ((replaceCell state handle value).1, (replaceCell state handle value).2.mapContent project)
        := by
  simp only [replaceCell, State.mapContent_lookupCell]
  cases state.lookupCell handle with
  | none => rfl
  | some cell => simp [State.mapContent, List.map_set, Cell.mapContent]

variable {Content : Type u} {SourceView : Type v} {TargetView : Type w}

/-- Acquisition is compatible with the existing target-view projection too.
Together with content projection, this connects a typed account world to its
lease-only CPI observation without changing any borrow decision. -/
theorem State.mapView_acquire (project : SourceView → TargetView)
    (state : State Content SourceView) (handle : Handle) (mode : Mode) (view : SourceView) :
    acquire (state.mapView project) handle mode (project view) =
      ((acquire state handle mode view).1, (acquire state handle mode view).2.mapView project) := by
  cases found : state.lookupCell handle with
  | none => simp [acquire, State.mapView_lookupCell, found]
  | some cell =>
    cases mode with
    | shared =>
      by_cases busy : state.exclusiveCount handle ≠ 0
      · simp [acquire, State.mapView_lookupCell, found, State.mapView_exclusiveCount, busy]
      · by_cases full : cell.policy.sharedLimit ≤ state.sharedCount handle
        all_goals simp [acquire, State.mapView_lookupCell, found, State.mapView_exclusiveCount,
          State.mapView_sharedCount, busy, full, State.mapView_issue]
    | exclusive =>
      by_cases busy : state.exclusiveCount handle ≠ 0 ∨ state.sharedCount handle ≠ 0
      all_goals simp [acquire, State.mapView_lookupCell, found, State.mapView_exclusiveCount,
        State.mapView_sharedCount, busy, State.mapView_issue]

end Solanalib.Specs.Core.Borrow
