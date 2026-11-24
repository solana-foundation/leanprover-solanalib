/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorViewsOwned

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorViews

variable {Payload Aux : Type}

/-- A live wrapper observation resolves to one actual cell and current value;
neither the reference token nor the getter carries a cached payload. -/
theorem current_iff {store : Store Payload} {guard : Borrow.Guard} {wrapper : Wrapper Payload} :
    current store guard = some wrapper ↔
      ∃ slot cell, store.resolve guard = some slot ∧
        store.lookupCell slot.cell = some cell ∧ cell.value = some wrapper := by
  cases live : store.resolve guard with
  | none => simp [current, Borrow.current, live]
  | some slot =>
    cases present : store.lookupCell slot.cell with
    | none => simp [current, Borrow.current, live, present]
    | some cell => simp [current, Borrow.current, live, present]

/-- Every admitted shared getter has the cell required by clone placement. -/
theorem currentCell_of_current {store : Store Payload} {guard : Borrow.Guard}
    {wrapper : Wrapper Payload} (present : current store guard = some wrapper) :
    ∃ cell, currentCell store guard = some cell ∧ cell.value = some wrapper := by
  obtain ⟨slot, cell, live, found, value⟩ := current_iff.mp present
  exact ⟨cell, by simp [currentCell, live, found], value⟩

/-- Exclusive field writes are defined, retain their loan and immediately
expose the replacement. The old wrapper metadata is preserved exactly. -/
theorem writePayload_current {store : Store Payload} {guard : Borrow.Guard}
    {wrapper : Wrapper Payload} (present : current store guard = some wrapper)
    (exclusive : ∃ slot, store.resolve guard = some slot ∧ slot.mode = .exclusive)
    (payload : Payload) :
    (writePayload store ⟨guard, true⟩ payload).1 = .ok () ∧
      current (writePayload store ⟨guard, true⟩ payload).2 guard =
        some (wrapper.withPayload payload) := by
  obtain ⟨slot, cell, live, found, value⟩ := current_iff.mp present
  obtain ⟨selected, same, mode⟩ := exclusive
  have equal : selected = slot := Option.some.inj (same.symm.trans live)
  subst selected
  simp only [writePayload, ↓reduceIte, present]
  constructor
  · simp [Borrow.write, live, mode, Borrow.replaceCell, found]
  · have written := Borrow.write_current live mode found (some (wrapper.withPayload payload))
    simp [current, written]

/-- A mutable field store changes the value read through that same reference
without a release-time copyback. The returned reference remains the same token. -/
theorem read_after_write {store : Store Payload} {guard : Borrow.Guard}
    {wrapper : Wrapper Payload} (present : current store guard = some wrapper)
    (exclusive : ∃ slot, store.resolve guard = some slot ∧ slot.mode = .exclusive)
    (payload : Payload) :
    readPayload (writePayload store ⟨guard, true⟩ payload).2 ⟨guard, true⟩ = some payload := by
  simp [readPayload, (writePayload_current present exclusive payload).2, Wrapper.withPayload]

/-- Two references with the same parent observe the same current value even
if one is shared and the other mutable. Permissions still differ for writes. -/
theorem read_permission_irrelevant (store : Store Payload) (guard : Borrow.Guard)
    (first second : Bool) :
    readPayload store ⟨guard, first⟩ = readPayload store ⟨guard, second⟩ := rfl

/-- Releasing the parent loan invalidates every payload view obtained from it. -/
theorem read_after_release {store : Store Payload} {guard : Borrow.Guard}
    {slot : Borrow.Slot Unit} (live : store.resolve guard = some slot) (mutable : Bool) :
    readPayload (Borrow.release store guard).2 ⟨guard, mutable⟩ = none := by
  simp [readPayload, current, Borrow.current_after_release live]

/-- Releasing that same loan also invalidates an AccountInfo reference; a
matching external identity alone cannot restore a consumed source lifetime. -/
theorem info_after_release (storage : InfoStorage) {store : Store Payload} {guard : Borrow.Guard}
    {slot : Borrow.Slot Unit} (live : store.resolve guard = some slot) (location : InfoLocation) :
    readInfo storage (Borrow.release store guard).2 ⟨guard, location⟩ = none := by
  simp [readInfo, current, Borrow.current_after_release live]

/-- Owned-info references designate the field of the selected wrapper, preserving
the distinction from a second wrapper with equal AccountInfo metadata. -/
theorem infoReference_owned (before : World Payload Aux) (guard : Borrow.Guard)
    (wrapper : Wrapper Payload) (present : current before.1 guard = some wrapper)
    {slot : Borrow.Slot Unit} (live : before.1.resolve guard = some slot) :
    infoReference .owned before guard = (⟨guard, .field slot.cell⟩, before) := by
  simp [infoReference, present, infoLocation, live]

/-- The complete shared-info reference reads exactly the selected AccountInfo of the wrapper,
retaining both independent Rc cell identities and owner identity. -/
theorem read_infoReference (storage : InfoStorage) (before : World Payload Aux)
    (guard : Borrow.Guard) (wrapper : Wrapper Payload)
    (present : current before.1 guard = some wrapper) :
    readInfo storage before.1 (infoReference storage before guard).1 = some wrapper.account.info :=
      by
  obtain ⟨slot, cell, live, found, value⟩ := current_iff.mp present
  cases storage <;> simp [readInfo, present, infoReference, infoLocation, live]

/-- Logical placement is fresh and returns the exact decoded payload and
retained metadata. It never changes an earlier wrapper or source loan. -/
theorem place_current (policy : Borrow.Policy) (wrapper : Wrapper Payload)
    (before : World Payload Aux) :
    (place policy wrapper before).2.1.lookupCell (place policy wrapper before).1 =
      some ⟨some wrapper, policy⟩ ∧
    (place policy wrapper before).1.cell = before.1.cells.length ∧
    (place policy wrapper before).2.1.slots = before.1.slots :=
  ⟨Borrow.State.insert_lookup _ _ _, rfl, rfl⟩

/-- A moved wrapper cannot be read again at its former object identity. -/
theorem retire_current (before : World Payload Aux) (handle : Borrow.Handle)
    (cell : Borrow.Cell (Option (Wrapper Payload)))
    (present : before.1.lookupCell handle = some cell) :
    (retire before handle).1.lookupCell handle = some { cell with value := none } :=
  Borrow.replaceCell_lookup present none

/-- Every nonterminal set_inner exit retains the new owner in the same
receiver. This applies to arbitrary destructor effects in the shared auxiliary
state and to the unwind of the old destructor as well as normal return. -/
theorem setInner_field (types : SetTypes)
    {before : World types.Payload types.Aux} {guard : Borrow.Guard}
    {replacement : types.Payload}
    (ready : Writable before.1 guard)
    {final : Outcome (World types.Payload types.Aux) Unit types.Unwind types.Terminal}
    (called : setInnerRun types before (guard, replacement) final) :
    match final with
    | .returned _ after | .unwound _ after =>
      readPayload after.1 ⟨guard, true⟩ = some replacement
    | .terminated _ => True := by
  obtain ⟨wrapper, present⟩ := ready.1
  simp only [setInnerRun, present] at called
  obtain ⟨dropped, ⟨inner, _, lifted⟩, finished⟩ := called
  cases inner with
  | returned value state =>
    cases value
    cases lifted
    cases finished
    exact read_after_write present ready.2 replacement
  | unwound reason state =>
    cases lifted
    cases finished
    exact read_after_write present ready.2 replacement
  | terminated reason =>
    cases lifted
    cases finished
    trivial

end Solanalib.Specs.Core.AnchorViews
