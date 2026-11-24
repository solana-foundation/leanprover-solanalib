/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleFocus
public import Solanalib.Specs.Core.AnchorViewsAssignment

@[expose] public section

open Solanalib.Contracts.Model
set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AnchorLifecycleFocus

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorViews AnchorLifecycle

def guard : Borrow.Guard := ⟨0, 0⟩
def slot : Borrow.Slot Unit := ⟨⟨0⟩, .exclusive, 0, ()⟩
def policy : Borrow.Policy := ⟨100⟩
def selected : Wrapper Nat := ⟨⟨7, AccountInfo.sampleInfo⟩, 41, some .zero⟩
def sibling : Wrapper Nat := ⟨⟨19, AccountInfo.sampleInfo⟩, 42, none⟩
def store : Store Nat := ⟨[⟨some selected, policy⟩, ⟨some sibling, policy⟩], [some slot]⟩
def receiver : Receiver Nat guard := ⟨store, ⟨⟨selected, rfl⟩, slot, rfl, rfl⟩⟩

/-- The destructor mutates the other wrapper, which shares the same Rc cells
but has a different decoded field and AccountInfo record identity. -/
def afterDrop : Receiver Nat guard :=
  ⟨{ store with cells := store.cells.set 1 ⟨some (sibling.withPayload 69), policy⟩ },
    ⟨⟨selected, rfl⟩, slot, rfl, rfl⟩⟩

abbrev State := Receiver Nat guard × List Nat

def payload : Owned.Focus State Nat := Owned.Focus.fst.comp Receiver.payloadFocus

def dropOld : Callback.Run State Nat Unit String Unit := Callback.ofFunction fun before old =>
  .unwound "old payload drop" (afterDrop, before.2 ++ [old])

theorem replacement_on_unwind : AnchorViewsAssignment.run payload dropOld (receiver, []) 91
    (.unwound "old payload drop" (afterDrop.replace 91, [7])) :=
  (AnchorViewsAssignment.unwound payload dropOld rfl).1

/-- The same original reference sees the installed replacement, while the
other wrapper keeps the actual mutation of the destructor. -/
theorem current_fields_after_unwind :
    readPayload (afterDrop.replace 91).val ⟨guard, true⟩ = some 91 ∧
    (afterDrop.replace 91).val.lookupCell ⟨1⟩ = some ⟨some (sibling.withPayload 69), policy⟩ ∧
    (afterDrop.replace 91).wrapper.infoIdentity = 41 := by
  exact ⟨rfl, rfl, rfl⟩

/-- A shared parent lease cannot instantiate the mutable receiver focus. -/
theorem shared_parent_rejected :
    ¬ Writable ({ store with slots := [some { slot with mode := .shared }] } : Store Nat) guard :=
      by
  rintro ⟨_, next, resolved, exclusive⟩
  change some { slot with mode := .shared } = some next at resolved
  cases resolved
  cases exclusive

/-- Releasing the original source loan makes the same reference unusable. -/
theorem released_parent_rejected :
    readPayload (Borrow.release (afterDrop.replace 91).val guard).2 ⟨guard, true⟩ = none := rfl

end SolanalibTest.Specs.Core.AnchorLifecycleFocus
