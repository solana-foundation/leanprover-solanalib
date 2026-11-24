/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorViewsFacts
public import Solanalib.Specs.Core.OwnedFocusFacts

@[expose] public section

open Solanalib.Contracts.Model
set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorViews

/-- A source receiver whose one existing parent loan remains writable. The
payload is stored only in the common wrapper Store; this subtype adds no value
snapshot or independent ownership ledger. -/
abbrev Receiver (Payload : Type) (guard : Borrow.Guard) :=
  { store : Store Payload // Writable store guard }

variable {Payload : Type} {guard : Borrow.Guard}

def Receiver.wrapper (receiver : Receiver Payload guard) : Wrapper Payload :=
  (current receiver.val guard).get (by
    obtain ⟨wrapper, present⟩ := receiver.property.1
    simp [present])

theorem Receiver.current_wrapper (receiver : Receiver Payload guard) :
    current receiver.val guard = some receiver.wrapper :=
  (Option.some_get _).symm

theorem Receiver.write_slots (receiver : Receiver Payload guard) (replacement : Payload) :
    (writePayload receiver.val ⟨guard, true⟩ replacement).2.slots = receiver.val.slots := by
  obtain ⟨slot, live, mode⟩ := receiver.property.2
  simp only [writePayload, ↓reduceIte, receiver.current_wrapper,
    Borrow.write, live, mode, ↓reduceIte, Borrow.replaceCell_slots]

def Receiver.replace (receiver : Receiver Payload guard) (replacement : Payload) :
    Receiver Payload guard :=
  ⟨(writePayload receiver.val ⟨guard, true⟩ replacement).2, by
    constructor
    · exact ⟨receiver.wrapper.withPayload replacement,
        (writePayload_current receiver.current_wrapper receiver.property.2 replacement).2⟩
    · obtain ⟨slot, live, mode⟩ := receiver.property.2
      refine ⟨slot, ?_, mode⟩
      simpa only [Borrow.State.resolve, Borrow.State.lookupSlot, receiver.write_slots] using live⟩

theorem Receiver.wrapper_replace (receiver : Receiver Payload guard) (replacement : Payload) :
    (receiver.replace replacement).wrapper = receiver.wrapper.withPayload replacement := by
  apply Option.some.inj
  rw [← Receiver.current_wrapper]
  exact (writePayload_current receiver.current_wrapper receiver.property.2 replacement).2

/-- Replacing the payload preserves the exact referred-to AccountInfo object,
its Rc aliases, and the separately saved InterfaceAccount owner. -/
theorem Receiver.replacement_metadata (receiver : Receiver Payload guard) (replacement : Payload) :
    ((receiver.replace replacement).wrapper.account.info,
      (receiver.replace replacement).wrapper.infoIdentity,
      (receiver.replace replacement).wrapper.savedOwner) =
    (receiver.wrapper.account.info, receiver.wrapper.infoIdentity, receiver.wrapper.savedOwner) :=
      by
  rw [receiver.wrapper_replace]
  rfl

theorem Receiver.replace_store (receiver : Receiver Payload guard) (replacement : Payload)
    {slot : Borrow.Slot Unit} {cell : Borrow.Cell (Option (Wrapper Payload))}
    (live : receiver.val.resolve guard = some slot)
    (found : receiver.val.lookupCell slot.cell = some cell) :
    (receiver.replace replacement).val =
      { receiver.val with
        cells := receiver.val.cells.set slot.cell.cell
          { cell with value := some (receiver.wrapper.withPayload replacement) } } := by
  obtain ⟨selected, same, mode⟩ := receiver.property.2
  have equal : selected = slot := Option.some.inj (same.symm.trans live)
  subst selected
  simp only [replace, writePayload, ↓reduceIte, receiver.current_wrapper,
    Borrow.write, live, mode, ↓reduceIte, Borrow.replaceCell, found]

theorem Receiver.replace_resolve (receiver : Receiver Payload guard) (replacement : Payload) :
    (receiver.replace replacement).val.resolve guard = receiver.val.resolve guard := by
  simp only [replace, Borrow.State.resolve, Borrow.State.lookupSlot, receiver.write_slots]

theorem Receiver.replace_get (receiver : Receiver Payload guard) :
    receiver.replace receiver.wrapper.account.value = receiver := by
  apply Subtype.ext
  obtain ⟨slot, cell, live, found, value⟩ := current_iff.mp receiver.current_wrapper
  rw [receiver.replace_store _ live found]
  have unchanged : { cell with value := some (receiver.wrapper.withPayload
    receiver.wrapper.account.value) } = cell := by
    simp only [Wrapper.withPayload]
    rw [← value]
  rw [unchanged]
  have keep : receiver.val.cells.set slot.cell.cell cell = receiver.val.cells := by
    obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
    simpa only [same] using List.set_getElem_self bound
  rw [keep]

theorem Receiver.replace_replace (receiver : Receiver Payload guard) (first second : Payload) :
    (receiver.replace first).replace second = receiver.replace second := by
  apply Subtype.ext
  obtain ⟨slot, cell, live, found, value⟩ := current_iff.mp receiver.current_wrapper
  have afterLive : (receiver.replace first).val.resolve guard = some slot := by
    rw [receiver.replace_resolve, live]
  have afterFound : (receiver.replace first).val.lookupCell slot.cell =
      some { cell with value := some (receiver.wrapper.withPayload first) } := by
    rw [receiver.replace_store _ live found]
    exact List.getElem?_set_self (Borrow.State.lookupCell_bound found)
  rw [(receiver.replace first).replace_store second afterLive afterFound,
    receiver.replace_store second live found, receiver.replace_store first live found]
  simp only [wrapper_replace, Wrapper.withPayload, List.set_set]

/-- Reload updates the current payload under the original source
loan of the caller. The three lens laws are proved from the actual common Store write. -/
def Receiver.payloadFocus : Owned.Focus (Receiver Payload guard) Payload where
  get := fun receiver => receiver.wrapper.account.value
  set := Receiver.replace
  get_set := fun receiver replacement => by
    rw [Receiver.wrapper_replace]
    rfl
  set_get := Receiver.replace_get
  set_set := Receiver.replace_replace

end Solanalib.Specs.Core.AnchorLifecycle
