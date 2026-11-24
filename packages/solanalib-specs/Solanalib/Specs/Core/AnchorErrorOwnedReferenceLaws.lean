/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwnedReference
public import Solanalib.Specs.Core.AnchorErrorOwnedLaws

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOwned.Reference

private theorem slot_bound {Value : Type} {slots : List (Option Value)}
    {index : Nat} {value : Value} (present : slots[index]?.join = some value) :
    index < slots.length := by
  by_cases bound : index < slots.length
  · exact bound
  · have outside : slots[index]? = none := List.getElem?_eq_none (by omega)
    rw [outside] at present
    cases present

private theorem append_current {Value : Type} (slots : List (Option Value)) (value : Value) :
    (slots ++ [some value])[slots.length]?.join = some value := by
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

private theorem append_other {Value : Type} (slots : List (Option Value))
    (value : Value) (index : Nat) (different : index ≠ slots.length) :
    (slots ++ [some value])[index]?.join = slots[index]?.join := by
  by_cases inside : index < slots.length
  · rw [List.getElem?_append_left inside]
  · have left : (slots ++ [some value])[index]? = none :=
      List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega)
    have right : slots[index]? = none := List.getElem?_eq_none (by omega)
    rw [left, right]

private theorem string_returned (message : Bool) {before after : State}
    {text : String} {resource : StringId}
    (run : Callback.ofFunction (allocateString message) before text (.returned resource after)) :
    resource = (stringResult message before text).1 ∧
      after = (stringResult message before text).2 := by
  change allocateString message before text = .returned resource after at run
  unfold allocateString at run
  split at run
  · cases run
  · cases run
    exact ⟨rfl, rfl⟩

private theorem box_returned {before after : State}
    {payload : Payload StringId} {resource : BoxId}
    (run : Callback.ofFunction allocateBox before payload (.returned resource after)) :
    resource = (boxResult before payload).1 ∧ after = (boxResult before payload).2 := by
  change allocateBox before payload = .returned resource after at run
  unfold allocateBox at run
  split at run
  · cases run
  · cases run
    exact ⟨rfl, rfl⟩

private theorem string_allocation_laws (message : Bool) :
    AllocationLaws currentString (Callback.ofFunction (allocateString message)) where
  current := by
    intro before text resource after run
    obtain ⟨rfl, rfl⟩ := string_returned message run
    exact append_current before.strings text
  fresh := by
    intro before text resource after run
    obtain ⟨rfl, rfl⟩ := string_returned message run
    simp [currentString, stringResult]
  other := by
    intro before text resource after run other different
    obtain ⟨rfl, rfl⟩ := string_returned message run
    exact append_other before.strings text other.index
      (fun equal => different (congrArg StringId.mk equal))

private theorem box_allocation_laws :
    AllocationLaws currentBox (Callback.ofFunction allocateBox) where
  current := by
    intro before payload resource after run
    obtain ⟨rfl, rfl⟩ := box_returned run
    exact append_current before.boxes payload
  fresh := by
    intro before payload resource after run
    obtain ⟨rfl, rfl⟩ := box_returned run
    simp [currentBox, boxResult]
  other := by
    intro before payload resource after run other different
    obtain ⟨rfl, rfl⟩ := box_returned run
    exact append_other before.boxes payload other.index
      (fun equal => different (congrArg BoxId.mk equal))

private theorem string_retirement_laws : RetirementLaws currentString retireString where
  present := by
    intro before resource outcome run
    obtain ⟨text, observed, _⟩ := run
    exact ⟨text, observed⟩
  current := by
    intro before resource after run
    obtain ⟨text, observed, equal⟩ := run
    cases equal
    change (before.strings.set resource.index none)[resource.index]?.join = none
    rw [List.getElem?_set_self (slot_bound observed)]
    rfl
  other := by
    intro before resource after run other different
    obtain ⟨_, _, equal⟩ := run
    cases equal
    change (before.strings.set resource.index none)[other.index]?.join = _
    rw [List.getElem?_set_ne (show resource.index ≠ other.index from
      fun equal => different (congrArg StringId.mk equal.symm))]
    rfl

private theorem box_retirement_laws : RetirementLaws currentBox retireBox where
  present := by
    intro before resource outcome run
    obtain ⟨payload, observed, _⟩ := run
    exact ⟨payload, observed⟩
  current := by
    intro before resource after run
    obtain ⟨payload, observed, equal⟩ := run
    cases equal
    change (before.boxes.set resource.index none)[resource.index]?.join = none
    rw [List.getElem?_set_self (slot_bound observed)]
    rfl
  other := by
    intro before resource after run other different
    obtain ⟨_, _, equal⟩ := run
    cases equal
    change (before.boxes.set resource.index none)[other.index]?.join = _
    rw [List.getElem?_set_ne (show resource.index ≠ other.index from
      fun equal => different (congrArg BoxId.mk equal.symm))]
    rfl

private theorem box_store_laws : StoreLaws currentBox writeBox where
  available := by
    intro before resource old value present
    simp only [writeBox, present]
    exact ⟨_, rfl⟩
  present := by
    intro before resource value after stored
    unfold writeBox at stored
    split at stored
    · cases stored
    · exact ⟨_, ‹currentBox before resource = some _›⟩
  current := by
    intro before resource value after stored
    unfold writeBox at stored
    split at stored
    · cases stored
    · cases stored
      change (before.boxes.set resource.index (some value))[resource.index]?.join = some value
      rw [List.getElem?_set_self (slot_bound ‹currentBox before resource = some _›)]
      rfl
  other := by
    intro before resource value after stored other different
    unfold writeBox at stored
    split at stored
    · cases stored
    · cases stored
      change (before.boxes.set resource.index (some value))[other.index]?.join = _
      rw [List.getElem?_set_ne (show resource.index ≠ other.index from
        fun equal => different (congrArg BoxId.mk equal.symm))]
      rfl

/-- The finite heap satisfies every primitive freshness, actual-content,
retirement and frame law. This is a concrete pure model implementation proof. -/
theorem ops_laws : ops.Laws where
  copy := string_allocation_laws false
  format := string_allocation_laws true
  box := box_allocation_laws
  stringDrop := string_retirement_laws
  boxFree := box_retirement_laws
  store := box_store_laws
  copy_boxes := by
    intro before text resource after run box
    obtain ⟨_, rfl⟩ := string_returned false run
    rfl
  format_boxes := by
    intro before text resource after run box
    obtain ⟨_, rfl⟩ := string_returned true run
    rfl
  box_strings := by
    intro before payload resource after run string
    obtain ⟨_, rfl⟩ := box_returned run
    rfl
  drop_boxes := by
    intro before resource after run box
    obtain ⟨_, _, equal⟩ := run
    cases equal
    rfl
  store_strings := by
    intro before resource payload after stored string
    change writeBox before resource payload = some after at stored
    unfold writeBox at stored
    split at stored
    · cases stored
    · cases stored
      rfl
  free_strings := by
    intro before resource after run string
    obtain ⟨_, _, equal⟩ := run
    cases equal
    rfl

end Solanalib.Specs.Core.AnchorErrorOwned.Reference
