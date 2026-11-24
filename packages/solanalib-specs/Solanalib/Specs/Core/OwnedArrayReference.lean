/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OwnedArray
public import Solanalib.Specs.Core.OwnedArrayLaws
public import Solanalib.Specs.Core.OwnedVector

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Owned.Array

universe u x y

/-- A dropless mathematical construction reference. It requests the next
expression immediately and allocates a fresh ledger slot only at completion.
This is one named provider, not a fixed schedule imposed on the generic engine
or a claim about Rust allocation. Elements have trivial reference destruction. -/
def droplessReference {Element : Type u} {Unwind : Type x} {Terminal : Type y} :
    Provider (VectorState Element) Element Nat Unwind Terminal where
  work := returnsOf fun before (count, values) =>
    (if values.length < count then .evaluate else .finish, before)
  finish := vectorReference.fromList
  cleanupOrder := fun _ values => List.finRange values.length
  drop := returnsOf fun before _ => ((), before)
  retire := returnsOf fun before _ => ((), before)
  double := fun _ _ _ _ => False

/-- The reference requests only a remaining expression or an exactly complete
result, and its cleanup order visits each evaluated occurrence once. -/
theorem droplessReference_conforms {Element : Type u} {Unwind : Type x} {Terminal : Type y} :
    (droplessReference : Provider (VectorState Element) Element Nat Unwind Terminal).Conforms := by
  constructor
  · intro before count values after _ called
    change (if values.length < count then Command.evaluate else .finish, before) =
      (.evaluate, after) at called
    by_cases remaining : values.length < count
    · exact remaining
    · simp only [remaining, ↓reduceIte, Prod.mk.injEq, reduceCtorEq, false_and] at called
  · intro before count values after bounded called
    change (if values.length < count then Command.evaluate else .finish, before) =
      (.finish, after) at called
    by_cases remaining : values.length < count
    · simp only [remaining, ↓reduceIte, Prod.mk.injEq, reduceCtorEq, false_and] at called
    · exact Nat.le_antisymm bounded (Nat.le_of_not_lt remaining)
  · intro state values
    exact List.Perm.refl _

/-- Completion stores the exact supplied prefix, including equal occurrences,
under the actual returned reference-ledger handle. -/
theorem droplessReference_finish_current {Element : Type u} {Unwind : Type x} {Terminal : Type y}
    (before after : VectorState Element) (values : List Element) (resource : Nat)
    (finished : (droplessReference : Provider (VectorState Element) Element Nat Unwind
      Terminal).finish
      before values (.returned resource after)) :
    after.current resource = some values :=
  (vectorReference_laws (Element := Element) (Unwind := Unwind) (Terminal := Terminal)).list_current
    before values resource after finished

/-- Completion creates a new logical identity rather than reusing a live or
retired reference-ledger slot. -/
theorem droplessReference_finish_fresh {Element : Type u} {Unwind : Type x} {Terminal : Type y}
    (before after : VectorState Element) (values : List Element) (resource : Nat)
    (finished : (droplessReference : Provider (VectorState Element) Element Nat Unwind
      Terminal).finish
      before values (.returned resource after)) :
    before.current resource = none :=
  (vectorReference_laws (Element := Element) (Unwind := Unwind) (Terminal := Terminal)).list_fresh
    before values resource after finished

/-- The successful completion returns the exact index and
state of the appended slot, so this reference never reuses a retired earlier slot. -/
theorem droplessReference_finish_exact {Element : Type u} {Unwind : Type x} {Terminal : Type y}
    (before after : VectorState Element) (values : List Element) (resource : Nat)
    (finished : (droplessReference : Provider (VectorState Element) Element Nat Unwind
      Terminal).finish
      before values (.returned resource after)) :
    resource = before.length ∧ after = before ++ [some values] := by
  change (before.length, before ++ [some values]) = (resource, after) at finished
  exact ⟨(Prod.mk.inj finished).1.symm, (Prod.mk.inj finished).2.symm⟩

/-- This named reference satisfies the separate local current-vector law;
the generic scheduling predicate alone does not imply that law. -/
theorem droplessReference_currentLaw {Element : Type u} {Unwind : Type x} {Terminal : Type y} :
    (droplessReference : Provider (VectorState Element) Element Nat Unwind Terminal).CurrentLaw
      vectorReference := by
  constructor
  intro before values resource after finished
  exact droplessReference_finish_current before after values resource finished

/-- A concrete expression interpretation returns the selected indexed value
and preserves the current reference ledger. -/
def pureEvaluator {Element : Type u} {Unwind : Type x} {Terminal : Type y}
    (valueAt : Nat → Element) :
    Callback.Run (VectorState Element) Nat Element Unwind Terminal :=
  returnsOf fun before index => (valueAt index, before)

/-- The exact ordered values produced by the first `count` expressions. -/
def referenceValues {Element : Type u} (count : Nat) (valueAt : Nat → Element) : List Element :=
  (List.range' 0 count).map valueAt

/-- From any already evaluated prefix, the reference executes every remaining
indexed expression once and stores the complete ordered result in a fresh slot.
This is a constructive finite trace, without assumed callback success. -/
theorem droplessReference_trace {Element : Type u} {Unwind : Type x} {Terminal : Type y}
    (remaining : Nat) (valueAt : Nat → Element) (values : List Element)
    (before : VectorState Element) :
    Trace (droplessReference : Provider (VectorState Element) Element Nat Unwind Terminal)
      (values.length + remaining) (pureEvaluator valueAt) values before
      (.returned before.length
        (before ++ [some (values ++ (List.range' values.length remaining).map valueAt)])) := by
  induction remaining generalizing values with
  | zero =>
    simp only [Nat.add_zero, List.range'_zero, List.map_nil, List.append_nil]
    apply Trace.finishReturn values before before (before ++ [some values]) before.length rfl
    · change (if values.length < values.length then Command.evaluate else .finish, before) =
        (.finish, before)
      simp only [Nat.lt_irrefl, ↓reduceIte]
    · rfl
  | succ remaining induction =>
    have bound : values.length < values.length + (remaining + 1) := by omega
    apply Trace.next values before before before (valueAt values.length) _ bound
    · change (if values.length < values.length + (remaining + 1) then Command.evaluate
        else .finish, before) = (.evaluate, before)
      simp only [bound, ↓reduceIte]
    · rfl
    · simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
        List.range'_succ, List.map_cons, List.append_assoc, List.cons_append, List.nil_append,
        Nat.add_assoc, Nat.add_comm 1 remaining] using induction (values ++ [valueAt values.length])

/-- The detailed reference execution starts with no evaluated expressions and
returns a fresh handle containing all indexed values in source order. -/
theorem droplessReference_runDetailed {Element : Type u} {Unwind : Type x} {Terminal : Type y}
    (count : Nat) (valueAt : Nat → Element) (before : VectorState Element) :
    (droplessReference : Provider (VectorState Element) Element Nat Unwind Terminal).runDetailed
      count (pureEvaluator valueAt) before
      (.returned before.length (before ++ [some (referenceValues count valueAt)])) := by
  simpa only [Provider.runDetailed, List.length_nil, Nat.zero_add, List.nil_append, referenceValues]
    using droplessReference_trace (Unwind := Unwind) (Terminal := Terminal) count valueAt [] before

/-- Erasing progress metadata preserves that same successful resource and state. -/
theorem droplessReference_run {Element : Type u} {Unwind : Type x} {Terminal : Type y}
    (count : Nat) (valueAt : Nat → Element) (before : VectorState Element) :
    (droplessReference : Provider (VectorState Element) Element Nat Unwind Terminal).run
      count (pureEvaluator valueAt) before
      (.returned before.length (before ++ [some (referenceValues count valueAt)])) :=
  ⟨_, droplessReference_runDetailed count valueAt before, rfl⟩

/-- A closed natural-number provider used for the law and execution witnesses.
Its impossibility of unwind is specific to this named mathematical sample. -/
def natReference : Provider (VectorState Nat) Nat Nat Empty Empty := droplessReference

/-- The sample already contains one live vector, so construction must preserve
an existing handle while returning a genuinely new ledger slot. -/
def natReferenceInitial : VectorState Nat := [some [42]]

/-- The indexed sample contains repeated equal values at distinct positions. -/
def natReferenceValueAt (index : Nat) : Nat := if index < 2 then 7 else 9

/-- The exact three-element expected result, retaining both equal sevens. -/
def natReferenceValues : List Nat := [7, 7, 9]

/-- Actual sample expression callbacks, rather than assumed successful exits. -/
def natReferenceEvaluate : Callback.Run (VectorState Nat) Nat Nat Empty Empty :=
  pureEvaluator natReferenceValueAt

/-- The precise final ledger includes the original vector and the new array. -/
def natReferenceAfter : VectorState Nat := [some [42], some natReferenceValues]

/-- Closed scheduling and occurrence-permutation witness for the sample. -/
theorem natReference_conforms : natReference.Conforms := droplessReference_conforms

/-- Closed local current-vector witness for the sample. -/
theorem natReference_currentLaw : natReference.CurrentLaw vectorReference :=
  droplessReference_currentLaw

/-- The concrete expression interpretation produces exactly the expected
ordered sequence, including the repeated equal values. -/
theorem natReference_values_exact : referenceValues 3 natReferenceValueAt = natReferenceValues :=
  rfl

/-- Closed nonempty construction witness includes all three expression calls
and actual vector completion into fresh handle 1. -/
theorem natReference_detailed_executes :
    natReference.runDetailed 3 natReferenceEvaluate natReferenceInitial
      (.returned 1 natReferenceAfter) :=
  droplessReference_runDetailed 3 natReferenceValueAt natReferenceInitial

/-- Erasing unwind metadata preserves the exact successful execution of the sample. -/
theorem natReference_executes :
    natReference.run 3 natReferenceEvaluate natReferenceInitial (.returned 1 natReferenceAfter) :=
  ⟨.returned 1 natReferenceAfter, natReference_detailed_executes, rfl⟩

/-- The returned logical handle currently owns all three ordered sample values. -/
theorem natReference_current : natReferenceAfter.current 1 = some natReferenceValues := rfl

/-- The returned handle did not designate an earlier vector. -/
theorem natReference_fresh : natReferenceInitial.current 1 = none := rfl

/-- Construction preserves the previously live handle and its actual contents. -/
theorem natReference_previous :
    natReferenceAfter.current 0 = natReferenceInitial.current 0 ∧
      natReferenceAfter.current 0 = some [42] := ⟨rfl, rfl⟩

end Solanalib.Specs.Core.Owned.Array
