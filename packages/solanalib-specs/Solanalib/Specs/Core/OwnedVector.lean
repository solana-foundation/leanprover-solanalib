/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Owned

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Owned

universe u x y

/-- A finite mathematical reference ledger. Slots are never reused after drop;
their indices are logical identities, not allocator addresses or Rust fields. -/
abbrev VectorState (Element : Type u) := List (Option (List Element))

/-- Read only a live reference-ledger slot. -/
def VectorState.current {Element : Type u} (state : VectorState Element)
    (resource : Nat) : Option (List Element) := state[resource]?.join

/-- Add a fresh logical slot containing the supplied exact sequence. This is
a model witness operation, not an implementation of a Rust allocation. -/
def VectorState.allocate {Element : Type u} (state : VectorState Element)
    (values : List Element) : Nat × VectorState Element :=
  (state.length, state ++ [some values])

/-- Modify the current sequence under a live token. Dead or missing tokens
have no permitted finite operation in this reference interpretation. -/
def VectorState.modify {Element : Type u} {Unwind : Type x} {Terminal : Type y}
    (state : VectorState Element) (resource : Nat) (update : List Element → List Element)
    (outcome : Outcome (VectorState Element) Unit Unwind Terminal) : Prop :=
  ∃ values, state.current resource = some values ∧
    outcome = .returned () (state.set resource (some (update values)))

/-- Retire a live logical token. The tombstone keeps all surviving identities
stable and prevents reusing a stale handle for a subsequently created vector. -/
def VectorState.retire {Element : Type u} {Unwind : Type x} {Terminal : Type y}
    (state : VectorState Element) (resource : Nat)
    (outcome : Outcome (VectorState Element) Unit Unwind Terminal) : Prop :=
  ∃ values, state.current resource = some values ∧
    outcome = .returned () (state.set resource none)

/-- A live logical vector has an actual slot in the finite reference ledger. -/
theorem VectorState.current_bound {Element : Type u} {state : VectorState Element}
    {resource : Nat} {values : List Element}
    (current : state.current resource = some values) : resource < state.length := by
  by_cases inside : resource < state.length
  · exact inside
  · have bound : state.length ≤ resource := Nat.le_of_not_lt inside
    simp [VectorState.current, List.getElem?_eq_none bound] at current

/-- The fresh appended slot contains the complete supplied sequence. -/
theorem VectorState.allocate_current {Element : Type u} (state : VectorState Element)
    (values : List Element) :
    (state.allocate values).2.current (state.allocate values).1 = some values := by
  simp [allocate, current]

/-- A fresh appended slot was absent before construction. -/
theorem VectorState.allocate_fresh {Element : Type u} (state : VectorState Element)
    (values : List Element) : state.current (state.allocate values).1 = none := by
  simp [allocate, current]

/-- Updating an existing slot yields its exact current value. -/
theorem VectorState.current_set {Element : Type u} (state : VectorState Element)
    (resource : Nat) (value : Option (List Element)) (bounded : resource < state.length) :
    VectorState.current (state.set resource value) resource = value := by
  simp [current, List.getElem?_set_self bounded]

/-- Replacing one slot leaves the observation of every different token unchanged. -/
theorem VectorState.current_set_other {Element : Type u} (state : VectorState Element)
    (resource other : Nat) (value : Option (List Element)) (different : other ≠ resource) :
    VectorState.current (state.set resource value) other = state.current other := by
  simp [current, List.getElem?_set_ne different.symm]

/-- Successful reference updates append to the actual observed input contents. -/
theorem VectorState.modify_current {Element : Type u} {Unwind : Type x} {Terminal : Type y}
    {state after : VectorState Element} {resource : Nat} {values : List Element}
    {update : List Element → List Element}
    (current : state.current resource = some values)
    (run : state.modify resource update (.returned () after :
      Outcome (VectorState Element) Unit Unwind Terminal)) :
    after.current resource = some (update values) := by
  obtain ⟨actual, observed, returned⟩ := run
  have same : actual = values := Option.some.inj (observed.symm.trans current)
  subst actual
  cases returned
  exact state.current_set resource (some (update values)) (current_bound current)

/-- A reference drop really retires the current token. -/
theorem VectorState.retire_current {Element : Type u} {Unwind : Type x} {Terminal : Type y}
    {state after : VectorState Element} {resource : Nat}
    (run : state.retire resource (.returned () after :
      Outcome (VectorState Element) Unit Unwind Terminal)) : after.current resource = none := by
  obtain ⟨values, current, returned⟩ := run
  cases returned
  exact state.current_set resource none (current_bound current)

/-- A normal-only concrete interpretation inhabiting the vector dependency
interface. This sample does not assert allocator success for other providers
or any Rust execution. Its exit types remain polymorphic for composition with
separate failure-injection and source-dependency models. -/
def vectorReference {Element : Type u} {Unwind : Type x} {Terminal : Type y} :
    VectorOps (VectorState Element) Element Nat Unwind Terminal where
  current := VectorState.current
  empty := fun state => state.allocate []
  withCapacity := returnsOf (fun state _ => state.allocate [])
  fromList := returnsOf VectorState.allocate
  push := fun state (resource, value) => state.modify resource (· ++ [value])
  extend := fun state (resource, extra) => state.modify resource (· ++ extra)
  drop := VectorState.retire

/-- The finite reference ledger satisfies every stated primitive dependency
law, including freshness, exact ordered contents, stale retirement and all
unwind obligations. The latter are vacuous only for this normal-only sample;
the generic laws and cleanup engine also support actual unwinding providers. -/
theorem vectorReference_laws {Element : Type u} {Unwind : Type x} {Terminal : Type y} :
    (vectorReference : VectorOps (VectorState Element) Element Nat Unwind Terminal).Laws := by
  constructor
  · exact fun before => VectorState.allocate_current before []
  · exact fun before => VectorState.allocate_fresh before []
  · intro before capacity resource after run
    change before.allocate [] = (resource, after) at run
    have correct := before.allocate_current []
    rw [run] at correct
    exact correct
  · intro before capacity resource after run
    change before.allocate [] = (resource, after) at run
    have correct := before.allocate_fresh []
    rw [run] at correct
    exact correct
  · intro before values resource after run
    change before.allocate values = (resource, after) at run
    have correct := before.allocate_current values
    rw [run] at correct
    exact correct
  · intro before values resource after run
    change before.allocate values = (resource, after) at run
    have correct := before.allocate_fresh values
    rw [run] at correct
    exact correct
  · intro before resource value values after current run
    exact VectorState.modify_current (state := before) (values := values)
      (update := fun previous => previous ++ [value]) current run
  · intro before resource value reason after live run
    obtain ⟨values, current, impossible⟩ := run
    cases impossible
  · intro before resource extra values after current run
    exact VectorState.modify_current (state := before) (values := values)
      (update := fun previous => previous ++ extra) current run
  · intro before resource extra reason after live run
    obtain ⟨values, current, impossible⟩ := run
    cases impossible
  · intro before resource after live run
    exact VectorState.retire_current run
  · intro before resource reason after live run
    obtain ⟨values, current, impossible⟩ := run
    cases impossible

end Solanalib.Specs.Core.Owned
