/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedSeeds
public import Solanalib.Specs.Core.OwnedVector
public import Solanalib.Specs.Core.OwnedFocusFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedSeeds.Witness

universe u v w x y z

/-- The finite controls can store a view of the data component and lift its
reader to the whole state. This avoids a recursive state containing readers
of itself; it does not replace live readers by byte snapshots. -/
def mapElements {State : Type u} {Element : Type v} {Mapped : Type w}
    {Resource : Type x} {Unwind : Type y} {Terminal : Type z}
    (ops : Owned.VectorOps State Element Resource Unwind Terminal)
    (view : Element → Mapped) : Owned.VectorOps State Mapped Resource Unwind Terminal where
  current := fun state resource => (ops.current state resource).map (List.map view)
  empty := ops.empty
  withCapacity := ops.withCapacity
  fromList := fun state values outcome =>
    ∃ originals, originals.map view = values ∧ ops.fromList state originals outcome
  push := fun state (resource, value) outcome =>
    ∃ original, view original = value ∧ ops.push state (resource, original) outcome
  extend := fun state (resource, values) outcome =>
    ∃ originals, originals.map view = values ∧ ops.extend state (resource, originals) outcome
  drop := ops.drop

/-- Changing the mathematical presentation of elements preserves all local
vector laws. A callback with an unrepresentable element has no finite outcome
in this sample provider; no totality claim is made. -/
theorem mapElements_laws {State : Type u} {Element : Type v} {Mapped : Type w}
    {Resource : Type x} {Unwind : Type y} {Terminal : Type z}
    {ops : Owned.VectorOps State Element Resource Unwind Terminal} (laws : ops.Laws)
    (view : Element → Mapped) : (mapElements ops view).Laws := by
  constructor
  · intro before
    change (ops.current (ops.empty before).2 (ops.empty before).1).map (List.map view) = some []
    rw [laws.empty_current]
    rfl
  · intro before
    change (ops.current before (ops.empty before).1).map (List.map view) = none
    rw [laws.empty_fresh]
    rfl
  · intro before capacity resource after run
    change (ops.current after resource).map (List.map view) = some []
    rw [laws.capacity_current before capacity resource after run]
    rfl
  · intro before capacity resource after run
    change (ops.current before resource).map (List.map view) = none
    rw [laws.capacity_fresh before capacity resource after run]
    rfl
  · rintro before values resource after ⟨originals, rfl, run⟩
    change (ops.current after resource).map (List.map view) = some (originals.map view)
    rw [laws.list_current before originals resource after run]
    rfl
  · rintro before values resource after ⟨originals, rfl, run⟩
    change (ops.current before resource).map (List.map view) = none
    rw [laws.list_fresh before originals resource after run]
    rfl
  · rintro before resource value values after current ⟨original, rfl, run⟩
    change (ops.current before resource).map (List.map view) = some values at current
    cases observed : ops.current before resource with
    | none => simp [observed] at current
    | some originals =>
      have equal : originals.map view = values := by simpa [observed] using current
      subst values
      change (ops.current after resource).map (List.map view) = _
      rw [laws.push_current before resource original originals after observed run]
      simp
  · rintro before resource value reason after ⟨values, current⟩ ⟨original, rfl, run⟩
    change (ops.current before resource).map (List.map view) = some values at current
    cases observed : ops.current before resource with
    | none => simp [observed] at current
    | some originals =>
      obtain ⟨updated, updatedCurrent⟩ := laws.push_unwind_live before resource original reason
        after ⟨originals, observed⟩ run
      exact ⟨updated.map view, by
        change (ops.current after resource).map _ = _; rw [updatedCurrent]; rfl⟩
  · rintro before resource extra values after current ⟨originals, rfl, run⟩
    change (ops.current before resource).map (List.map view) = some values at current
    cases observed : ops.current before resource with
    | none => simp [observed] at current
    | some previous =>
      have equal : previous.map view = values := by simpa [observed] using current
      subst values
      change (ops.current after resource).map (List.map view) = _
      rw [laws.extend_current before resource originals previous after observed run]
      simp
  · rintro before resource extra reason after ⟨values, current⟩ ⟨originals, rfl, run⟩
    change (ops.current before resource).map (List.map view) = some values at current
    cases observed : ops.current before resource with
    | none => simp [observed] at current
    | some previous =>
      obtain ⟨updated, updatedCurrent⟩ := laws.extend_unwind_live before resource originals reason
        after ⟨previous, observed⟩ run
      exact ⟨updated.map view, by
        change (ops.current after resource).map _ = _; rw [updatedCurrent]; rfl⟩
  · rintro before resource after ⟨values, current⟩ run
    change (ops.current before resource).map (List.map view) = some values at current
    cases observed : ops.current before resource with
    | none => simp [observed] at current
    | some originals =>
      change (ops.current after resource).map (List.map view) = none
      rw [laws.drop_current before resource after ⟨originals, observed⟩ run]
      rfl
  · rintro before resource reason after ⟨values, current⟩ run
    change (ops.current before resource).map (List.map view) = some values at current
    cases observed : ops.current before resource with
    | none => simp [observed] at current
    | some originals =>
      change (ops.current after resource).map (List.map view) = none
      rw [laws.drop_unwind_consumed before resource reason after ⟨originals, observed⟩ run]
      rfl

/-- Events of one concrete normal ledger provider. A drop records the actual
current elements, allowing the seed provider to consume owned literals. -/
inductive Step (Element : Type v) where
  /-- Construction of an empty vector in the sample ledger. -/
  | empty
  /-- Construction of an empty vector with the requested capacity. -/
  | capacity (capacity : Nat)
  /-- Construction from the supplied initial elements. -/
  | fromList (values : List Element)
  /-- Transfer of one element into the selected vector resource. -/
  | push (resource : Nat) (value : Element)
  /-- Transfer of a sequence of elements into the selected vector resource. -/
  | extend (resource : Nat) (values : List Element)
  /-- Destruction of a vector, carrying its actual current elements to the hook. -/
  | drop (resource : Nat) (values : List Element)

/-- A focused normal ledger with explicit effects outside its own ledger.
The hook may record calls or consume nested owners; its stated premise below
is local to this vector component and is not a law of arbitrary providers. -/
def ledger {State : Type u} {Element : Type v} {Unwind : Type y} {Terminal : Type z}
    (focus : Owned.Focus State (Owned.VectorState Element))
    (hook : Step Element → State → State → State) :
    Owned.VectorOps State Element Nat Unwind Terminal where
  current := fun state resource => (focus.get state).current resource
  empty := fun before =>
    let allocated := (focus.get before).allocate []
    (allocated.1, hook .empty before (focus.set before allocated.2))
  withCapacity := returnsOf fun before capacity =>
    let allocated := (focus.get before).allocate []
    (allocated.1, hook (.capacity capacity) before (focus.set before allocated.2))
  fromList := returnsOf fun before values =>
    let allocated := (focus.get before).allocate values
    (allocated.1, hook (.fromList values) before (focus.set before allocated.2))
  push := fun before (resource, value) outcome =>
    ∃ values, (focus.get before).current resource = some values ∧
      outcome = .returned () (hook (.push resource value) before
        (focus.set before ((focus.get before).set resource (some (values ++ [value])))))
  extend := fun before (resource, extra) outcome =>
    ∃ values, (focus.get before).current resource = some values ∧
      outcome = .returned () (hook (.extend resource extra) before
        (focus.set before ((focus.get before).set resource (some (values ++ extra)))))
  drop := fun before resource outcome =>
    ∃ values, (focus.get before).current resource = some values ∧
      outcome = .returned () (hook (.drop resource values) before
        (focus.set before ((focus.get before).set resource none)))

/-- The eventful finite ledger meets the same complete primitive law set as
the shared normal reference. No success assumption for deployed allocation is
introduced by this mathematical sample. -/
theorem ledger_laws {State : Type u} {Element : Type v} {Unwind : Type y} {Terminal : Type z}
    (focus : Owned.Focus State (Owned.VectorState Element))
    (hook : Step Element → State → State → State)
    (preserve : ∀ step before after, focus.get (hook step before after) = focus.get after) :
    (ledger focus hook : Owned.VectorOps State Element Nat Unwind Terminal).Laws := by
  constructor
  · intro before
    change (focus.get (hook .empty before (focus.set before _))).current _ = _
    rw [preserve, focus.get_set]
    exact Owned.VectorState.allocate_current (focus.get before) []
  · exact fun before => Owned.VectorState.allocate_fresh (focus.get before) []
  · intro before capacity resource after run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    change (focus.get (hook _ before (focus.set before _))).current _ = _
    rw [preserve, focus.get_set]
    exact Owned.VectorState.allocate_current (focus.get before) []
  · intro before capacity resource after run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact Owned.VectorState.allocate_fresh (focus.get before) []
  · intro before values resource after run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    change (focus.get (hook _ before (focus.set before _))).current _ = _
    rw [preserve, focus.get_set]
    exact Owned.VectorState.allocate_current (focus.get before) values
  · intro before values resource after run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact Owned.VectorState.allocate_fresh (focus.get before) values
  · rintro before resource value values after current ⟨actual, observed, returned⟩
    have equal : actual = values := Option.some.inj (observed.symm.trans current)
    subst actual
    cases returned
    change (focus.get (hook _ before (focus.set before _))).current resource = _
    rw [preserve, focus.get_set]
    exact Owned.VectorState.current_set _ _ _ (Owned.VectorState.current_bound current)
  · rintro before resource value reason after live ⟨values, current, impossible⟩
    cases impossible
  · rintro before resource extra values after current ⟨actual, observed, returned⟩
    have equal : actual = values := Option.some.inj (observed.symm.trans current)
    subst actual
    cases returned
    change (focus.get (hook _ before (focus.set before _))).current resource = _
    rw [preserve, focus.get_set]
    exact Owned.VectorState.current_set _ _ _ (Owned.VectorState.current_bound current)
  · rintro before resource extra reason after live ⟨values, current, impossible⟩
    cases impossible
  · rintro before resource after live ⟨values, current, returned⟩
    cases returned
    change (focus.get (hook _ before (focus.set before _))).current resource = _
    rw [preserve, focus.get_set]
    exact Owned.VectorState.current_set _ _ _ (Owned.VectorState.current_bound current)
  · rintro before resource reason after live ⟨values, current, impossible⟩
    cases impossible

end Solanalib.Specs.Core.Token.AllocatedSeeds.Witness
