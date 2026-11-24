/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorViews.Values

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

def readableB {P : Type} (s : Store P) (g : Borrow.Guard) : Bool := (current s g).isSome

theorem readableB_iff {P : Type} (s : Store P) (g : Borrow.Guard) :
    readableB s g = true ↔ Readable s g := Option.isSome_iff_exists

def writableB {P : Type} (s : Store P) (g : Borrow.Guard) : Bool :=
  readableB s g && match s.resolve g with
    | some slot => decide (slot.mode = .exclusive)
    | none => false

theorem writableB_iff {P : Type} (s : Store P) (g : Borrow.Guard) :
    writableB s g = true ↔ Writable s g := by
  unfold writableB Writable
  rw [Bool.and_eq_true, readableB_iff]
  apply and_congr_right
  intro _
  cases h : s.resolve g <;> simp

def movableB {P : Type} (s : Store P) (h : Borrow.Handle) : Bool :=
  ((s.lookupCell h).bind (·.value)).isSome && decide (s.lease h = .free)

theorem movableB_iff {P : Type} (s : Store P) (h : Borrow.Handle) :
    movableB s h = true ↔ Movable s h := by
  unfold movableB Movable
  rw [Bool.and_eq_true, decide_eq_true_iff]
  apply and_congr_left
  intro _
  cases hc : s.lookupCell h with
  | none => simp
  | some cell => simp [Option.isSome_iff_exists]

/-- Each Boolean is used through an equivalence to the registered admission,
not as an independent approximation to it. -/
def decideBy {p : Prop} (b : Bool) (h : b = true ↔ p) : Bool :=
  @decide p (decidable_of_iff _ h)

instance {P : Type} (s : Store P) (g : Borrow.Guard) : Decidable (Readable s g) :=
  decidable_of_iff _ (readableB_iff s g)

instance {P : Type} (s : Store P) (g : Borrow.Guard) : Decidable (Writable s g) :=
  decidable_of_iff _ (writableB_iff s g)

instance {P : Type} (s : Store P) (h : Borrow.Handle) : Decidable (Movable s h) :=
  decidable_of_iff _ (movableB_iff s h)

end SolanalibTest.Conformance.Library.Families.AnchorViews
