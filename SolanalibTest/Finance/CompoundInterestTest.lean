/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Finance.CompoundInterest

/-!
# Regression tests for `Solanalib.Finance.CompoundInterest`

Pins three layered properties:

1. **The math is right** on concrete values (a 2× multiplier doubles
   the principal once per period).
2. **Inherited theorems flow through the composition** — once a
   `CompoundInterest` instance becomes a `MonotoneSequence`, the
   generic `MonotoneSequence.apply_zero_le` / `apply_le_of_le`
   theorems apply without re-proof.
3. **The unit-multiplier identity** holds: with a 1.0 multiplier,
   the balance is constant. If a future refactor changes the
   compound formula in a way that breaks this, CI catches it.
-/

namespace SolanalibTest.Finance.CompoundInterest

open Solanalib Solanalib.Finance

/-! ## Concrete: a 2× multiplier doubles the balance each period -/

/-- A 2.0 multiplier as a Q68.60 Fraction. -/
def double : Fraction := Fraction.fromNat 2

/-- The multiplier is at least 1.0. -/
theorem double_ge_one : Fraction.one ≤ double := by
  show Fraction.one.bits ≤ double.bits
  rw [Fraction.one_bits]
  show Fraction.scale ≤ 2 * Fraction.scale
  exact Nat.le_mul_of_pos_left _ (by decide)

example : CompoundInterest.balance 100 double 0 = 100 := rfl
example : CompoundInterest.balance 100 double 1 = 200 := by decide
example : CompoundInterest.balance 100 double 3 = 800 := by decide

/-! ## Unit multiplier: balance is constant -/

example (n : Nat) :
    CompoundInterest.balance 100 Fraction.one n = 100 :=
  CompoundInterest.balance_at_one_multiplier 100 n

/-! ## Composition: balance is monotone via the MonotoneSequence bridge -/

/-- The bundled `MonotoneSequence` view of a 2× compounding from 100. -/
def example_seq : MonotoneSequence :=
  CompoundInterest.toMonotoneSequence 100 double double_ge_one

/-- **Generic `apply_zero_le` applies** — value at any step is at
least the initial value. The proof is `MonotoneSequence`'s
inherited theorem, *not* anything CompoundInterest-specific. -/
example (n : Nat) : example_seq.apply 0 ≤ example_seq.apply n :=
  example_seq.apply_zero_le n

/-- **Generic monotonicity applies** — value-at-later ≥ value-at-earlier. -/
example {n m : Nat} (h : n ≤ m) :
    example_seq.apply n ≤ example_seq.apply m :=
  example_seq.apply_le_of_le h

/-- Sanity: `apply 0 = principal`, since the bundled `apply` is the
underlying `balance` function. -/
example : example_seq.apply 0 = 100 := rfl

/-- And concretely, value at step 3 is the expected `100 * 2^3 = 800`. -/
example : example_seq.apply 3 = 800 := by decide

/-! ## Direct theorem: balance never drops below principal -/

example (n : Nat) : 100 ≤ CompoundInterest.balance 100 double n :=
  CompoundInterest.balance_ge_principal 100 double double_ge_one n

end SolanalibTest.Finance.CompoundInterest
