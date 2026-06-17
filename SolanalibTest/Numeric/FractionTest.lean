/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Numeric.Fraction

/-!
# Regression tests for `Solanalib.Numeric.Fraction`

Pins the spec-layer behaviour of the Q68.60 fixed-point shape:
constants, basic arithmetic, integer round-trip via `fromNat` /
`toFloor`, the monoid theorems, ordering, and `sub`/`add` cancellation.
-/

namespace SolanalibTest.Numeric.Fraction

open Solanalib

/-! ## Constants and conversions -/

/-- `zero` and `one` are distinct. -/
example : Fraction.zero ≠ Fraction.one := by decide

/-- `fromNat n |>.toFloor = n` — integers round-trip cleanly. -/
example (n : Nat) : (Fraction.fromNat n).toFloor = n :=
  Fraction.toFloor_fromNat n

/-- `fromNat 0 = zero`. -/
example : Fraction.fromNat 0 = Fraction.zero := by
  ext
  show 0 * Fraction.scale = 0
  exact Nat.zero_mul _

/-- `fromNat 1 = one`. -/
example : Fraction.fromNat 1 = Fraction.one := by
  ext
  show 1 * Fraction.scale = Fraction.scale
  exact Nat.one_mul _

/-! ## Monoid theorems -/

example : Fraction.zero.add Fraction.one = Fraction.one :=
  Fraction.zero_add Fraction.one

example : Fraction.one.add Fraction.zero = Fraction.one :=
  Fraction.add_zero Fraction.one

example (a b : Fraction) : a.add b = b.add a :=
  Fraction.add_comm a b

example : Fraction.one.mul Fraction.one = Fraction.one :=
  Fraction.mul_one Fraction.one

example (a : Fraction) : Fraction.one.mul a = a :=
  Fraction.one_mul a

/-! ## Ordering -/

example (a : Fraction) : Fraction.zero ≤ a :=
  Fraction.zero_le a

example (a : Fraction) : a ≤ a := Fraction.le_refl a

example {a b c : Fraction} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Fraction.le_trans h₁ h₂

example : Fraction.zero ≤ Fraction.one := by decide

/-! ## Subtraction (with underflow precondition) -/

/-- `(a - b) + b = a` whenever the subtraction is well-defined. -/
example (a b : Fraction) (h : b.bits ≤ a.bits) : (a.sub b h).add b = a :=
  Fraction.sub_add a b h

/-- Concrete: `one − one = zero`. -/
example :
    Fraction.one.sub Fraction.one (Nat.le_refl _) = Fraction.zero := by
  ext
  show Fraction.scale - Fraction.scale = 0
  exact Nat.sub_self _

/-! ## Division -/

/-- `div_one` returns the dividend unchanged. -/
example (a : Fraction) : a.div Fraction.one Fraction.one_bits_ne_zero = a :=
  Fraction.div_one a

/-! ## Lamports ↔ Fraction bridge -/

/-- Lamports → Fraction → Nat round-trip preserves the integer value. -/
example (l : Lamports) : (Fraction.ofLamports l).toFloor = l.toNat :=
  Fraction.toFloor_ofLamports l

end SolanalibTest.Numeric.Fraction
