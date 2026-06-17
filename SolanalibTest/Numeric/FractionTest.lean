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
`toFloor`, and the five named monoid theorems.
-/

namespace SolanalibTest.Numeric.Fraction

open Solanalib

/-- `zero` and `one` are distinct (the additive and multiplicative units
are not the same). -/
example : Fraction.zero ≠ Fraction.one := by decide

/-- `fromNat 5 |>.toFloor = 5` — integers round-trip cleanly. -/
example : (Fraction.fromNat 5).toFloor = 5 := by
  unfold Fraction.fromNat Fraction.toFloor
  exact Nat.mul_div_cancel _ Fraction.scale_pos

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

/-- The five monoid theorems instantiate concretely. -/
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

end SolanalibTest.Numeric.Fraction
