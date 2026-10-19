/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Numeric.BasisPoints
import Solanalib.Numeric.Checked
import Solanalib.Numeric.Fraction
import Solanalib.Numeric.Limbs
import Solanalib.Numeric.Rounding

/-!
# Regression tests for rounding, checked arithmetic, basis points and limbs

Pins concrete values of the Rust idioms modelled in `Solanalib.Numeric`.
-/

namespace SolanalibTest.Numeric.Rounding

open Solanalib Solanalib.Numeric

/-! ## Rounding -/

example : ceilDiv 7 2 = 4 := by decide
example : ceilDiv 8 2 = 4 := by decide
example : ceilDiv 0 5 = 0 := by decide
example : roundedDiv 7 2 false = 3 := by decide
example : roundedDiv 7 2 true = 4 := by decide
example : splitMulDiv 7 3 4 = 7 * 3 / 4 := splitMulDiv_eq 7 3 4
example : splitMulDivCeil 7 3 4 = 6 := by decide

/-! ## Checked arithmetic -/

example : checkedAdd 8 200 55 = some 255 := by decide
example : checkedAdd 8 200 56 = none := by decide
example : checkedSub 3 4 = none := by decide
example : checkedMul 64 (2 ^ 32) (2 ^ 32) = none := by decide
example : checkedDiv 7 0 = none := by decide
example : saturatingAdd 8 200 100 = 255 := by decide
example : wrappingAdd 8 200 100 = 44 := by decide
example : signedMax 8 = 127 := by decide
example : signedMin 8 = -128 := by decide
example : saturate 8 300 = 127 := by decide
example : checkedAddSigned 8 100 28 = none := by decide

/-! ## Basis points -/

example : bpsShare 1000 30 = 3 := by decide
example : bpsShareCeil 1001 30 = 4 := by decide
example : bpsRemainder 1000 30 = 997 := by decide

/-! ## Limbs -/

example : limbsValue [1, 2] = 1 + 2 * 2 ^ 64 := by decide
example : toLimbs 2 (2 ^ 64 + 5) = [5, 1] := by decide

/-! ## Rounded-up fixed point -/

example : (Fraction.mulCeil ⟨3⟩ ⟨1⟩).bits = 1 := by decide
example : (Fraction.mul ⟨3⟩ ⟨1⟩).bits = 0 := by decide

end SolanalibTest.Numeric.Rounding
