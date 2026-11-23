/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.ModEq
import Solanalib.Init

/-!
# Rounding: floor and ceiling division as Solana programs compute them

On-chain programs only have integer division, which truncates. Every
quantity that must be rounded *against* the user (fees charged, amounts
owed, tokens taken in) is therefore computed with the idiom
`(n + d - 1) / d`, and every quantity rounded *in favour of* the program
(amounts paid out) with plain `n / d`. Getting the direction wrong is a
classic source of value leaks, so this module fixes the two shapes once
and connects the Rust idiom to Mathlib's `⌈/⌉`.

A second recurring idiom is the *split* product `n / d * s + n % d * s / d`,
which computes `⌊n * s / d⌋` without forming the possibly overflowing
product `n * s` (for example, a `u128` value rescaled by `2^60` or `2^64`).
`splitMulDiv_eq` shows it is exact.

## Main definitions

* `Solanalib.Numeric.ceilDiv` — `(n + d - 1) / d`, the Rust ceiling-division idiom.
* `Solanalib.Numeric.roundedDiv` — floor or ceiling division selected by a flag.
* `Solanalib.Numeric.splitMulDiv` — overflow-avoiding `⌊n * s / d⌋`.
* `Solanalib.Numeric.splitMulDivCeil` — overflow-avoiding `⌈n * s / d⌉`.

## Main statements

* `ceilDiv_eq` — `ceilDiv` agrees with Mathlib's `⌈/⌉` on `ℕ`.
* `ceilDiv_le_iff`, `le_mul_ceilDiv` — the Galois-connection characterisation.
* `div_le_ceilDiv`, `ceilDiv_le_div_add_one` — ceiling and floor differ by at most one.
* `ceilDiv_add_le` — ceiling division is subadditive (splitting never undercharges).
* `splitMulDiv_eq`, `splitMulDivCeil_eq` — the split idioms are exact.
-/

namespace Solanalib.Numeric

/-- Ceiling division `⌈n / d⌉` written as Rust programs compute it:
`(n + d - 1) / d`. Division by zero returns `0`, like `Nat` division. -/
def ceilDiv (n d : Nat) : Nat := (n + d - 1) / d

/-- Division rounding up when `roundUp` holds and down otherwise, the
shape of the `round_up : bool` parameter of many on-chain math helpers. -/
def roundedDiv (n d : Nat) (roundUp : Bool) : Nat :=
  if roundUp then ceilDiv n d else n / d

/-- `⌊n * s / d⌋` computed from the quotient and remainder of `n` by `d`,
so the full product `n * s` is never formed. -/
def splitMulDiv (n s d : Nat) : Nat := n / d * s + n % d * s / d

/-- `⌈n * s / d⌉` computed from the quotient and remainder of `n` by `d`. -/
def splitMulDivCeil (n s d : Nat) : Nat := n / d * s + ceilDiv (n % d * s) d

/-! ## Ceiling division -/

/-- The Rust idiom is Mathlib's ceiling division on `ℕ`. -/
theorem ceilDiv_eq (n d : Nat) : ceilDiv n d = n ⌈/⌉ d := rfl

@[simp]
theorem ceilDiv_zero_right (n : Nat) : ceilDiv n 0 = 0 := by
  simp [ceilDiv_eq]

@[simp]
theorem zero_ceilDiv (d : Nat) : ceilDiv 0 d = 0 := by
  simp [ceilDiv_eq]

@[simp]
theorem ceilDiv_one (n : Nat) : ceilDiv n 1 = n := by
  simp [ceilDiv]

/-- `ceilDiv n d` is the least `c` with `n ≤ d * c`. -/
theorem ceilDiv_le_iff {n d c : Nat} (hd : 0 < d) : ceilDiv n d ≤ c ↔ n ≤ d * c :=
  ceilDiv_le_iff_le_mul hd

theorem le_mul_ceilDiv (n : Nat) {d : Nat} (hd : 0 < d) : n ≤ d * ceilDiv n d :=
  (ceilDiv_le_iff hd).1 le_rfl

/-- Rounding up never yields less than rounding down. -/
theorem div_le_ceilDiv (n d : Nat) : n / d ≤ ceilDiv n d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · exact Nat.div_le_div_right (by omega)

/-- Rounding up exceeds rounding down by at most one. -/
theorem ceilDiv_le_div_add_one (n d : Nat) : ceilDiv n d ≤ n / d + 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [ceilDiv_le_iff hd]
    have := Nat.lt_mul_div_succ n hd
    omega

/-- When `d` divides `n`, both roundings agree. -/
theorem ceilDiv_eq_div_of_dvd {n d : Nat} (h : d ∣ n) : ceilDiv n d = n / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · obtain ⟨k, rfl⟩ := h
    apply le_antisymm
    · rw [ceilDiv_le_iff hd, Nat.mul_div_cancel_left k hd]
    · exact div_le_ceilDiv _ _

/-- When `d` does not divide `n`, rounding up adds exactly one. -/
theorem ceilDiv_eq_div_add_one {n d : Nat} (hd : 0 < d) (h : n % d ≠ 0) :
    ceilDiv n d = n / d + 1 := by
  apply le_antisymm (ceilDiv_le_div_add_one n d)
  have hn := Nat.div_add_mod n d
  have hc := le_mul_ceilDiv n hd
  by_contra hlt
  have : ceilDiv n d ≤ n / d := by omega
  have := Nat.mul_le_mul_left d this
  omega

theorem ceilDiv_mono_left {n m : Nat} (d : Nat) (h : n ≤ m) : ceilDiv n d ≤ ceilDiv m d :=
  Nat.div_le_div_right (by omega)

/-- Charging two parts separately, each rounded up, never charges less
than rounding up their sum. -/
theorem ceilDiv_add_le (a b d : Nat) : ceilDiv (a + b) d ≤ ceilDiv a d + ceilDiv b d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [ceilDiv_le_iff hd, Nat.mul_add]
    exact Nat.add_le_add (le_mul_ceilDiv a hd) (le_mul_ceilDiv b hd)

/-! ## Selected rounding -/

@[simp]
theorem roundedDiv_false (n d : Nat) : roundedDiv n d false = n / d := rfl

@[simp]
theorem roundedDiv_true (n d : Nat) : roundedDiv n d true = ceilDiv n d := rfl

theorem roundedDiv_false_le_true (n d : Nat) : roundedDiv n d false ≤ roundedDiv n d true :=
  div_le_ceilDiv n d

theorem roundedDiv_mono_left {n m : Nat} (d : Nat) (roundUp : Bool) (h : n ≤ m) :
    roundedDiv n d roundUp ≤ roundedDiv m d roundUp := by
  cases roundUp
  · exact Nat.div_le_div_right h
  · exact ceilDiv_mono_left d h

/-! ## Split products -/

/-- The split idiom computes `⌊n * s / d⌋` exactly. -/
theorem splitMulDiv_eq (n s d : Nat) : splitMulDiv n s d = n * s / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [splitMulDiv]
  · conv_rhs => rw [← Nat.div_add_mod n d]
    rw [splitMulDiv, Nat.add_mul, Nat.mul_assoc, Nat.mul_add_div hd]

/-- The split idiom computes `⌈n * s / d⌉` exactly. -/
theorem splitMulDivCeil_eq (n s d : Nat) : splitMulDivCeil n s d = ceilDiv (n * s) d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [splitMulDivCeil]
  · conv_rhs => rw [← Nat.div_add_mod n d]
    have : d * (n / d * s) + n % d * s + d - 1 = d * (n / d * s) + (n % d * s + d - 1) := by
      omega
    rw [splitMulDivCeil, ceilDiv, ceilDiv, Nat.add_mul, Nat.mul_assoc, this, Nat.mul_add_div hd]

end Solanalib.Numeric
