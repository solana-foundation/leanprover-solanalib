/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Solanalib.Init

/-!
# CompoundInterestApprox: the cubic binomial approximation of compounding

Lending programs accrue interest per slot or second, so the exact growth
factor `(1 + t)^n` would need a power with an exponent in the millions.
Instead they evaluate the first terms of the binomial expansion

`(1 + t)^n ≈ 1 + n t + n(n−1)/2 · t² + n(n−1)(n−2)/6 · t³`,

for example in klend's `approximate_compounded_interest` and in the
Aave-style `calculate_compounded_interest`. This module defines that
cubic approximation over `ℚ` and relates it to exact compounding: it is
exact for at most three periods and never overestimates for a
non-negative rate, so a protocol using it never charges more than exact
per-period compounding.

## Main definitions

* `Solanalib.Finance.cubicCompoundApprox` — the cubic binomial approximation.

## Main statements

* `cubicCompoundApprox_eq_sum` — it is the binomial sum truncated after the cubic term.
* `cubicCompoundApprox_eq_pow` — it is exact for `n ≤ 3` periods.
* `cubicCompoundApprox_le_pow` — it never exceeds `(1 + t)^n` when `0 ≤ t`.
* `one_add_mul_le_cubicCompoundApprox` — it is at least simple interest `1 + n t` when `0 ≤ t`.
-/

namespace Solanalib.Finance

open Finset

/-- The cubic binomial approximation of the growth factor `(1 + t)^n` after
`n` periods at per-period rate `t`. -/
def cubicCompoundApprox (n : Nat) (t : ℚ) : ℚ :=
  1 + n * t + n * (n - 1) / 2 * t ^ 2 + n * (n - 1) * (n - 2) / 6 * t ^ 3

private theorem cast_choose_three (n : Nat) :
    (n.choose 3 : ℚ) = n * (n - 1) * (n - 2) / 6 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> simp [Nat.choose]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [Nat.cast_choose ℚ h, Nat.add_sub_cancel]
    simp only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
    have : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    field_simp
    ring

/-- The approximation is the binomial expansion of `(1 + t)^n` truncated
after the cubic term. -/
theorem cubicCompoundApprox_eq_sum (n : Nat) (t : ℚ) :
    cubicCompoundApprox n t = ∑ k ∈ range 4, t ^ k * (n.choose k : ℚ) := by
  simp only [sum_range_succ, sum_range_zero, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_choose_two, cast_choose_three, cubicCompoundApprox]
  ring

private theorem pow_eq_sum (n : Nat) (t : ℚ) :
    (1 + t) ^ n = ∑ k ∈ range (n + 1), t ^ k * (n.choose k : ℚ) := by
  rw [add_comm, add_pow]
  simp

/-- For at most three periods the approximation is exact. -/
theorem cubicCompoundApprox_eq_pow {n : Nat} (hn : n ≤ 3) (t : ℚ) :
    cubicCompoundApprox n t = (1 + t) ^ n := by
  interval_cases n <;> simp [cubicCompoundApprox] <;> ring

/-- For a non-negative rate the approximation never exceeds exact compounding. -/
theorem cubicCompoundApprox_le_pow (n : Nat) {t : ℚ} (ht : 0 ≤ t) :
    cubicCompoundApprox n t ≤ (1 + t) ^ n := by
  rcases Nat.lt_or_ge n 3 with h | h
  · exact (cubicCompoundApprox_eq_pow h.le t).le
  · rw [cubicCompoundApprox_eq_sum, pow_eq_sum]
    apply sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
    intro k _ _
    positivity

/-- For a non-negative rate the approximation is at least simple interest. -/
theorem one_add_mul_le_cubicCompoundApprox (n : Nat) {t : ℚ} (ht : 0 ≤ t) :
    1 + n * t ≤ cubicCompoundApprox n t := by
  rw [cubicCompoundApprox_eq_sum]
  simp only [sum_range_succ, sum_range_zero, Nat.choose_zero_right, Nat.choose_one_right]
  have h2 : 0 ≤ t ^ 2 * (n.choose 2 : ℚ) := by positivity
  have h3 : 0 ≤ t ^ 3 * (n.choose 3 : ℚ) := by positivity
  push_cast
  linarith

end Solanalib.Finance
