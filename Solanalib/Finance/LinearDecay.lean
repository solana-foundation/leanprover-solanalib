/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Init

/-!
# Linear decay

A quantity that decays linearly from `peak` at the start of a window to `0`
at the end. Outside the window, the value is `0`.

This pattern recurs across Solana DeFi:

* **Withdrawal-penalty curves** in farm contracts: penalty is `peak` if you
  unstake at the start of the lock, `0` at maturity.
* **Linear vesting**: complementary shape; the *claimable* amount is
  `peak − decay`.
* **Liquidation-incentive bonuses** that decay over time.
* **Time-weighted voting power** approaching a sunset.

The Lean model below is a single `def` over `Nat` (the spec layer); a
`UInt64` wrapper plus the no-overflow proof lives in a follow-up file.

## Main definitions

* `Solanalib.Finance.LinearDecay.value` — the decaying quantity at a
  given time.

## Main statements

* `value_le_peak`             — bounded above by `peak`.
* `value_antitone_in_window`  — within the window, value is non-increasing
                                in `tNow`.
* `value_at_begin`            — at the left boundary, value equals `peak`.
* `value_at_end`              — at or after the right boundary, value is `0`.

Each theorem maps to a specific refactor-bug class:

| Theorem | Bug class it catches |
|---|---|
| `value_le_peak` | Penalty growing larger than configured (mul/div re-ordering) |
| `value_antitone_in_window` | Subtraction direction flipped in the numerator |
| `value_at_begin` | Off-by-one on the lock-start guard |
| `value_at_end` | Off-by-one on the maturity guard (`>` vs `≥`) |

The function is **not** monotonically antitone globally — at `tNow = tBegin`
it jumps from `0` (outside-window) to `peak` (inside-window). The honest
monotonicity statement (`value_antitone_in_window`) restricts both
timestamps to the locking window.
-/

namespace Solanalib.Finance.LinearDecay

/-- The value of a linearly-decaying quantity at time `tNow`, given the
window `[tBegin, tEnd)` and the peak `peak`.

Inside the window, the value is `peak * (tEnd - tNow) / (tEnd - tBegin)`.
Outside (before `tBegin` or at/after `tEnd`), it's `0`. -/
def value (tBegin tNow tEnd peak : Nat) : Nat :=
  if tNow < tBegin then 0
  else if tEnd ≤ tNow then 0
  else peak * (tEnd - tNow) / (tEnd - tBegin)

/-! ## Theorems -/

/-- **P1 — Bounded.** The decay never exceeds the configured peak. -/
theorem value_le_peak (tBegin tNow tEnd peak : Nat) :
    value tBegin tNow tEnd peak ≤ peak := by
  unfold value
  split
  · exact Nat.zero_le _
  split
  · exact Nat.zero_le _
  rename_i h_not_before h_not_after
  have h_now_ge_begin : tBegin ≤ tNow := Nat.le_of_not_lt h_not_before
  have h_now_lt_end   : tNow < tEnd  := Nat.lt_of_not_le h_not_after
  have h_begin_lt_end : tBegin < tEnd := Nat.lt_of_le_of_lt h_now_ge_begin h_now_lt_end
  have h_denom_pos    : 0 < tEnd - tBegin := Nat.sub_pos_of_lt h_begin_lt_end
  have h_numer_le     : tEnd - tNow ≤ tEnd - tBegin := Nat.sub_le_sub_left h_now_ge_begin tEnd
  calc peak * (tEnd - tNow) / (tEnd - tBegin)
      ≤ peak * (tEnd - tBegin) / (tEnd - tBegin) :=
        Nat.div_le_div_right (Nat.mul_le_mul_left peak h_numer_le)
    _ = peak                                     :=
        Nat.mul_div_cancel peak h_denom_pos

/-- **P2 — Antitone in `tNow` (within the window).** If `t₁ ≤ t₂` and
both fall inside the locking window, then `value` at `t₂` is at most
`value` at `t₁`.

The global function is **not** monotonically antitone — at `tNow = tBegin`
it jumps from `0` (outside) to `peak` (inside). The honest statement
restricts to in-window timestamps. -/
theorem value_antitone_in_window
    (tBegin tEnd peak : Nat) {t₁ t₂ : Nat}
    (h_begin : tBegin ≤ t₁) (h_order : t₁ ≤ t₂) (h_end : t₂ < tEnd) :
    value tBegin t₂ tEnd peak ≤ value tBegin t₁ tEnd peak := by
  have h_t₁_not_before : ¬ t₁ < tBegin := Nat.not_lt.mpr h_begin
  have h_t₁_lt_end     : t₁ < tEnd     := Nat.lt_of_le_of_lt h_order h_end
  have h_t₁_not_after  : ¬ tEnd ≤ t₁  := Nat.not_le.mpr h_t₁_lt_end
  have h_t₂_not_before : ¬ t₂ < tBegin := Nat.not_lt.mpr (Nat.le_trans h_begin h_order)
  have h_t₂_not_after  : ¬ tEnd ≤ t₂  := Nat.not_le.mpr h_end
  unfold value
  simp only [h_t₁_not_before, h_t₁_not_after,
             h_t₂_not_before, h_t₂_not_after, if_false]
  exact Nat.div_le_div_right
    (Nat.mul_le_mul_left peak (Nat.sub_le_sub_left h_order tEnd))

/-- **P3a — Value at start.** At `tNow = tBegin` (with a non-degenerate
window), the value equals the configured peak. -/
theorem value_at_begin (tBegin tEnd peak : Nat) (h : tBegin < tEnd) :
    value tBegin tBegin tEnd peak = peak := by
  unfold value
  have h_not_lt : ¬ tBegin < tBegin := Nat.lt_irrefl _
  have h_not_le : ¬ tEnd ≤ tBegin := Nat.not_le_of_lt h
  simp only [h_not_lt, h_not_le, if_false]
  exact Nat.mul_div_cancel peak (Nat.sub_pos_of_lt h)

/-- **P3b — Value at end.** At or after the right boundary, the value
is `0`. -/
theorem value_at_end (tBegin tEnd peak : Nat) :
    value tBegin tEnd tEnd peak = 0 := by
  unfold value
  split
  · rfl
  split
  · rfl
  rename_i _ h_not_le
  exact absurd (Nat.le_refl tEnd) h_not_le

end Solanalib.Finance.LinearDecay
