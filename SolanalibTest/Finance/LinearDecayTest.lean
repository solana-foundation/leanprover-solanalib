/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Finance.LinearDecay

/-!
# Regression tests for `Solanalib.Finance.LinearDecay`

Concrete-number sanity checks plus a shape-correspondence example: the
Lean `value` formula matches a real-world withdrawal-penalty formula
when none of its early-return guards fire.

If any of the four theorems in `LinearDecay.lean` regress (e.g. the
mul/div order flips, the subtraction direction flips), one of the
concrete examples below will fail to type-check.
-/

namespace SolanalibTest.Finance.LinearDecay

open Solanalib.Finance.LinearDecay

/-- Concrete: a 10000-bps penalty over a 1000-second window, evaluated
at the start, returns the full peak. -/
example : value 0 0 1000 10000 = 10000 := by decide

/-- Concrete: at maturity, the penalty is 0. -/
example : value 0 1000 1000 10000 = 0 := by decide

/-- Concrete: halfway through, the penalty is half of peak. -/
example : value 0 500 1000 10000 = 5000 := by decide

/-- Concrete: 75% through, the penalty is a quarter of peak. -/
example : value 0 750 1000 10000 = 2500 := by decide

/-- Concrete: before the window opens, the penalty is 0. -/
example : value 100 50 1000 10000 = 0 := by decide

/-- Concrete: well after maturity, the penalty is 0. -/
example : value 0 5000 1000 10000 = 0 := by decide

/-- The four properties apply to concrete instances. -/
example : value 0 500 1000 10000 ≤ 10000 := value_le_peak 0 500 1000 10000

example (h_begin : 100 ≤ 200) (h_order : 200 ≤ 500) (h_end : 500 < 1000) :
    value 100 500 1000 10000 ≤ value 100 200 1000 10000 :=
  value_antitone_in_window 100 1000 10000 h_begin h_order h_end

example : value 100 100 1000 10000 = 10000 :=
  value_at_begin 100 1000 10000 (by decide)

example : value 0 1000 1000 10000 = 0 :=
  value_at_end 0 1000 10000

/-- Withdrawal-penalty correspondence: when none of the early-return
guards fire, the formula `penalty_bps * time_remaining / total_duration`
is exactly `LinearDecay.value`. -/
example (tBegin tNow tEnd peak : Nat)
    (h_now_in_window_begin : tBegin ≤ tNow)
    (h_now_in_window_end   : tNow < tEnd) :
    value tBegin tNow tEnd peak = peak * (tEnd - tNow) / (tEnd - tBegin) := by
  unfold value
  have h_not_before : ¬ tNow < tBegin := Nat.not_lt.mpr h_now_in_window_begin
  have h_not_after  : ¬ tEnd ≤ tNow  := Nat.not_le.mpr h_now_in_window_end
  simp [h_not_before, h_not_after]

end SolanalibTest.Finance.LinearDecay
