/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Numeric.Rounding

/-!
# BasisPoints: rates expressed in hundredths of a percent

Fees, protocol shares, haircuts and decay factors on Solana are usually
stored as integers counting basis points (`1 bps = 1/10_000`). A program
computes the bps share of an amount as `amount * rate / 10_000`, rounded
down (when paying out) or up (when charging), and often keeps the
remainder for another party. This module fixes those shapes and the facts
that make fee splits safe: the parts never exceed the whole and add up
exactly.

## Main definitions

* `Solanalib.Numeric.bpsDenominator` — `10_000`.
* `Solanalib.Numeric.bpsShare` — `⌊amount · rate / 10_000⌋`.
* `Solanalib.Numeric.bpsShareCeil` — `⌈amount · rate / 10_000⌉`.
* `Solanalib.Numeric.bpsRemainder` — what is left after taking `bpsShare`.

## Main statements

* `bpsShare_le`, `bpsShareCeil_le` — a share at a rate of at most 100% never exceeds the amount.
* `bpsShare_add_bpsRemainder` — share and remainder recombine exactly.
* `bpsShare_le_bpsShareCeil`, `bpsShareCeil_le_bpsShare_add_one` — the roundings differ by ≤ 1.
* `bpsShare_mono_amount`, `bpsShare_mono_rate` — monotonicity in both arguments.
-/

namespace Solanalib.Numeric

/-- One whole, in basis points. -/
def bpsDenominator : Nat := 10000

/-- The `rate`-basis-point share of `amount`, rounded down. -/
def bpsShare (amount rate : Nat) : Nat := amount * rate / bpsDenominator

/-- The `rate`-basis-point share of `amount`, rounded up. -/
def bpsShareCeil (amount rate : Nat) : Nat := ceilDiv (amount * rate) bpsDenominator

/-- What remains of `amount` after the rounded-down `rate`-bps share is taken. -/
def bpsRemainder (amount rate : Nat) : Nat := amount - bpsShare amount rate

@[simp]
theorem bpsShare_zero_rate (amount : Nat) : bpsShare amount 0 = 0 := by
  simp [bpsShare]

@[simp]
theorem bpsShare_zero_amount (rate : Nat) : bpsShare 0 rate = 0 := by
  simp [bpsShare]

/-- The full rate takes the whole amount. -/
@[simp]
theorem bpsShare_denominator (amount : Nat) : bpsShare amount bpsDenominator = amount := by
  simp [bpsShare, bpsDenominator]

/-- At a rate of at most 100%, the share never exceeds the amount. -/
theorem bpsShare_le {amount rate : Nat} (h : rate ≤ bpsDenominator) :
    bpsShare amount rate ≤ amount := by
  unfold bpsShare
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm bpsDenominator]
  exact Nat.mul_le_mul_left amount h

/-- At a rate of at most 100%, the rounded-up share never exceeds the amount. -/
theorem bpsShareCeil_le {amount rate : Nat} (h : rate ≤ bpsDenominator) :
    bpsShareCeil amount rate ≤ amount := by
  unfold bpsShareCeil
  rw [ceilDiv_le_iff (by decide), Nat.mul_comm bpsDenominator]
  exact Nat.mul_le_mul_left amount h

/-- The share and the remainder add up to the amount, so a fee split
neither creates nor destroys tokens. -/
theorem bpsShare_add_bpsRemainder {amount rate : Nat} (h : rate ≤ bpsDenominator) :
    bpsShare amount rate + bpsRemainder amount rate = amount := by
  have := bpsShare_le (amount := amount) h
  unfold bpsRemainder
  omega

theorem bpsShare_le_bpsShareCeil (amount rate : Nat) :
    bpsShare amount rate ≤ bpsShareCeil amount rate :=
  div_le_ceilDiv _ _

theorem bpsShareCeil_le_bpsShare_add_one (amount rate : Nat) :
    bpsShareCeil amount rate ≤ bpsShare amount rate + 1 :=
  ceilDiv_le_div_add_one _ _

theorem bpsShare_mono_amount {amount amount' : Nat} (rate : Nat) (h : amount ≤ amount') :
    bpsShare amount rate ≤ bpsShare amount' rate :=
  Nat.div_le_div_right (Nat.mul_le_mul_right rate h)

theorem bpsShare_mono_rate (amount : Nat) {rate rate' : Nat} (h : rate ≤ rate') :
    bpsShare amount rate ≤ bpsShare amount rate' :=
  Nat.div_le_div_right (Nat.mul_le_mul_left amount h)

end Solanalib.Numeric
