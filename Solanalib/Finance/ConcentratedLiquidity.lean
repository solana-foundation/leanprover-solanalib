/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Numeric.Rounding

/-!
# ConcentratedLiquidity: token amounts of a Q64.64 sqrt-price AMM

Concentrated-liquidity market makers (the Uniswap v3 design, used on
Solana by Orca Whirlpools, Raydium CLMM and others) store the square root
of the price as a Q64.64 fixed-point number `sqrtPrice = √P · 2^64`, and a
liquidity amount `L`. Moving the price between two sqrt prices `p` and `q`
exchanges

* token A: `ΔA = L · |q − p| · 2^64 / (p · q)` and
* token B: `ΔB = L · |q − p| / 2^64`,

rounded *up* for the amount the pool receives and *down* for the amount it
pays out. This module defines those amounts at the spec layer, together
with the per-liquidity fee-growth increment, and proves the properties a
swap or position implementation relies on.

## Main definitions

* `sqrtPriceDistance` — `|q − p|` on `Nat`.
* `amountADelta`, `amountBDelta` — token amounts between two sqrt prices.
* `inputAmount`, `outputAmount` — the amounts a swap step takes in and pays out.
* `feeGrowthIncrement` — Q64.64 fee growth per unit of liquidity.

## Main statements

* `amountADelta_comm`, `amountBDelta_comm` — amounts do not depend on direction.
* `amountADelta_self`, `amountBDelta_self` — no price movement exchanges nothing.
* `amountADelta_down_le_up`, `amountBDelta_down_le_up` — paying out never exceeds charging.
* `amountADelta_mono_liquidity`, `amountBDelta_mono_liquidity` — monotone in liquidity.
* `amountBDelta_down_add_le`, `amountBDelta_up_le_add` — splitting a price move into two
  steps can neither increase the payout nor decrease the charge in token B.
* `inputAmount_eq`, `outputAmount_eq` — the rounding direction of each swap side.
-/

namespace Solanalib.Finance.ConcentratedLiquidity

open Solanalib.Numeric

/-- The Q64.64 scale `2^64`. Irreducible so that proofs treat it as an
abstract positive constant; unfold with `q64_eq`. -/
@[irreducible] def q64 : Nat := 2 ^ 64

theorem q64_eq : q64 = 2 ^ 64 := by unfold q64; rfl

theorem q64_pos : 0 < q64 := by rw [q64_eq]; exact Nat.two_pow_pos 64

/-- The distance `|q − p|` between two sqrt prices. -/
def sqrtPriceDistance (p q : Nat) : Nat := max p q - min p q

/-- The token-A amount between sqrt prices `p` and `q` at liquidity `liquidity`:
`liquidity · |q − p| · 2^64 / (p · q)`, rounded up when `roundUp` holds. -/
def amountADelta (p q liquidity : Nat) (roundUp : Bool) : Nat :=
  roundedDiv (liquidity * sqrtPriceDistance p q * q64) (p * q) roundUp

/-- The token-B amount between sqrt prices `p` and `q` at liquidity `liquidity`:
`liquidity · |q − p| / 2^64`, rounded up when `roundUp` holds. -/
def amountBDelta (p q liquidity : Nat) (roundUp : Bool) : Nat :=
  roundedDiv (liquidity * sqrtPriceDistance p q) q64 roundUp

/-- The amount a swap step from `current` to `next` takes in, rounded up.
When `aToB` holds the pool receives token A, otherwise token B. -/
def inputAmount (aToB : Bool) (current next liquidity : Nat) : Nat :=
  if aToB then amountADelta current next liquidity true
  else amountBDelta current next liquidity true

/-- The amount a swap step from `current` to `next` pays out, rounded down.
When `aToB` holds the pool pays token B, otherwise token A. -/
def outputAmount (aToB : Bool) (current next liquidity : Nat) : Nat :=
  if aToB then amountBDelta current next liquidity false
  else amountADelta current next liquidity false

/-- The Q64.64 growth of fees per unit of liquidity when `fee` tokens are
distributed over `liquidity`; nothing accrues when there is no liquidity. -/
def feeGrowthIncrement (fee liquidity : Nat) : Nat :=
  if liquidity = 0 then 0 else fee * q64 / liquidity

/-! ## Distance -/

theorem sqrtPriceDistance_comm (p q : Nat) : sqrtPriceDistance p q = sqrtPriceDistance q p := by
  unfold sqrtPriceDistance
  omega

@[simp]
theorem sqrtPriceDistance_self (p : Nat) : sqrtPriceDistance p p = 0 := by
  simp [sqrtPriceDistance]

theorem sqrtPriceDistance_of_le {p q : Nat} (h : p ≤ q) : sqrtPriceDistance p q = q - p := by
  unfold sqrtPriceDistance
  omega

/-- Distances along a monotone path add up. -/
theorem sqrtPriceDistance_add {p q r : Nat} (hpq : p ≤ q) (hqr : q ≤ r) :
    sqrtPriceDistance p q + sqrtPriceDistance q r = sqrtPriceDistance p r := by
  unfold sqrtPriceDistance
  omega

/-! ## Token amounts -/

theorem amountADelta_comm (p q liquidity : Nat) (roundUp : Bool) :
    amountADelta p q liquidity roundUp = amountADelta q p liquidity roundUp := by
  rw [amountADelta, amountADelta, sqrtPriceDistance_comm, Nat.mul_comm p]

theorem amountBDelta_comm (p q liquidity : Nat) (roundUp : Bool) :
    amountBDelta p q liquidity roundUp = amountBDelta q p liquidity roundUp := by
  rw [amountBDelta, amountBDelta, sqrtPriceDistance_comm]

@[simp]
theorem amountADelta_self (p liquidity : Nat) (roundUp : Bool) :
    amountADelta p p liquidity roundUp = 0 := by
  cases roundUp <;> simp [amountADelta]

@[simp]
theorem amountBDelta_self (p liquidity : Nat) (roundUp : Bool) :
    amountBDelta p p liquidity roundUp = 0 := by
  cases roundUp <;> simp [amountBDelta]

@[simp]
theorem amountADelta_zero_liquidity (p q : Nat) (roundUp : Bool) :
    amountADelta p q 0 roundUp = 0 := by
  cases roundUp <;> simp [amountADelta]

@[simp]
theorem amountBDelta_zero_liquidity (p q : Nat) (roundUp : Bool) :
    amountBDelta p q 0 roundUp = 0 := by
  cases roundUp <;> simp [amountBDelta]

/-- The rounded-down amount never exceeds the rounded-up amount. -/
theorem amountADelta_down_le_up (p q liquidity : Nat) :
    amountADelta p q liquidity false ≤ amountADelta p q liquidity true :=
  roundedDiv_false_le_true _ _

/-- The rounded-down amount never exceeds the rounded-up amount. -/
theorem amountBDelta_down_le_up (p q liquidity : Nat) :
    amountBDelta p q liquidity false ≤ amountBDelta p q liquidity true :=
  roundedDiv_false_le_true _ _

/-- The two roundings of the token-B amount differ by at most one unit. -/
theorem amountBDelta_up_le_down_add_one (p q liquidity : Nat) :
    amountBDelta p q liquidity true ≤ amountBDelta p q liquidity false + 1 := by
  rw [amountBDelta, amountBDelta, roundedDiv_true, roundedDiv_false]
  exact ceilDiv_le_div_add_one _ _

theorem amountADelta_mono_liquidity (p q : Nat) {liquidity liquidity' : Nat} (roundUp : Bool)
    (h : liquidity ≤ liquidity') :
    amountADelta p q liquidity roundUp ≤ amountADelta p q liquidity' roundUp := by
  unfold amountADelta
  apply roundedDiv_mono_left
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)

theorem amountBDelta_mono_liquidity (p q : Nat) {liquidity liquidity' : Nat} (roundUp : Bool)
    (h : liquidity ≤ liquidity') :
    amountBDelta p q liquidity roundUp ≤ amountBDelta p q liquidity' roundUp := by
  unfold amountBDelta
  apply roundedDiv_mono_left
  exact Nat.mul_le_mul_right _ h

/-- Paying out token B in two steps `p → q → r` never pays more than one step `p → r`. -/
theorem amountBDelta_down_add_le {p q r : Nat} (liquidity : Nat) (hpq : p ≤ q) (hqr : q ≤ r) :
    amountBDelta p q liquidity false + amountBDelta q r liquidity false ≤
      amountBDelta p r liquidity false := by
  rw [amountBDelta, amountBDelta, amountBDelta, roundedDiv_false, roundedDiv_false,
    roundedDiv_false, ← sqrtPriceDistance_add hpq hqr, Nat.mul_add]
  exact Nat.add_div_le_add_div _ _ _

/-- Charging token B in two steps `p → q → r` never charges less than one step `p → r`. -/
theorem amountBDelta_up_le_add {p q r : Nat} (liquidity : Nat) (hpq : p ≤ q) (hqr : q ≤ r) :
    amountBDelta p r liquidity true ≤
      amountBDelta p q liquidity true + amountBDelta q r liquidity true := by
  rw [amountBDelta, amountBDelta, amountBDelta, roundedDiv_true, roundedDiv_true,
    roundedDiv_true, ← sqrtPriceDistance_add hpq hqr, Nat.mul_add]
  exact ceilDiv_add_le _ _ _

/-! ## Swap steps -/

/-- A swap step charges its input rounded up. -/
theorem inputAmount_eq (aToB : Bool) (current next liquidity : Nat) :
    inputAmount aToB current next liquidity =
      if aToB then amountADelta current next liquidity true
      else amountBDelta current next liquidity true := rfl

/-- A swap step pays its output rounded down. -/
theorem outputAmount_eq (aToB : Bool) (current next liquidity : Nat) :
    outputAmount aToB current next liquidity =
      if aToB then amountBDelta current next liquidity false
      else amountADelta current next liquidity false := rfl

/-- Taking in token A, a pool never charges less than it would pay out for
the same movement in the opposite direction. -/
theorem outputAmount_not_aToB_le_inputAmount_aToB (current next liquidity : Nat) :
    outputAmount false next current liquidity ≤ inputAmount true current next liquidity := by
  simp only [outputAmount, inputAmount, Bool.false_eq_true, if_false, if_true]
  rw [amountADelta_comm]
  exact amountADelta_down_le_up _ _ _

/-- Taking in token B, a pool never charges less than it would pay out for
the same movement in the opposite direction. -/
theorem outputAmount_aToB_le_inputAmount_not_aToB (current next liquidity : Nat) :
    outputAmount true next current liquidity ≤ inputAmount false current next liquidity := by
  simp only [outputAmount, inputAmount, Bool.false_eq_true, if_false, if_true]
  rw [amountBDelta_comm]
  exact amountBDelta_down_le_up _ _ _

/-! ## Fee growth -/

@[simp]
theorem feeGrowthIncrement_zero_liquidity (fee : Nat) : feeGrowthIncrement fee 0 = 0 := by
  simp [feeGrowthIncrement]

/-- Distributing the fee growth back over the liquidity never pays out more
than the fee collected (in Q64.64 units). -/
theorem feeGrowthIncrement_mul_le (fee liquidity : Nat) :
    feeGrowthIncrement fee liquidity * liquidity ≤ fee * q64 := by
  unfold feeGrowthIncrement
  split
  · simp
  · exact Nat.div_mul_le_self _ _

theorem feeGrowthIncrement_mono_fee {fee fee' : Nat} (liquidity : Nat) (h : fee ≤ fee') :
    feeGrowthIncrement fee liquidity ≤ feeGrowthIncrement fee' liquidity := by
  unfold feeGrowthIncrement
  split
  · simp
  · exact Nat.div_le_div_right (Nat.mul_le_mul_right _ h)

end Solanalib.Finance.ConcentratedLiquidity
