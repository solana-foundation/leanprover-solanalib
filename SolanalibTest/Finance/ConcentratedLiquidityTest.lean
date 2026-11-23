/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Finance.CompoundInterestApprox
import Solanalib.Finance.ConcentratedLiquidity

/-!
# Regression tests for concentrated liquidity and approximate compounding
-/

namespace SolanalibTest.Finance.ConcentratedLiquidity

open Solanalib.Finance Solanalib.Finance.ConcentratedLiquidity

/-- Moving the sqrt price by one whole unit (`2^64`) at liquidity `10` exchanges
`10` units of token B. -/
example : amountBDelta (2 ^ 64) (2 ^ 65) 10 false = 10 := by
  simp [amountBDelta, sqrtPriceDistance, q64_eq]

/-- A swap step charges at least what the reverse step pays. -/
example (p q l : Nat) : outputAmount true q p l ≤ inputAmount false p q l :=
  outputAmount_aToB_le_inputAmount_not_aToB p q l

example : cubicCompoundApprox 2 (1 / 10) = (1 + 1 / 10) ^ 2 :=
  cubicCompoundApprox_eq_pow (by decide) _

example : cubicCompoundApprox 10 (1 / 100) ≤ (1 + 1 / 100) ^ 10 :=
  cubicCompoundApprox_le_pow 10 (by norm_num)

end SolanalibTest.Finance.ConcentratedLiquidity
