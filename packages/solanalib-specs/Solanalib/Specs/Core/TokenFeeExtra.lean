/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenFee

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- The inverse helper first calculates the gross amount, then applies the
ordinary checked fee calculation to that amount. It does not subtract the
requested net amount from the gross result. -/
def TransferFee.calculateInverseFee (fee : TransferFee) (postFeeAmount : UInt64) :
    Option UInt64 := do
  let gross ← fee.calculatePreFeeAmount postFeeAmount
  fee.calculateFee gross

/-- The selected fee record is applied at the requested epoch. -/
def TransferFeeConfig.calculateEpochFee (config : TransferFeeConfig)
    (epoch amount : UInt64) : Option UInt64 :=
  (config.getEpochFee epoch).calculateFee amount

/-- The inverse calculation uses the same epoch comparison as direct fees. -/
def TransferFeeConfig.calculateInverseEpochFee (config : TransferFeeConfig)
    (epoch amount : UInt64) : Option UInt64 :=
  (config.getEpochFee epoch).calculateInverseFee amount

/-- A successful inverse fee obeys the cap of the selected record, even though
checked arithmetic may prevent the computation from returning a value. -/
theorem TransferFee.calculateInverseFee_le_max {fee : TransferFee}
    {amount charged : UInt64} (success : fee.calculateInverseFee amount = some charged) :
    charged.toNat ≤ fee.maximumFee.toNat := by
  unfold calculateInverseFee at success
  cases gross : fee.calculatePreFeeAmount amount with
  | none => simp [gross] at success
  | some value => exact calculateFee_le_max (by simpa [gross] using success)

/-- Above 100 percent, a positive requested net amount fails before the second
fee calculation. The configured maximum does not make that branch succeed. -/
theorem TransferFee.calculateInverseFee_excess_rate (fee : TransferFee) (amount : UInt64)
    (excess : FeeArithmetic.basisPointScale < fee.basisPoints.toNat)
    (positive : amount.toNat ≠ 0) : fee.calculateInverseFee amount = none := by
  simp [calculateInverseFee, fee.calculatePreFeeAmount_excess_rate amount excess positive]

/-- At activation, both epoch wrappers use the newer record. -/
theorem TransferFeeConfig.calculateEpochFee_at (config : TransferFeeConfig) (amount : UInt64) :
    config.calculateEpochFee config.newer.epoch amount = config.newer.calculateFee amount ∧
      config.calculateInverseEpochFee config.newer.epoch amount =
        config.newer.calculateInverseFee amount := by
  simp [calculateEpochFee, calculateInverseEpochFee, getEpochFee_at]

end Solanalib.Specs.Core.Token
