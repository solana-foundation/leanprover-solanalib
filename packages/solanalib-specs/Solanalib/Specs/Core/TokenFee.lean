/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Runtime.Basic

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- A decoded transfer-fee record. The full `u16` rate is retained: decoding
does not establish the separately checked policy bound of 10,000 basis points. -/
structure TransferFee where
  /-- Activation epoch, inspected only when choosing the fee of a configuration. -/
  epoch : UInt64
  /-- Maximum charged fee, applied after the raw fee has been narrowed. -/
  maximumFee : UInt64
  /-- Decoded rate, including values above the 10,000-point policy limit. -/
  basisPoints : UInt16
  deriving DecidableEq, Repr, Inhabited

/-- A decoded fee configuration. Authority fields retain their raw 32-byte
`MaybeNull<Address>` values; all-zero bytes denote an absent authority. -/
structure TransferFeeConfig where
  /-- Raw nullable authority allowed to configure transfer fees. -/
  configAuthority : Solanalib.Runtime.Pubkey
  /-- Raw nullable authority allowed to withdraw withheld fees. -/
  withdrawWithheldAuthority : Solanalib.Runtime.Pubkey
  /-- Withheld token amount retained without modification by fee selection. -/
  withheldAmount : UInt64
  /-- Selected record before the activation epoch of the newer record. -/
  older : TransferFee
  /-- Selected record at and after its activation epoch. -/
  newer : TransferFee
  deriving DecidableEq, Repr

namespace FeeArithmetic

/-- One hundred percent, in the units used by the token fee functions. -/
def basisPointScale : Nat := 10000

/-- The strict upper bound on a checked `u128` result. -/
def u128Limit : Nat := 2^128

/-- A checked `u128` result, represented without modular reduction. Call sites
provide operands decoded from bounded integers or preceding checked results. -/
def checkedU128 (value : Nat) : Option Nat :=
  if value < u128Limit then some value else none

/-- Conversion to `u64` fails before any downstream fee cap is applied. -/
def checkedU64 (value : Nat) : Option UInt64 :=
  if value < 2^64 then some (UInt64.ofNat value) else none

/-- Checked subtraction of nonnegative intermediate values. -/
def checkedSub (left right : Nat) : Option Nat :=
  if right ≤ left then some (left - right) else none

/-- Checked division retains the division-by-zero failure of the source. -/
def checkedDiv (numerator denominator : Nat) : Option Nat :=
  if denominator = 0 then none else some (numerator / denominator)

/-- The source checks `numerator + denominator`, subtracts one, then divides.
Reassociating the expression before checking would change overflow behavior. -/
def ceilDiv128 (numerator denominator : Nat) : Option Nat := do
  let sum ← checkedU128 (numerator + denominator)
  let adjusted ← checkedSub sum 1
  checkedDiv adjusted denominator

/-- A checked `u64` sum, with no wrapping on overflow. -/
def addU64 (left right : UInt64) : Option UInt64 :=
  checkedU64 (left.toNat + right.toNat)

/-- A checked `u64` difference, with no saturation on underflow. -/
def subU64 (left right : UInt64) : Option UInt64 := do
  let difference ← checkedSub left.toNat right.toNat
  checkedU64 difference

/-- Within its checked sum bound, the helper computes the mathematical
ceiling formula for every positive denominator. -/
theorem ceilDiv128_formula (numerator denominator : Nat)
    (positive : 0 < denominator) (bounded : numerator + denominator < u128Limit) :
    ceilDiv128 numerator denominator = some ((numerator + denominator - 1) / denominator) := by
  have subtracts : 1 ≤ numerator + denominator := by omega
  simp [ceilDiv128, checkedU128, checkedSub, checkedDiv, bounded, subtracts,
    Nat.ne_of_gt positive]

/-- Every successful positive-denominator result is the least integer whose
multiple reaches the numerator: its excess is less than one denominator. -/
theorem ceilDiv128_rounding {numerator denominator quotient : Nat}
    (positive : 0 < denominator)
    (success : ceilDiv128 numerator denominator = some quotient) :
    numerator ≤ quotient * denominator ∧ quotient * denominator < numerator + denominator := by
  have bounded : numerator + denominator < u128Limit := by
    by_cases bound : numerator + denominator < u128Limit
    · exact bound
    · simp [ceilDiv128, checkedU128, bound] at success
  have formula := ceilDiv128_formula numerator denominator positive bounded
  have quotientEq := Option.some.inj (success.symm.trans formula)
  subst quotient
  have remainder := Nat.mod_lt (numerator + denominator - 1) positive
  have division := Nat.mod_add_div (numerator + denominator - 1) denominator
  rw [Nat.mul_comm denominator] at division
  omega

/-- A successful checked conversion returns exactly the mathematical input. -/
theorem checkedU64_some {value : Nat} {converted : UInt64}
    (success : checkedU64 value = some converted) :
    converted.toNat = value := by
  unfold checkedU64 at success
  split at success
  next bounded =>
    cases success
    exact UInt64.toNat_ofNat_of_lt' bounded
  next => contradiction

/-- Once subtraction does not underflow, its difference still fits in `u64`.
The explicit result conversion of the model therefore adds no source failure. -/
theorem subU64_of_le (left right : UInt64) (ordered : right.toNat ≤ left.toNat) :
    subU64 left right = some (UInt64.ofNat (left.toNat - right.toNat)) := by
  have bounded : left.toNat - right.toNat < 2^64 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) left.toNat_lt
  simp [subU64, checkedSub, checkedU64, ordered, bounded]

/-- A successful subtraction records the exact additive balance. -/
theorem subU64_conserves {left right difference : UInt64}
    (success : subU64 left right = some difference) :
    difference.toNat + right.toNat = left.toNat := by
  unfold subU64 checkedSub at success
  split at success
  next ordered =>
    have decoded := checkedU64_some success
    omega
  next => contradiction

end FeeArithmetic

namespace TransferFee

open FeeArithmetic

/-- Compute the rounded-up raw fee, convert it to `u64`, and only then cap it.
This also describes records whose rate exceeds 100 percent. -/
def calculateFee (fee : TransferFee) (preFeeAmount : UInt64) : Option UInt64 :=
  if fee.basisPoints.toNat = 0 ∨ preFeeAmount.toNat = 0 then some 0
  else do
    let numerator ← checkedU128 (preFeeAmount.toNat * fee.basisPoints.toNat)
    let rounded ← ceilDiv128 numerator basisPointScale
    let raw ← checkedU64 rounded
    pure (if raw.toNat ≤ fee.maximumFee.toNat then raw else fee.maximumFee)

/-- Deduct the computed fee using a checked `u64` subtraction. -/
def calculatePostFeeAmount (fee : TransferFee) (preFeeAmount : UInt64) : Option UInt64 := do
  let charged ← fee.calculateFee preFeeAmount
  subU64 preFeeAmount charged

/-- Compute the input amount for a requested output using the branch
order of the source. A positive output with a rate above 10,000 fails checked denominator
subtraction, even when the maximum fee is zero. -/
def calculatePreFeeAmount (fee : TransferFee) (postFeeAmount : UInt64) : Option UInt64 :=
  if fee.basisPoints.toNat = 0 then some postFeeAmount
  else if postFeeAmount.toNat = 0 then some 0
  else if fee.basisPoints.toNat = basisPointScale then
    addU64 fee.maximumFee postFeeAmount
  else do
    let numerator ← checkedU128 (postFeeAmount.toNat * basisPointScale)
    let denominator ← checkedSub basisPointScale fee.basisPoints.toNat
    let raw ← ceilDiv128 numerator denominator
    let extra ← checkedSub raw postFeeAmount.toNat
    if fee.maximumFee.toNat ≤ extra then addU64 postFeeAmount fee.maximumFee
    else checkedU64 raw

/-- A zero rate always computes a zero fee, for every representable amount. -/
theorem calculateFee_zero_rate (fee : TransferFee) (amount : UInt64)
    (zero : fee.basisPoints.toNat = 0) : fee.calculateFee amount = some 0 := by
  simp [calculateFee, zero]

/-- A zero input has no fee, including for otherwise invalid rates. -/
theorem calculateFee_zero_amount (fee : TransferFee) :
    fee.calculateFee 0 = some 0 := by
  simp [calculateFee]

/-- Every successfully computed fee is at most the configured cap. This does
not imply success: converting the uncapped fee may already have failed. -/
theorem calculateFee_le_max {fee : TransferFee} {amount charged : UInt64}
    (success : fee.calculateFee amount = some charged) :
    charged.toNat ≤ fee.maximumFee.toNat := by
  unfold calculateFee at success
  split at success
  next => cases success; simp
  next =>
    cases numeratorEq : checkedU128 (amount.toNat * fee.basisPoints.toNat) with
    | none => simp [numeratorEq] at success
    | some numerator =>
      cases roundedEq : ceilDiv128 numerator basisPointScale with
      | none => simp [numeratorEq, roundedEq] at success
      | some rounded =>
        cases rawEq : checkedU64 rounded with
        | none => simp [numeratorEq, roundedEq, rawEq] at success
        | some raw =>
          by_cases bounded : raw.toNat ≤ fee.maximumFee.toNat
          · simp [numeratorEq, roundedEq, rawEq, bounded] at success
            cases success
            exact bounded
          · simp [numeratorEq, roundedEq, rawEq, bounded] at success
            cases success
            exact Nat.le_refl _

/-- A successful deduction preserves the gross amount as net plus fee. -/
theorem calculatePostFeeAmount_conserves {fee : TransferFee}
    {amount charged net : UInt64}
    (feeComputed : fee.calculateFee amount = some charged)
    (netComputed : fee.calculatePostFeeAmount amount = some net) :
    net.toNat + charged.toNat = amount.toNat := by
  apply subU64_conserves
  simpa [calculatePostFeeAmount, feeComputed] using netComputed

/-- At zero rate, the requested output is already the required input. -/
theorem calculatePreFeeAmount_zero_rate (fee : TransferFee) (amount : UInt64)
    (zero : fee.basisPoints.toNat = 0) :
    fee.calculatePreFeeAmount amount = some amount := by
  simp [calculatePreFeeAmount, zero]

/-- The zero-output shortcut precedes the invalid-rate denominator check. -/
theorem calculatePreFeeAmount_zero_amount (fee : TransferFee) :
    fee.calculatePreFeeAmount 0 = some 0 := by
  by_cases zero : fee.basisPoints.toNat = 0 <;> simp [calculatePreFeeAmount, zero]

/-- Exactly 100 percent uses checked cap-plus-output addition. -/
theorem calculatePreFeeAmount_full_rate (fee : TransferFee) (amount : UInt64)
    (rate : fee.basisPoints.toNat = basisPointScale)
    (positive : amount.toNat ≠ 0) :
    fee.calculatePreFeeAmount amount = addU64 fee.maximumFee amount := by
  simp [calculatePreFeeAmount, rate, positive, basisPointScale]

/-- Rates above 100 percent fail for positive requested outputs; they are not
clamped to the maximum permissible rate or excused by a zero cap. -/
theorem calculatePreFeeAmount_excess_rate (fee : TransferFee) (amount : UInt64)
    (excess : basisPointScale < fee.basisPoints.toNat)
    (positive : amount.toNat ≠ 0) :
    fee.calculatePreFeeAmount amount = none := by
  have nonzero : fee.basisPoints.toNat ≠ 0 := by
    simp only [basisPointScale] at excess
    omega
  have notFull : fee.basisPoints.toNat ≠ basisPointScale := by omega
  simp only [calculatePreFeeAmount, nonzero, positive, notFull, ite_false]
  cases checkedU128 (amount.toNat * basisPointScale) <;>
    simp [checkedSub, Nat.not_le_of_lt excess]

/-- An individual fee computation does not inspect the activation epoch. -/
theorem calculateFee_epoch_irrelevant (fee : TransferFee) (epoch amount : UInt64) :
    ({ fee with epoch := epoch } : TransferFee).calculateFee amount =
      fee.calculateFee amount := rfl

end TransferFee

namespace TransferFeeConfig

/-- Choose the newer record at and after its epoch, otherwise the older one.
The epoch of the older record does not restrict selection. -/
def getEpochFee (config : TransferFeeConfig) (epoch : UInt64) : TransferFee :=
  if config.newer.epoch.toNat ≤ epoch.toNat then config.newer else config.older

/-- At the exact activation epoch, the newer record is selected. -/
theorem getEpochFee_at (config : TransferFeeConfig) :
    config.getEpochFee config.newer.epoch = config.newer := by
  simp [getEpochFee]

/-- Every epoch before the newer record selects the older record, regardless
of the activation field of the older record. -/
theorem getEpochFee_before (config : TransferFeeConfig) (epoch : UInt64)
    (before : epoch.toNat < config.newer.epoch.toNat) :
    config.getEpochFee epoch = config.older := by
  simp [getEpochFee, Nat.not_le_of_lt before]

/-- Every epoch at or after the newer activation selects the newer record. -/
theorem getEpochFee_after (config : TransferFeeConfig) (epoch : UInt64)
    (after : config.newer.epoch.toNat ≤ epoch.toNat) :
    config.getEpochFee epoch = config.newer := by
  simp [getEpochFee, after]

end TransferFeeConfig

end Solanalib.Specs.Core.Token
