/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenFeeExtra

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplToken2022Interface.extension.transfer_fee

open Solanalib.Specs.Core.Token

namespace TransferFee

/-- The pure, immutable fee calculation, including its `None` results. -/
def calculate_fee_contract : Solanalib.Contracts.Model TransferFee UInt64 (Option UInt64) :=
  .returning (fun _ _ => True) fun fee amount result after =>
    result = fee.calculateFee amount ∧ after = fee

/-- The total mathematical reference; it is not a Rust-body interpretation. -/
def calculateFeeReference (fee : TransferFee) (amount : UInt64) :
    Option UInt64 × TransferFee := (fee.calculateFee amount, fee)

/-- Closed realization of the helper used by post-fee amount calculation. -/
theorem calculate_fee_reference :
    calculate_fee_contract.RealizedBy calculateFeeReference := by
  intro fee amount _
  exact ⟨rfl, rfl⟩

/-- The precondition of the helper has a concrete inhabitant. -/
theorem calculate_fee_satisfiable : calculate_fee_contract.Satisfiable :=
  ⟨⟨0, 0, 0⟩, 0, trivial⟩

/-- Calculate the net amount, preserving checked fee conversion and deduction. -/
def calculate_post_fee_amount_contract :
    Solanalib.Contracts.Model TransferFee UInt64 (Option UInt64) :=
  .returning (fun _ _ => True) fun fee amount result after =>
    result = fee.calculatePostFeeAmount amount ∧ after = fee

/-- A total reference of the immutable net-amount calculation. -/
def calculatePostFeeAmountReference (fee : TransferFee) (amount : UInt64) :
    Option UInt64 × TransferFee := (fee.calculatePostFeeAmount amount, fee)

/-- The versioned net-amount contract has a closed realization. -/
theorem calculate_post_fee_amount_reference :
    calculate_post_fee_amount_contract.RealizedBy calculatePostFeeAmountReference := by
  intro fee amount _
  exact ⟨rfl, rfl⟩

/-- The precondition of the net-amount contract has a concrete inhabitant. -/
theorem calculate_post_fee_amount_satisfiable :
    calculate_post_fee_amount_contract.Satisfiable := ⟨⟨0, 0, 0⟩, 0, trivial⟩

/-- Compute the gross amount with exact special cases, checked rounding,
cap comparison, and overflow failures. No successful return is assumed. -/
def calculate_pre_fee_amount_contract :
    Solanalib.Contracts.Model TransferFee UInt64 (Option UInt64) :=
  .returning (fun _ _ => True) fun fee amount result after =>
    result = fee.calculatePreFeeAmount amount ∧ after = fee

/-- A total reference of the immutable gross-amount calculation. -/
def calculatePreFeeAmountReference (fee : TransferFee) (amount : UInt64) :
    Option UInt64 × TransferFee := (fee.calculatePreFeeAmount amount, fee)

/-- The versioned gross-amount contract has a closed realization. -/
theorem calculate_pre_fee_amount_reference :
    calculate_pre_fee_amount_contract.RealizedBy calculatePreFeeAmountReference := by
  intro fee amount _
  exact ⟨rfl, rfl⟩

/-- The precondition of the gross-amount contract has a concrete inhabitant. -/
theorem calculate_pre_fee_amount_satisfiable :
    calculate_pre_fee_amount_contract.Satisfiable := ⟨⟨0, 0, 0⟩, 0, trivial⟩

end TransferFee

namespace TransferFeeConfig

/-- Return the value of the selected immutable fee field. A Rust binding must
separately relate this value projection to the returned field reference. -/
def get_epoch_fee_contract : Solanalib.Contracts.Model TransferFeeConfig UInt64 TransferFee :=
  .returning (fun _ _ => True) fun config epoch result after =>
    result = config.getEpochFee epoch ∧ after = config

/-- A total reference that preserves the entire configuration. -/
def getEpochFeeReference (config : TransferFeeConfig) (epoch : UInt64) :
    TransferFee × TransferFeeConfig := (config.getEpochFee epoch, config)

/-- Epoch selection has a closed realization, including the equality case. -/
theorem get_epoch_fee_reference : get_epoch_fee_contract.RealizedBy getEpochFeeReference := by
  intro config epoch _
  exact ⟨rfl, rfl⟩

/-- Epoch selection has a concrete configuration and input. -/
theorem get_epoch_fee_satisfiable : get_epoch_fee_contract.Satisfiable :=
  ⟨⟨.zero, .zero, 0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩, 0, trivial⟩

end TransferFeeConfig

end Solanalib.Specs.SplToken2022Interface.extension.transfer_fee

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFeeConfig

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token

/-- Select by epoch and apply the checked immutable fee calculation. -/
def calculate_epoch_fee_contract :
    Solanalib.Contracts.Model TransferFeeConfig (UInt64 × UInt64) (Option UInt64) :=
  .returning (fun _ _ => True) fun before args value after =>
    value = before.calculateEpochFee args.1 args.2 ∧ after = before

/-- Exact total reference, including every failed fee calculation. -/
def calculateEpochFeeReference (config : TransferFeeConfig) (args : UInt64 × UInt64) :
    Option UInt64 × TransferFeeConfig := (config.calculateEpochFee args.1 args.2, config)

/-- Whole-contract reuse covers errors as well as successful fee values. -/
theorem calculate_epoch_fee_reference :
    calculate_epoch_fee_contract.RealizedBy calculateEpochFeeReference := by
  intro before args _
  exact ⟨rfl, rfl⟩

/-- A concrete receiver and amount inhabit this exact versioned contract. -/
theorem calculate_epoch_fee_satisfiable : calculate_epoch_fee_contract.Satisfiable :=
  ⟨⟨.zero, .zero, 7, ⟨0, 10, 100⟩, ⟨10, 20, 250⟩⟩, (10, 100), trivial⟩

end Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFeeConfig
