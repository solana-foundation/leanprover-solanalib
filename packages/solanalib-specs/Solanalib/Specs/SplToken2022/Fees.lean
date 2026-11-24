/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenFeeExtra
public import Solanalib.Specs.SplToken2022Interface.Fees
public import Solanalib.Specs.SplToken2022Interface.FeeReference

@[expose] public section

open Solanalib.Specs

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplToken2022.extension.transfer_fee

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token

namespace TransferFeeConfig

/-- Select by epoch and apply the ordinary fee calculation. -/
def calculate_epoch_fee_contract :
    Solanalib.Contracts.Model TransferFeeConfig (UInt64 × UInt64) (Option UInt64) :=
  .returning (fun _ _ => True) fun before args value after =>
    value = before.calculateEpochFee args.1 args.2 ∧ after = before

/-- Exact total reference; epochs are compared as unsigned 64-bit values. -/
def calculateEpochFeeReference (config : TransferFeeConfig) (args : UInt64 × UInt64) :
    Option UInt64 × TransferFeeConfig := (config.calculateEpochFee args.1 args.2, config)

/-- The direct epoch wrapper realizes its full contract. -/
theorem calculate_epoch_fee_reference :
    calculate_epoch_fee_contract.RealizedBy calculateEpochFeeReference := by
  intro before args _
  exact ⟨rfl, rfl⟩

/-- Distinct records inhabit the precondition of the epoch wrapper. -/
theorem calculate_epoch_fee_satisfiable : calculate_epoch_fee_contract.Satisfiable :=
  ⟨⟨.zero, .zero, 7, ⟨0, 10, 100⟩, ⟨10, 20, 250⟩⟩, (10, 100), trivial⟩

/-- Select by epoch and apply the checked inverse fee calculation. -/
def calculate_inverse_epoch_fee_contract :
    Solanalib.Contracts.Model TransferFeeConfig (UInt64 × UInt64) (Option UInt64) :=
  .returning (fun _ _ => True) fun before args value after =>
    value = before.calculateInverseEpochFee args.1 args.2 ∧ after = before

/-- Exact inverse wrapper reference. -/
def calculateInverseEpochFeeReference (config : TransferFeeConfig) (args : UInt64 × UInt64) :
    Option UInt64 × TransferFeeConfig := (config.calculateInverseEpochFee args.1 args.2, config)

/-- Both selection and inverse failure behavior are retained. -/
theorem calculate_inverse_epoch_fee_reference :
    calculate_inverse_epoch_fee_contract.RealizedBy calculateInverseEpochFeeReference := by
  intro before args _
  exact ⟨rfl, rfl⟩

/-- The inverse epoch wrapper has a concrete admitted receiver. -/
theorem calculate_inverse_epoch_fee_satisfiable :
    calculate_inverse_epoch_fee_contract.Satisfiable :=
  ⟨⟨.zero, .zero, 7, ⟨0, 10, 100⟩, ⟨10, 20, 250⟩⟩, (10, 100), trivial⟩

end TransferFeeConfig

end Solanalib.Specs.SplToken2022.extension.transfer_fee

namespace Solanalib.Specs.SplToken2022.extension.transfer_fee

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token

namespace TransferFee

/-- The older PodU64/PodU16 fields decode to the same bounded integers. The
checked arithmetic, narrowing-before-cap and zero branches match the shared
fee model; this is a whole-contract alias, not only a success-result equation. -/
abbrev calculate_fee_contract :=
  SplToken2022Interface.extension.transfer_fee.TransferFee.calculate_fee_contract

/-- Shared exact reference for the arithmetic. -/
abbrev calculateFeeReference :=
  SplToken2022Interface.extension.transfer_fee.TransferFee.calculateFeeReference

/-- Every input uses the shared complete fee behavior. -/
theorem calculate_fee_reference : calculate_fee_contract.RealizedBy calculateFeeReference :=
  SplToken2022Interface.extension.transfer_fee.TransferFee.calculate_fee_reference

/-- The fee contract has a concrete admitted record and amount. -/
theorem calculate_fee_satisfiable : calculate_fee_contract.Satisfiable :=
  SplToken2022Interface.extension.transfer_fee.TransferFee.calculate_fee_satisfiable

/-- Invert through the checked gross-amount helper, then calculate its fee. -/
def calculate_inverse_fee_contract :
    Solanalib.Contracts.Model TransferFee UInt64 (Option UInt64) :=
  .returning (fun _ _ => True) fun before amount value after =>
    value = before.calculateInverseFee amount ∧ after = before

/-- Exact total reference, including every None branch. -/
def calculateInverseFeeReference (fee : TransferFee) (amount : UInt64) :
    Option UInt64 × TransferFee := (fee.calculateInverseFee amount, fee)

/-- The reference realizes the full inverse contract. -/
theorem calculate_inverse_fee_reference :
    calculate_inverse_fee_contract.RealizedBy calculateInverseFeeReference := by
  intro before args _
  exact ⟨rfl, rfl⟩

/-- A nonzero rate and amount are admitted without an assumed success. -/
theorem calculate_inverse_fee_satisfiable : calculate_inverse_fee_contract.Satisfiable :=
  ⟨⟨0, 10, 250⟩, 100, trivial⟩

end TransferFee

namespace TransferFeeConfig

/-- The source returns a reference to the selected field of the same parent;
the old Pod field representation does not change this reference contract. -/
abbrev get_epoch_fee_contract :=
  SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.get_epoch_fee_live_contract

/-- The same existing-parent interpretation supplies the complete reference. -/
abbrev getEpochFeeReference :=
  SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.getEpochFeeLiveReference

/-- Explicit nonempty two-record receiver interpretation. -/
abbrev getEpochFeeSample :=
  SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.getEpochFeeLiveSample

/-- Field identity, equality boundary and current parent observation are all
preserved by the shared family. -/
theorem get_epoch_fee_reference : FamilyReference get_epoch_fee_contract getEpochFeeReference :=
  SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.get_epoch_fee_live_reference

/-- The shared actual receiver read supplies admission. -/
theorem get_epoch_fee_satisfiable : FamilySatisfiable get_epoch_fee_contract getEpochFeeSample :=
  SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.get_epoch_fee_live_satisfiable

/-- The older family has the same concrete equality-boundary execution. -/
theorem get_epoch_fee_has_execution :
    FamilyHasExecution get_epoch_fee_contract getEpochFeeReference getEpochFeeSample :=
  SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.get_epoch_fee_live_has_execution

end TransferFeeConfig

end Solanalib.Specs.SplToken2022.extension.transfer_fee
