/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.Common
import Solanalib.Specs.SplToken2022Interface.Fees
import Solanalib.Specs.SplToken2022Interface.FeeReference

/-!
# Transfer-fee arithmetic and epoch selection (spl-token-2022-interface 3.1.1)

The three `TransferFee` methods are pure references over the receiver (the
model state) and the amount: each record is decided as the graph of the
registered reference.

`TransferFeeConfig::get_epoch_fee` has two registered models: the value
observation `getEpochFeeReference` (the copied fee) and the borrowed-field
family `getEpochFeeLiveReference`, decided at its registered sample index
`getEpochFeeLiveSample` (the configuration itself as state, one parent
identity) through `live_iff`. The record keeps the field the returned
reference points to (compared by address natively) and the value read
through it; one checker decides both.
-/

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.Fees

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open Solanalib.Specs.SplToken2022Interface.extension.transfer_fee

def u64Field (j : Json) (k : String) : Result UInt64 := do
  pure (UInt64.ofNat (← uintField 64 j k))

def transferFee (j : Json) : Result TransferFee := do
  pure ⟨← u64Field j "epoch", ← u64Field j "maximum_fee",
    UInt16.ofNat (← uintField 16 j "transfer_fee_basis_points")⟩

def transferFeeJson (f : TransferFee) : Json := Json.mkObj [
  ("epoch", Lean.toJson f.epoch.toNat), ("maximum_fee", Lean.toJson f.maximumFee.toNat),
  ("transfer_fee_basis_points", Lean.toJson f.basisPoints.toNat)]

def transferFeeConfig (j : Json) : Result TransferFeeConfig := do
  pure ⟨← keyField j "transfer_fee_config_authority", ← keyField j "withdraw_withheld_autho\
    rity",
    ← u64Field j "withheld_amount", ← transferFee (← field j "older_transfer_fee"),
    ← transferFee (← field j "newer_transfer_fee")⟩

def transferFeeConfigJson (c : TransferFeeConfig) : Json := Json.mkObj [
  ("transfer_fee_config_authority", pubkeyJson c.configAuthority),
  ("withdraw_withheld_authority", pubkeyJson c.withdrawWithheldAuthority),
  ("withheld_amount", Lean.toJson c.withheldAmount.toNat),
  ("older_transfer_fee", transferFeeJson c.older), ("newer_transfer_fee", transferFeeJson c.newer)]

def amount (j : Json) : Result UInt64 := u64Field j "amount"

def optU64 (j : Json) : Result (Option UInt64) := asOption (fun v => do pure (UInt64.ofNat (←
  asUInt 64 v))) j

def optU64Json : Option UInt64 → Json := optionJson fun v => Lean.toJson v.toNat

/-- The registered references compute the shared fee arithmetic (by definition). -/
theorem calculate_fee_evaluated :
    TransferFee.calculateFeeReference = fun fee a => (fee.calculateFee a, fee) := rfl

theorem calculate_post_fee_amount_evaluated :
    TransferFee.calculatePostFeeAmountReference = fun fee a => (fee.calculatePostFeeAmount a, fee)
      := rfl

theorem calculate_pre_fee_amount_evaluated :
    TransferFee.calculatePreFeeAmountReference = fun fee a => (fee.calculatePreFeeAmount a, fee) :=
      rfl

def arithmeticChecker (method reference : String)
    (ref : TransferFee → UInt64 → Option UInt64 × TransferFee) : Checker where
  function := "spl_token_2022_interface::extension::transfer_fee::TransferFee::" ++ method
  generics := []
  reference := reference
  decides := [reference]
  check := fun c => do
    decideReturns (returnsOf ref) ref rfl (← transferFee c.state) (← amount c.args)
      optU64 transferFee optU64Json transferFeeJson c.outcome

/-! ## Epoch selection -/

abbrev Sample := TransferFeeConfig.getEpochFeeLiveSample

/-- At the registered sample index (the state is the configuration, one
parent), the borrowed-field relation admits exactly the selected field of the
current configuration, with the state unchanged. -/
theorem live_iff (before : TransferFeeConfig) (epoch : UInt64)
    (o : Outcome TransferFeeConfig (FeeReference.Reference Unit) Empty Empty) :
    TransferFeeConfig.getEpochFeeLiveReference Sample before ⟨(), epoch⟩ o ↔
      Outcome.returned ⟨(), FeeReference.selectField before epoch⟩ before = o := by
  constructor
  · rintro ⟨config, ⟨_, hc⟩, rfl⟩
    cases hc
    rfl
  · intro h
    exact ⟨before, ⟨trivial, rfl⟩, h.symm⟩

/-- The precondition of the live family (a current read of the parent) at the
sample index: the parent is the state itself, so it always holds. The checker
decides it through this equivalence. -/
theorem live_requires_iff (before : TransferFeeConfig) (epoch : UInt64) :
    (TransferFeeConfig.get_epoch_fee_live_contract.contract Sample).requires before ⟨(), epoch⟩ ↔
      True :=
  ⟨fun _ => trivial, fun _ => ⟨before, trivial, rfl⟩⟩

def fieldOf : String → Result FeeReference.Field
  | "older" => pure .older
  | "newer" => pure .newer
  | other => throw s!"unknown field {other}"

def fieldJson : FeeReference.Field → Json
  | .older => "older"
  | .newer => "newer"

theorem get_epoch_fee_evaluated :
    TransferFeeConfig.getEpochFeeReference = fun config e => (config.getEpochFee e, config) := rfl

def epochChecker : Checker :=
  pairChecker "spl_token_2022_interface::extension::transfer_fee::TransferFeeConfig::get_ep\
    och_fee"
    []
    "Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.getEpoc\
      hFeeLiveReference"
    "Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.getEpoc\
      hFeeReference" (fun c => do
    let before ← transferFeeConfig c.state
    let epoch ← u64Field c.args "epoch"
    let selected := FeeReference.selectField before epoch
    let (value, _) := TransferFeeConfig.getEpochFeeReference before epoch
    let expected := returnedJson
      (Json.mkObj [("field", fieldJson selected), ("value", transferFeeJson value)])
      (transferFeeConfigJson before)
    match ← (← field c.outcome "exit").getStr? with
    | "returned" =>
      let result ← field c.outcome "result"
      let after ← transferFeeConfig (← field c.outcome "state")
      let recordedField ← fieldOf (← (← field result "field").getStr?)
      let recordedValue ← transferFee (← field result "value")
      let liveOutcome : Outcome TransferFeeConfig (FeeReference.Reference Unit) Empty Empty :=
        .returned ⟨(), recordedField⟩ after
      have : Decidable (TransferFeeConfig.getEpochFeeLiveReference Sample before ⟨(), epoch⟩
        liveOutcome) :=
        decidable_of_iff _ (live_iff before epoch liveOutcome).symm
      have : Decidable ((TransferFeeConfig.get_epoch_fee_live_contract.contract Sample).requires
          before ⟨(), epoch⟩) := decidable_of_iff _ (live_requires_iff before epoch).symm
      let liveOk := decide ((TransferFeeConfig.get_epoch_fee_live_contract.contract Sample).requires
          before ⟨(), epoch⟩) &&
        decide (TransferFeeConfig.getEpochFeeLiveReference Sample before ⟨(), epoch⟩ liveOutcome)
      let valueOk := decide (returnsOf TransferFeeConfig.getEpochFeeReference before epoch
        (Outcome.returned (Unwind := Empty) (Terminal := Empty) recordedValue after))
      return (liveOk, valueOk, expected)
    | _ => return (false, false, expected))
    ["Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.getEpo\
      chFeeLiveReference"]

def checkers : List Checker := [
  arithmeticChecker "calculate_fee"
    "Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFee.calculateFeeR\
      eference"
    TransferFee.calculateFeeReference,
  arithmeticChecker "calculate_post_fee_amount"
    "Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFee.calculatePost\
      FeeAmountReference"
    TransferFee.calculatePostFeeAmountReference,
  arithmeticChecker "calculate_pre_fee_amount"
    "Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFee.calculatePreF\
      eeAmountReference"
    TransferFee.calculatePreFeeAmountReference,
  epochChecker]

end SolanalibTest.Conformance.Library.Families.TokenInterface.Fees
