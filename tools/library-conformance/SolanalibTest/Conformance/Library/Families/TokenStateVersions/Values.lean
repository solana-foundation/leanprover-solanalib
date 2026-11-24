/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SplToken2022Interface.Fees
import SolanalibTest.Conformance.Library.Families.TokenInterface.Fees
import SolanalibTest.Conformance.Library.Families.Anchor.Graph
import Solanalib.Specs.Core.TokenExtensionFee
import Solanalib.Specs.SplToken2022.Fees
import Solanalib.Specs.SplToken2022.StateExtra
import Solanalib.Specs.SplTokenMetadataInterface.State

set_option autoImplicit false

open Solanalib.Specs
open Solanalib.Specs.SplToken2022
open Solanalib.Specs.SplToken2022Interface

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.Values

open Lean (Json)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface
open SolanalibTest.Conformance.Library.Families.Anchor (PGraph decideProjected)

def noArgs (args : Json) : Result Unit :=
  if args == Json.mkObj [] then pure () else throw "expected no explicit arguments"

/-- The test keeps the actual packed Pod receiver, including all raw rates. -/
def feeConfig (j : Json) : Result TransferFeeConfig := do
  let bytes ← asBytes j
  unless bytes.length == 108 do throw "TransferFeeConfig must contain 108 bytes"
  pure (transferFeeConfigRepresentation.observe bytes)

def arithmetic (inverse : Bool) : Checker where
  function := "spl_token_2022::extension::transfer_fee::TransferFee::" ++
    if inverse then "calculate_inverse_fee" else "calculate_fee"
  generics := []
  reference := if inverse then
    "Solanalib.Specs.SplToken2022.extension.transfer_fee.TransferFee.calculateInverseFeeRef\
      erence"
      else
    "Solanalib.Specs.SplToken2022.extension.transfer_fee.TransferFee.calculateFeeReference"
  decides := [if inverse then
    "Solanalib.Specs.SplToken2022.extension.transfer_fee.TransferFee.calculateInverseFeeRef\
      erence"
      else
    "Solanalib.Specs.SplToken2022.extension.transfer_fee.TransferFee.calculateFeeReference"]
  check := fun c => do
    let reference := if inverse then
      extension.transfer_fee.TransferFee.calculateInverseFeeReference
        else
      SplToken2022.extension.transfer_fee.TransferFee.calculateFeeReference
    decideReturns (returnsOf reference) reference rfl
      (← Fees.transferFee c.state) (← Fees.amount c.args)
      Fees.optU64 Fees.transferFee Fees.optU64Json Fees.transferFeeJson c.outcome

def epoch (inverse : Bool) : Checker where
  function := "spl_token_2022" ++
    "::extension::transfer_fee::TransferFeeConfig::" ++
    if inverse then "calculate_inverse_epoch_fee" else "calculate_epoch_fee"
  generics := []
  reference := "Solanalib.Specs.SplToken2022" ++
    ".extension.transfer_fee.TransferFeeConfig." ++
    if inverse then "calculateInverseEpochFeeReference" else "calculateEpochFeeReference"
  decides := ["Solanalib.Specs.SplToken2022" ++
    ".extension.transfer_fee.TransferFeeConfig." ++
    if inverse then "calculateInverseEpochFeeReference" else "calculateEpochFeeReference"]
  check := fun c => do
    let reference := if inverse then
        extension.transfer_fee.TransferFeeConfig.calculateInverseEpochFeeReference
      else
        SplToken2022.extension.transfer_fee.TransferFeeConfig.calculateEpochFeeReference
    decideReturns (returnsOf reference) reference rfl
      (← feeConfig c.state) (← Fees.u64Field c.args "epoch", ← Fees.amount c.args)
      Fees.optU64 feeConfig Fees.optU64Json (fun _ => c.state) c.outcome

/-- Decide the actual old-version precondition at its concrete parent index. -/
def selectedFeeDecision (before : TransferFeeConfig) (epoch : UInt64) :
    Decidable
      ((extension.transfer_fee.TransferFeeConfig.get_epoch_fee_contract.contract
        extension.transfer_fee.TransferFeeConfig.getEpochFeeSample).requires
        before ⟨(), epoch⟩) :=
  decidable_of_iff _ (Fees.live_requires_iff before epoch).symm

/-- At this concrete parent interpretation every state has its live parent.
The proof exercises the same explicit decision used by the checker. -/
theorem selectedFee_requires (before : TransferFeeConfig) (epoch : UInt64) :
    ((extension.transfer_fee.TransferFeeConfig.get_epoch_fee_contract.contract
      extension.transfer_fee.TransferFeeConfig.getEpochFeeSample).requires
      before ⟨(), epoch⟩) ↔ True := by
  letI := selectedFeeDecision before epoch
  have checked : decide
      ((extension.transfer_fee.TransferFeeConfig.get_epoch_fee_contract.contract
        extension.transfer_fee.TransferFeeConfig.getEpochFeeSample).requires
        before ⟨(), epoch⟩) = true :=
    decide_eq_true ((Fees.live_requires_iff before epoch).2 trivial)
  exact ⟨fun _ => trivial, fun _ => of_decide_eq_true checked⟩

def selectedFee : Checker where
  function := "spl_token_2022::extension::transfer_fee::TransferFeeConfig::get_epoch_fee"
  generics := []
  reference :=
    "Solanalib.Specs.SplToken2022.extension.transfer_fee.TransferFeeConfig.getEpochFeeRefer\
      ence"
  decides :=
    ["Solanalib.Specs.SplToken2022.extension.transfer_fee.TransferFeeConfig.getEpochFeeRefe\
      rence"]
  decidesRequires :=
    ["Solanalib.Specs.SplToken2022.extension.transfer_fee.TransferFeeConfig.getEpochFeeRefe\
      rence"]
  check := fun c => do
    let before ← feeConfig c.state
    let epoch ← Fees.u64Field c.args "epoch"
    let outcome : Outcome TransferFeeConfig (FeeReference.Reference Unit) Empty Empty :=
      .returned ⟨(), FeeReference.selectField before epoch⟩ before
    let project : Outcome TransferFeeConfig (FeeReference.Reference Unit) Empty Empty → Json
      | .returned reference after => returnedJson
          (Json.mkObj [("field", Fees.fieldJson reference.field),
            ("value", Fees.transferFeeJson (reference.field.get after))]) c.state
      | .unwound reason _ => reason.elim
      | .terminated reason => reason.elim
    have graph : PGraph
        (extension.transfer_fee.TransferFeeConfig.getEpochFeeReference
          extension.transfer_fee.TransferFeeConfig.getEpochFeeSample
          before ⟨(), epoch⟩) (some outcome) := by
      intro final
      exact (Fees.live_iff before epoch final).trans
        ⟨congrArg some, Option.some.inj⟩
    have : Decidable
        ((extension.transfer_fee.TransferFeeConfig.get_epoch_fee_contract.contract
          extension.transfer_fee.TransferFeeConfig.getEpochFeeSample).requires
          before ⟨(), epoch⟩) := selectedFeeDecision before epoch
    let admitted := decide
      ((extension.transfer_fee.TransferFeeConfig.get_epoch_fee_contract.contract
        extension.transfer_fee.TransferFeeConfig.getEpochFeeSample).requires
        before ⟨(), epoch⟩)
    let verdict := decideProjected _ (some outcome) graph
      (fun final => project final == c.outcome) (some true) (fun _ => project outcome)
    let retained ← feeConfig (← field c.outcome "state")
    pure ⟨admitted && verdict.admitted && retained == before, verdict.expected⟩

def account (j : Json) : Result Account := do
  match unpackAccountUnchecked (← asBytes j) with
  | .ok account => pure account
  | .error _ => throw "invalid packed account fields"

def frozen : Checker where
  function := "spl_token_2022::state::Account::is_frozen"
  generics := []
  reference := "Solanalib.Specs.SplToken2022.state.Account.isFrozenReference"
  decides := ["Solanalib.Specs.SplToken2022.state.Account.isFrozenReference"]
  check := fun c => do
    let _ ← noArgs c.args
    decideReturns (returnsOf state.Account.isFrozenReference)
      state.Account.isFrozenReference rfl (← account c.state) ()
      Json.getBool? account Json.bool (fun _ => c.state) c.outcome

def metadata (j : Json) : Result Metadata := do
  pure ⟨← keyField j "authority", ← keyField j "mint",
    ← (← field j "name").getStr?, ← (← field j "symbol").getStr?,
    ← (← field j "uri").getStr?,
    ← listField j "additional" (fun entry => do
      let values ← entry.getArr?
      match values.toList with
      | [key, value] => pure (← key.getStr?, ← value.getStr?)
      | _ => throw "metadata additional entry must have two strings")⟩

def metadataJson (value : Metadata) : Json := Json.mkObj [
  ("authority", pubkeyJson value.updateAuthority), ("mint", pubkeyJson value.mint),
  ("name", Json.str value.name), ("symbol", Json.str value.symbol), ("uri", Json.str value.uri),
  ("additional", Lean.toJson value.additionalMetadata)]

def metadataDefault : Checker where
  function :=
    "<spl_token_metadata_interface::state::TokenMetadata as \
      core::default::Default>::default"
  generics := []
  reference := "Solanalib.Specs.SplTokenMetadataInterface.state.TokenMetadata.defaultRefere\
    nce"
  decides := ["Solanalib.Specs.SplTokenMetadataInterface.state.TokenMetadata.defaultReferen\
    ce"]
  check := fun c => do
    let _ ← noArgs c.args
    let verdict ← decideReturns
      (returnsOf Solanalib.Specs.SplTokenMetadataInterface.state.TokenMetadata.defaultReference)
      Solanalib.Specs.SplTokenMetadataInterface.state.TokenMetadata.defaultReference rfl
      (← asUnit c.state) () metadata asUnit metadataJson (fun _ => Json.null) c.outcome
    let capacities ← field (← field c.outcome "result") "capacities"
    pure ⟨verdict.admitted && capacities == Lean.toJson ([0, 0, 0, 0] : List Nat), verdict.expected⟩

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.Values

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.Values

open Lean (Json)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface
open SolanalibTest.Conformance.Library.Families.Anchor (PGraph decideProjected)

def epochForVersion (olderInterface inverse : Bool) : Checker where
  function := (if olderInterface then "spl_token_2022_interface" else "spl_token_2022") ++
    "::extension::transfer_fee::TransferFeeConfig::" ++
    if inverse then "calculate_inverse_epoch_fee" else "calculate_epoch_fee"
  generics := []
  reference := if olderInterface then
    "Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.calcula\
      teEpochFeeReference"
    else if inverse then
      "Solanalib.Specs.SplToken2022.extension.transfer_fee.TransferFeeConfig.calculateInver\
        seEpochFeeReference"
    else
      "Solanalib.Specs.SplToken2022.extension.transfer_fee.TransferFeeConfig.calculateEpoch\
        FeeReference"
  decides := [if olderInterface then
    "Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.calcula\
      teEpochFeeReference"
    else if inverse then
      "Solanalib.Specs.SplToken2022.extension.transfer_fee.TransferFeeConfig.calculateInver\
        seEpochFeeReference"
    else
      "Solanalib.Specs.SplToken2022.extension.transfer_fee.TransferFeeConfig.calculateEpoch\
        FeeReference"]
  check := fun c => do
    let reference := if olderInterface then
      SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.calculateEpochFeeReference
      else if inverse then
        extension.transfer_fee.TransferFeeConfig.calculateInverseEpochFeeReference
      else
        SplToken2022.extension.transfer_fee.TransferFeeConfig.calculateEpochFeeReference
    decideReturns (returnsOf reference) reference rfl
      (← feeConfig c.state) (← Fees.u64Field c.args "epoch", ← Fees.amount c.args)
      Fees.optU64 feeConfig Fees.optU64Json (fun _ => c.state) c.outcome

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.Values
