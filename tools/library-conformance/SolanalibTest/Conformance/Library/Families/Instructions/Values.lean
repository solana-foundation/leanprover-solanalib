/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Instructions.Common
import SolanalibTest.Conformance.Library.Pyth
import Solanalib.Specs.SolanaInstruction.Capabilities
import Solanalib.Specs.SolanaInstructionView.Capabilities
import Solanalib.Specs.SolanaSystemInterface.Capabilities
import Solanalib.Specs.PythSolanaReceiverSdk.Capabilities

/-!
# Family `Instructions`: total value models

The `AccountMeta` constructors, the InstructionView seed/signer conversions and
read-only signer metadata, and the System instruction value observations are
registered as `returnsOf` their `_model` (the `reference` of the catalogs); each
checker decides that graph, linked by `rfl`. The Pyth getter is registered as
the graph `outcome = Pyth.run aborts before args`; it is decided at the index
`⟨Unit, false⟩` (state `()`, the recorded `panic = "unwind"` profile).
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

open Solanalib.Specs.PythSolanaReceiverSdk

namespace SolanalibTest.Conformance.Library.Families.Instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Instruction
open SolanalibTest.Conformance.Library.Borsh

/-! ## The evaluated functions are the registered references -/

theorem account_meta_new_evaluated :
    Solanalib.Specs.SolanaInstruction.Capabilities.reference .AccountMeta_new PUnit.unit =
      returnsOf Solanalib.Specs.SolanaInstruction.AccountMeta.new_model := rfl

theorem account_meta_new_readonly_evaluated :
    Solanalib.Specs.SolanaInstruction.Capabilities.reference .AccountMeta_new_readonly PUnit.unit =
      returnsOf Solanalib.Specs.SolanaInstruction.AccountMeta.new_readonly_model := rfl

theorem v1_seed_from_slice_evaluated :
    Solanalib.Specs.SolanaInstructionView.Capabilities.reference .cpi_Seed_from_slice PUnit.unit =
      returnsOf Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_slice_model := rfl

theorem v1_signer_from_slice_evaluated :
    Solanalib.Specs.SolanaInstructionView.Capabilities.reference .cpi_Signer_from_slice PUnit.unit =
      returnsOf Solanalib.Specs.SolanaInstructionView.cpi.Signer.from_slice_model := rfl

theorem v2_seed_from_slice_evaluated :
    Solanalib.Specs.SolanaInstructionView.Capabilities.reference .cpi_Seed_from_slice PUnit.unit =
      returnsOf Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_slice_model := rfl

theorem v2_seed_from_array_evaluated :
    Solanalib.Specs.SolanaInstructionView.Capabilities.reference .cpi_Seed_from_array PUnit.unit =
      returnsOf Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_array_model := rfl

theorem v2_signer_from_array_evaluated :
    Solanalib.Specs.SolanaInstructionView.Capabilities.reference .cpi_Signer_from_array PUnit.unit =
      returnsOf Solanalib.Specs.SolanaInstructionView.cpi.Signer.from_array_model := rfl

theorem readonly_signer_evaluated :
    Solanalib.Specs.SolanaInstructionView.Capabilities.reference
      .InstructionAccount_readonly_signer PUnit.unit =
      returnsOf Solanalib.Specs.SolanaInstructionView.InstructionAccount.readonly_signer_model :=
        rfl

theorem create_account_evaluated :
    Solanalib.Specs.SolanaSystemInterface.Capabilities.reference .instruction_create_account
      PUnit.unit =
      returnsOf Solanalib.Specs.SolanaSystemInterface.instruction.create_account_model := rfl

theorem transfer_evaluated :
    Solanalib.Specs.SolanaSystemInterface.Capabilities.reference .instruction_transfer PUnit.unit =
      returnsOf Solanalib.Specs.SolanaSystemInterface.instruction.transfer_model := rfl

/-! ## solana-instruction 3.4.0 `AccountMeta` -/

def metaArgs (j : Json) : Result (Solanalib.Runtime.Pubkey × Bool) := do
  pure (← keyField j "pubkey", ← boolField j "is_signer")

def accountMetaNewChecker : Checker where
  function := "solana_instruction::account_meta::AccountMeta::new"
  generics := []
  reference := "Solanalib.Specs.SolanaInstruction.AccountMeta.new_model"
  decides := ["Solanalib.Specs.SolanaInstruction.AccountMeta.new_model"]
  check := decidePure Solanalib.Specs.SolanaInstruction.AccountMeta.new_model
    (Solanalib.Specs.SolanaInstruction.Capabilities.reference .AccountMeta_new PUnit.unit)
      account_meta_new_evaluated metaArgs metaOf metaJson

def accountMetaNewReadonlyChecker : Checker where
  function := "solana_instruction::account_meta::AccountMeta::new_readonly"
  generics := []
  reference := "Solanalib.Specs.SolanaInstruction.AccountMeta.new_readonly_model"
  decides := ["Solanalib.Specs.SolanaInstruction.AccountMeta.new_readonly_model"]
  check := decidePure Solanalib.Specs.SolanaInstruction.AccountMeta.new_readonly_model
    (Solanalib.Specs.SolanaInstruction.Capabilities.reference .AccountMeta_new_readonly PUnit.unit)
      account_meta_new_readonly_evaluated
    metaArgs metaOf metaJson

/-! ## InstructionView seeds, signers and read-only signer metadata -/

def seedArgs (j : Json) : Result Solanalib.Runtime.Bytes := do asBytes (← field j "bytes")

def seedsArgs (j : Json) : Result (List Seed) := do asList asBytes (← field j "seeds")

def arrayValue {α : Type} (size : Nat) (values : List α) : Result (ArrayValue α) :=
  if h : values.length = size then pure ⟨size, values, h⟩
  else throw s!"array of {values.length} elements recorded at SIZE = {size}"

def seedJson (s : Seed) : Json := bytesJson s
def signerJson (s : Signer) : Json := listJson bytesJson s

def v1SeedFromSliceChecker : Checker where
  function := "<solana_instruction_view::cpi::Seed<'a> as core::convert::From<&'a \
    [u8]>>::from"
  generics := []
  reference := "Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_slice_model"
  decides := ["Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_slice_model"]
  check := decidePure Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_slice_model
    (Solanalib.Specs.SolanaInstructionView.Capabilities.reference .cpi_Seed_from_slice PUnit.unit)
      v1_seed_from_slice_evaluated seedArgs asBytes seedJson

def v1SignerFromSliceChecker : Checker where
  function :=
    "<solana_instruction_view::cpi::Signer<'a, 'b> as core::convert::From<&'b \
      [solana_instruction_view::cpi::Seed<'a>]>>::from"
  generics := []
  reference := "Solanalib.Specs.SolanaInstructionView.cpi.Signer.from_slice_model"
  decides := ["Solanalib.Specs.SolanaInstructionView.cpi.Signer.from_slice_model"]
  check := decidePure Solanalib.Specs.SolanaInstructionView.cpi.Signer.from_slice_model
    (Solanalib.Specs.SolanaInstructionView.Capabilities.reference .cpi_Signer_from_slice
      PUnit.unit) v1_signer_from_slice_evaluated seedsArgs
    (asList asBytes) signerJson

def v2SeedFromSliceChecker : Checker where
  function :=
    "<solana_instruction_view::cpi::Seed<'bytes> as core::convert::From<&'bytes \
      [u8]>>::from"
  generics := []
  reference := "Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_slice_model"
  decides := ["Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_slice_model"]
  check := decidePure Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_slice_model
    (Solanalib.Specs.SolanaInstructionView.Capabilities.reference .cpi_Seed_from_slice PUnit.unit)
      v2_seed_from_slice_evaluated seedArgs asBytes seedJson

/-- `Seed::from(&[u8; SIZE])`, one checker per recorded `SIZE`. -/
def v2SeedFromArrayChecker (size : Nat) : Checker where
  function :=
    "<solana_instruction_view::cpi::Seed<'bytes> as core::convert::From<&'bytes [u8; \
      SIZE]>>::from"
  generics := [("SIZE", toString size)]
  reference := "Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_array_model"
  decides := ["Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_array_model"]
  check := decidePure Solanalib.Specs.SolanaInstructionView.cpi.Seed.from_array_model
    (Solanalib.Specs.SolanaInstructionView.Capabilities.reference .cpi_Seed_from_array PUnit.unit)
      v2_seed_from_array_evaluated
    (fun j => do arrayValue size (← seedArgs j)) asBytes seedJson

/-- `Signer::from(&[Seed; SIZE])`, one checker per recorded `SIZE`. -/
def v2SignerFromArrayChecker (size : Nat) : Checker where
  function :=
    "<solana_instruction_view::cpi::Signer<'bytes, 'seeds> as core::convert::From<&'seeds \
      [solana_instruction_view::cpi::Seed<'bytes>; SIZE]>>::from"
  generics := [("SIZE", toString size)]
  reference := "Solanalib.Specs.SolanaInstructionView.cpi.Signer.from_array_model"
  decides := ["Solanalib.Specs.SolanaInstructionView.cpi.Signer.from_array_model"]
  check := decidePure Solanalib.Specs.SolanaInstructionView.cpi.Signer.from_array_model
    (Solanalib.Specs.SolanaInstructionView.Capabilities.reference .cpi_Signer_from_array
      PUnit.unit) v2_signer_from_array_evaluated
    (fun j => do arrayValue size (← seedsArgs j)) (asList asBytes) signerJson

def readonlySignerChecker : Checker where
  function := "solana_instruction_view::InstructionAccount::<'a>::readonly_signer"
  generics := []
  reference := "Solanalib.Specs.SolanaInstructionView.InstructionAccount.readonly_signer_mo\
    del"
  decides := ["Solanalib.Specs.SolanaInstructionView.InstructionAccount.readonly_signer_mod\
    el"]
  check := decidePure Solanalib.Specs.SolanaInstructionView.InstructionAccount.readonly_signer_model
    (Solanalib.Specs.SolanaInstructionView.Capabilities.reference
      .InstructionAccount_readonly_signer PUnit.unit) readonly_signer_evaluated
    (fun j => keyField j "address") metaOf metaJson

/-! ## solana-system-interface 3.2.0 instruction values -/

def createAccountArgs (j : Json) : Result
  Solanalib.Specs.SolanaSystemInterface.instruction.CreateAccountArgs := do
  pure ⟨← keyField j "from", ← keyField j "to", ← natField j "lamports" 64, ← natField j
    "space" 64,
    ← keyField j "owner"⟩

def transferArgs (j : Json) : Result Solanalib.Specs.SolanaSystemInterface.instruction.TransferArgs
  := do
  pure ⟨← keyField j "from", ← keyField j "to", ← natField j "lamports" 64⟩

def createAccountChecker : Checker where
  function := "solana_system_interface::instruction::create_account"
  generics := []
  reference := "Solanalib.Specs.SolanaSystemInterface.instruction.create_account_model"
  decides := ["Solanalib.Specs.SolanaSystemInterface.instruction.create_account_model"]
  check := decidePure Solanalib.Specs.SolanaSystemInterface.instruction.create_account_model
    (Solanalib.Specs.SolanaSystemInterface.Capabilities.reference .instruction_create_account
      PUnit.unit) create_account_evaluated
    createAccountArgs instructionOf instructionJson

def transferChecker : Checker where
  function := "solana_system_interface::instruction::transfer"
  generics := []
  reference := "Solanalib.Specs.SolanaSystemInterface.instruction.transfer_model"
  decides := ["Solanalib.Specs.SolanaSystemInterface.instruction.transfer_model"]
  check := decidePure Solanalib.Specs.SolanaSystemInterface.instruction.transfer_model
    (Solanalib.Specs.SolanaSystemInterface.Capabilities.reference .instruction_transfer PUnit.unit)
      transfer_evaluated
    transferArgs instructionOf instructionJson

/-! ## pyth-solana-receiver-sdk 2.0.0 price getter -/

namespace PythGetter

open Solanalib.Specs.Core.Oracle

abbrev index : price_update.PriceUpdateV2.GetterIndex :=
  ⟨Unit, false⟩

abbrev Out := Outcome Unit (Except Pyth.GetPriceError Pyth.Price) Pyth.Panic Pyth.Panic

/-- The registered getter at the recorded index is the graph of `Pyth.run false`. -/
theorem getter_evaluated (args : Pyth.Args) (o : Out) :
    price_update.PriceUpdateV2.get_price_no_older_than_with_custom_verification_level_run
        index () args o ↔ Pyth.run false () args = o :=
  eq_comm

def clock (j : Json) : Result Sysvar.Clock := do
  pure ⟨← asUInt 64 (← field j "slot"), ← asSInt 64 (← field j "epoch_start_timestamp"),
    ← asUInt 64 (← field j "epoch"), ← asUInt 64 (← field j "leader_schedule_epoch"),
    ← asSInt 64 (← field j "unix_timestamp")⟩

def args (j : Json) : Result Pyth.Args := do
  pure ⟨← SolanalibTest.Conformance.Library.Pyth.update (← field j "update"), ← clock (← field j
    "clock"),
    ← u64Parse (← field j "maximum_age"), ← keyField j "feed_id",
    ← SolanalibTest.Conformance.Library.Pyth.level (← field j "verification_level")⟩

def price (j : Json) : Result Pyth.Price := do
  pure ⟨← i64Parse (← field j "price"), ← u64Parse (← field j "conf"),
    ← i32Parse (← field j "exponent"), ← i64Parse (← field j "publish_time")⟩

def priceJson (p : Pyth.Price) : Json := Json.mkObj [
  ("price", i64Json p.price), ("conf", u64Json p.confidence), ("exponent", i32Json p.exponent),
  ("publish_time", i64Json p.publishTime)]

def errorName : Pyth.GetPriceError → String
  | .priceTooOld => "PriceTooOld"
  | .invalidWindowSize => "InvalidWindowSize"
  | .mismatchedFeedId => "MismatchedFeedId"
  | .insufficientVerificationLevel => "InsufficientVerificationLevel"
  | .feedIdMustBe32Bytes => "FeedIdMustBe32Bytes"
  | .feedIdNonHexCharacter => "FeedIdNonHexCharacter"

def errors : List Pyth.GetPriceError :=
  [.priceTooOld, .invalidWindowSize, .mismatchedFeedId, .insufficientVerificationLevel,
    .feedIdMustBe32Bytes, .feedIdNonHexCharacter]

def error (j : Json) : Result Pyth.GetPriceError := do
  let name ← j.getStr?
  match errors.find? (errorName · == name) with
  | some e => pure e
  | none => throw s!"unknown GetPriceError {name}"

/-- The text of the unwrapped `TryFromIntError` (`<i64 as TryFrom<u64>>`); no other panic is a
model exit. -/
def conversionPanic : String :=
  "called `Result::unwrap()` on an `Err` value: TryFromIntError(PosOverflow)"

def panicOf (reason : String) : Option Pyth.Panic :=
  if reason = conversionPanic then some .maximumAgeConversion else none

def outJson : Out → Json
  | .returned r () => returnedJson (exceptJson (fun e => Json.str (errorName e)) priceJson r)
    Json.null
  | .unwound .maximumAgeConversion () => Json.mkObj [("exit", "unwound"), ("reason",
    conversionPanic), ("state", Json.null)]
  | .terminated .maximumAgeConversion => Json.mkObj [("exit", "terminated"), ("reason",
    conversionPanic)]

def checker : Checker where
  function :=
    "pyth_solana_receiver_sdk::price_update::PriceUpdateV2::get_price_no_older_than_with_cu\
      stom_verification_level"
  generics := []
  reference :=
    "Solanalib.Specs.PythSolanaReceiverSdk.price_update.PriceUpdateV2.get_price_no_older_th\
      an_with_custom_verification_level_run"
  decides :=
    ["Solanalib.Specs.PythSolanaReceiverSdk.price_update.PriceUpdateV2.get_price_no_older_t\
      han_with_custom_verification_level_run"]
  check := fun c => do
    asUnit c.state
    let a ← args c.args
    let recorded ← parseOutcome (asExcept error price) asUnit panicOf noReason c.outcome
    pure (decideGraph _ (Pyth.run false () a) (getter_evaluated a) recorded outJson)

end PythGetter

end SolanalibTest.Conformance.Library.Families.Instructions
