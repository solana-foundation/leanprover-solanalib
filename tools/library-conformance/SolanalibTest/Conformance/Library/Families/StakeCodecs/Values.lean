/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.Capabilities
import SolanalibTest.Conformance.Library.Families.Instructions.Common
import Solanalib.Specs.SolanaAddressLookupTableInterface.Capabilities

set_option autoImplicit false
open Lean (Json toJson)

open Solanalib.Specs.SolanaAddressLookupTableInterface
open Solanalib.Specs.SolanaProgram

namespace SolanalibTest.Conformance.Library.Families.StakeCodecs

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Borsh

def nullable {A : Type} (parse : Json → Result A) (value : Json) : Result (Option A) :=
  match value with
  | .null => pure none
  | other => return some (← parse other)

def nullableJson {A : Type} (render : A → Json) : Option A → Json
  | none => .null
  | some value => render value

def lookupSlice (j : Json) : Result Bytemuck.SliceRef := do
  pure ⟨← (← field j "address").getNat?, ← asBytes (← field j "bytes")⟩

def lookupMeta (j : Json) : Result AddressLookupTable.Meta := do
  pure ⟨← StakeAddress.u64Field j "deactivation_slot", ← StakeAddress.u64Field j
    "last_extended_slot",
    UInt8.ofNat (← asUInt 8 (← field j "last_extended_slot_start_index")),
    ← nullable StakeAddress.pubkey (← field j "authority"), UInt16.ofNat (← asUInt 16 (← field j
      "padding"))⟩

def lookupValue (j : Json) : Result AddressLookupTable.Value := do
  pure ⟨← lookupMeta (← field j "meta"), ← lookupSlice (← field j "addresses")⟩

def lookupError (j : Json) : Result AddressLookupTable.Error := do
  match ← j.getStr? with
  | "InvalidAccountData" => pure .invalidAccountData
  | "UninitializedAccount" => pure .uninitializedAccount
  | other => throw s!"unknown lookup error {other}"

def lookupErrorJson : AddressLookupTable.Error → Json
  | .invalidAccountData => toJson "InvalidAccountData"
  | .uninitializedAccount => toJson "UninitializedAccount"

def lookupJson (value : AddressLookupTable.Value) : Json := Json.mkObj [
  ("meta", Json.mkObj [("deactivation_slot", u64Json value.metadata.deactivationSlot),
    ("last_extended_slot", u64Json value.metadata.lastExtendedSlot),
    ("last_extended_slot_start_index", toJson value.metadata.lastExtendedSlotStartIndex.toNat),
    ("authority", nullableJson StakeAddress.pubkeyJson value.metadata.authority),
    ("padding", toJson value.metadata.padding.toNat)]),
  ("addresses", Json.mkObj [("address", toJson value.addresses.address), ("bytes", bytesJson
    value.addresses.bytes)])]

namespace Lookup

/-- These event lists come from a separate actual call to the pinned bincode
primitive and a separate drop of its returned error, using the native tracking
allocator. They are the chosen dependency index, not the SDK outcome. -/
def decode (events : List String) (before : List String) (bytes : Solanalib.Runtime.Bytes) :
    Outcome (List String) (Except Unit AddressLookupTableOwned.ProgramState) String String :=
  match AddressLookupTableOwned.decodeProgram bytes with
  | some state => .returned (.ok state) (before ++ events)
  | none => .returned (.error ()) (before ++ events)

def index (decodeEvents dropEvents : List String) : AddressLookupTableOwned.Index where
  State := List String
  DecodeError := Unit
  Unwind := String
  Terminal := String
  decode := Callback.ofFunction (decode decodeEvents)
  dropError := Callback.ofFunction fun before _ => .returned () (before ++ dropEvents)
  returns_wire := by
    intro before bytes result after execution
    change decode decodeEvents before bytes = .returned result after at execution
    unfold decode at execution
    split at execution <;> cases execution <;> assumption

def executable (decodeEvents dropEvents : List String) : AddressLookupTableOwned.Executable (index
  decodeEvents dropEvents) where
  decode := decode decodeEvents
  dropError := fun (before : List String) _ => .returned () (before ++ dropEvents)
  decode_eq := rfl
  drop_eq := rfl

def run (decodeEvents dropEvents : List String) :=
  state.AddressLookupTable.deserialize_run
    (index decodeEvents dropEvents)

theorem evaluated (decodeEvents dropEvents : List String) :
    run decodeEvents dropEvents = AddressLookupTableOwned.run (index decodeEvents dropEvents) := rfl

def stateJson (state : List String) : Json := listJson Json.str state

def outcomeJson : Outcome (List String) (Except AddressLookupTable.Error AddressLookupTable.Value)
  String String → Json
  | .returned result state => returnedJson (exceptJson lookupErrorJson lookupJson result)
    (stateJson state)
  | .unwound reason state => Json.mkObj [("exit", "unwound"), ("reason", toJson reason), (
    "state",
    stateJson state)]
  | .terminated reason => Json.mkObj [("exit", "terminated"), ("reason", toJson reason)]

def check (c : Case) : Result Verdict := do
  let input ← lookupSlice c.args
  let before ← asList Json.getStr? c.state
  let probe ← field c.args "codec_probe"
  let decodeEvents ← asList Json.getStr? (← field probe "decode")
  let dropEvents ← asList Json.getStr? (← field probe "drop")
  let decodedOk ← (← field probe "ok").getBool?
  if decodedOk != (AddressLookupTableOwned.decodeProgram input.bytes).isSome then
    throw "actual bincode primitive disagrees with the selected wire decoder"
  if decodedOk && (!decodeEvents.isEmpty || !dropEvents.isEmpty) then
    throw "plain metadata decoding unexpectedly allocated or destroyed an error"
  if !decodedOk && (decodeEvents.isEmpty || dropEvents.isEmpty) then
    throw "bincode failure omitted its owned error allocation or destruction"
  let observed ← parseOutcome (asExcept lookupError lookupValue) (asList Json.getStr?) some some
    c.outcome
  let expected := AddressLookupTableOwned.runFn (index decodeEvents dropEvents)
    (executable decodeEvents dropEvents) before input
  have graph : ∀ outcome, run decodeEvents dropEvents before input outcome ↔ expected = outcome :=
    by
    intro outcome
    rw [evaluated]
    exact AddressLookupTableOwned.run_graph _ _ _ _ _
  letI : DecidableEq (Outcome (index decodeEvents dropEvents).State
      (Except AddressLookupTable.Error AddressLookupTable.Value)
      (index decodeEvents dropEvents).Unwind (index decodeEvents dropEvents).Terminal) :=
    inferInstanceAs (DecidableEq (Outcome (List String)
      (Except AddressLookupTable.Error AddressLookupTable.Value) String String))
  pure (decideGraph _ expected graph observed outcomeJson)

end Lookup

def interfaceLookupChecker : Checker where
  function := "solana_address_lookup_table_interface::state::AddressLookupTable::<'_>::dese\
    rialize"
  generics := []
  reference :=
    "Solanalib.Specs.SolanaAddressLookupTableInterface.state.AddressLookupTable.deserialize\
      _run"
  decides :=
    ["Solanalib.Specs.SolanaAddressLookupTableInterface.state.AddressLookupTable.deserializ\
      e_run"]
  check := Lookup.check

end SolanalibTest.Conformance.Library.Families.StakeCodecs

namespace SolanalibTest.Conformance.Library.Families.StakeCodecs
open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Borsh

namespace Lookup

def runForVersion (modern : Bool) (decodeEvents dropEvents : List String) :=
  if modern then
    state.AddressLookupTable.deserialize_run
    (index decodeEvents dropEvents)
  else address_lookup_table.state.AddressLookupTable.deserialize_run
    (index decodeEvents dropEvents)

theorem evaluatedForVersion (modern : Bool) (decodeEvents dropEvents : List String) :
    runForVersion modern decodeEvents dropEvents = AddressLookupTableOwned.run (index decodeEvents
      dropEvents) := by
  cases modern <;> rfl

def checkForVersion (modern : Bool) (c : Case) : Result Verdict := do
  let input ← lookupSlice c.args
  let before ← asList Json.getStr? c.state
  let probe ← field c.args "codec_probe"
  let decodeEvents ← asList Json.getStr? (← field probe "decode")
  let dropEvents ← asList Json.getStr? (← field probe "drop")
  let decodedOk ← (← field probe "ok").getBool?
  if decodedOk != (AddressLookupTableOwned.decodeProgram input.bytes).isSome then
    throw "actual bincode primitive disagrees with the selected wire decoder"
  if decodedOk && (!decodeEvents.isEmpty || !dropEvents.isEmpty) then
    throw "plain metadata decoding unexpectedly allocated or destroyed an error"
  if !decodedOk && (decodeEvents.isEmpty || dropEvents.isEmpty) then
    throw "bincode failure omitted its owned error allocation or destruction"
  let observed ← parseOutcome (asExcept lookupError lookupValue) (asList Json.getStr?) some some
    c.outcome
  let expected := AddressLookupTableOwned.runFn (index decodeEvents dropEvents)
    (executable decodeEvents dropEvents) before input
  have graph : ∀ outcome, runForVersion modern decodeEvents dropEvents before input outcome ↔
    expected = outcome := by
    intro outcome
    rw [evaluatedForVersion]
    exact AddressLookupTableOwned.run_graph _ _ _ _ _
  letI : DecidableEq (Outcome (index decodeEvents dropEvents).State
      (Except AddressLookupTable.Error AddressLookupTable.Value)
      (index decodeEvents dropEvents).Unwind (index decodeEvents dropEvents).Terminal) :=
    inferInstanceAs (DecidableEq (Outcome (List String)
      (Except AddressLookupTable.Error AddressLookupTable.Value) String String))
  pure (decideGraph _ expected graph observed outcomeJson)

end Lookup

def programLookupChecker : Checker where
  function := "solana_program::address_lookup_table::state::AddressLookupTable::<'_>::deser\
    ialize"
  generics := []
  reference :=
    "Solanalib.Specs.SolanaProgram.address_lookup_table.state.AddressLookupTable.deserializ\
      e_run"
  decides :=
    ["Solanalib.Specs.SolanaProgram.address_lookup_table.state.AddressLookupTable.deseriali\
      ze_run"]
  check := Lookup.checkForVersion false

end SolanalibTest.Conformance.Library.Families.StakeCodecs

namespace SolanalibTest.Conformance.Library.Families.StakeCodecs
open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Borsh

/-- JSON stores the exact legacy variants and binary64 payload bits. -/
def legacyState (j : Json) : Result LegacyStake.State := do
  match ← (← field j "tag").getStr? with
  | "uninitialized" => pure .uninitialized
  | "rewards_pool" => pure .rewardsPool
  | "initialized" => pure (.initialized (← StakeAddress.meta_ (← field j "meta")))
  | "stake" => pure (.stake (← StakeAddress.meta_ (← field j "meta")) (← StakeAddress.stake (←
    field j "stake")))
  | other => throw s!"unknown legacy stake variant {other}"

def lockupJson (l : StakeState.Lockup) : Json := Json.mkObj [
  ("unix_timestamp", i64Json l.unixTimestamp), ("epoch", u64Json l.epoch),
  ("custodian", StakeAddress.pubkeyJson l.custodian)]

def delegationJson (d : StakeState.Delegation) : Json := Json.mkObj [
  ("voter_pubkey", StakeAddress.pubkeyJson d.voterPubkey), ("stake", u64Json d.stake),
  ("activation_epoch", u64Json d.activationEpoch), ("deactivation_epoch", u64Json
    d.deactivationEpoch),
  ("warmup_cooldown_rate", f64BitsJson d.warmupCooldownRate)]

def lockupForceArgs (j : Json) : Result (StakeState.Lockup × LegacyStake.Clock × Option
  Solanalib.Runtime.Pubkey) := do
  let clock ← field j "clock"
  pure ⟨← StakeAddress.lockup (← field j "lockup"),
    ⟨← StakeAddress.i64Field clock "unix_timestamp", ← StakeAddress.u64Field clock "epoch"⟩,
    ← nullable StakeAddress.pubkey (← field j "custodian")⟩

def lockupDefaultChecker : Checker where
  function := "<solana_program::stake::state::Lockup as core::default::Default>::default"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.stake.state.Lockup.default_run"
  decides := ["Solanalib.Specs.SolanaProgram.stake.state.Lockup.default_run"]
  check := Instructions.decidePure stake.state.Lockup.default_run
    (Capabilities.reference .stake_state_Lockup_default PUnit.unit)
      rfl
    asUnit StakeAddress.lockup lockupJson

def lockupForceChecker : Checker where
  function := "solana_program::stake::state::Lockup::is_in_force"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.stake.state.Lockup.is_in_force_run"
  decides := ["Solanalib.Specs.SolanaProgram.stake.state.Lockup.is_in_force_run"]
  check := Instructions.decidePure stake.state.Lockup.is_in_force_run
    (Capabilities.reference .stake_state_Lockup_is_in_force
      PUnit.unit) rfl
    lockupForceArgs Json.getBool? toJson

def delegationChecker : Checker where
  function := "solana_program::stake::state::StakeState::delegation"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.stake.state.StakeState.delegation_run"
  decides := ["Solanalib.Specs.SolanaProgram.stake.state.StakeState.delegation_run"]
  check := Instructions.decidePure
    stake.state.StakeState.delegation_run
    (Capabilities.reference .stake_state_StakeState_delegation
      PUnit.unit) rfl
    legacyState (nullable StakeAddress.delegation) (nullableJson delegationJson)

def lockupChecker : Checker where
  function := "solana_program::stake::state::StakeState::lockup"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.stake.state.StakeState.lockup_run"
  decides := ["Solanalib.Specs.SolanaProgram.stake.state.StakeState.lockup_run"]
  check := Instructions.decidePure stake.state.StakeState.lockup_run
    (Capabilities.reference .stake_state_StakeState_lockup
      PUnit.unit) rfl
    legacyState (nullable StakeAddress.lockup) (nullableJson lockupJson)

def metadataChecker : Checker where
  function := "solana_program::stake::state::StakeState::meta"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.stake.state.StakeState.meta_run"
  decides := ["Solanalib.Specs.SolanaProgram.stake.state.StakeState.meta_run"]
  check := Instructions.decidePure stake.state.StakeState.meta_run
    (Capabilities.reference .stake_state_StakeState_meta PUnit.unit)
      rfl
    legacyState (nullable StakeAddress.meta_) (nullableJson StakeAddress.metaJson)

end SolanalibTest.Conformance.Library.Families.StakeCodecs
