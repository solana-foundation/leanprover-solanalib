/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.Rent
import Solanalib.Specs.SolanaProgram.Hash
import Solanalib.Specs.SolanaEpochSchedule.EpochSchedule
import Solanalib.Specs.SolanaProgram.EpochSchedule
import SolanalibTest.Conformance.Library.Families.Runtime.Rent
import SolanalibTest.Conformance.Library.Families.Runtime.Values
import Solanalib.Specs.SolanaRent.RentExempt

set_option autoImplicit false

open Lean (Json toJson)

open Solanalib.Specs.SolanaProgram

namespace SolanalibTest.Conformance.Library.Families.Utilities.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime

/-- The same complete rent model is used only at separately reviewed exact APIs. -/
def isExempt (function : String) : Checker where
  function := function
  generics := []
  reference := "Solanalib.Specs.SolanaRent.Rent.is_exempt_run"
  decides := ["Solanalib.Specs.SolanaRent.Rent.is_exempt_run"]
  check := fun c => do
    let before ← arithmeticProfile c.state
    let args := (← Rent.rent300 (← field c.args "rent"),
      ← u64 (← field c.args "balance"), ← u64 (← field c.args "data_len"))
    let recorded ← parseOutcome bool arithmeticProfile panicReason panicReason c.outcome
    return decideGraph (Solanalib.Specs.SolanaRent.Rent.is_exempt_run before args)
      (Solanalib.Specs.SolanaRent.Rent.is_exempt before args) (fun _ => Iff.rfl) recorded
      (outcomeJson arithmeticProfileJson Json.bool panicJson panicJson)


def programIsExempt (function : String) : Checker where
  function := function
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.rent.Rent.is_exempt_run"
  decides := ["Solanalib.Specs.SolanaProgram.rent.Rent.is_exempt_run"]
  check := fun c => do
    let before ← arithmeticProfile c.state
    let args := (← Rent.rent300 (← field c.args "rent"),
      ← u64 (← field c.args "balance"), ← u64 (← field c.args "data_len"))
    let recorded ← parseOutcome bool arithmeticProfile panicReason panicReason c.outcome
    return decideGraph (rent.Rent.is_exempt_run before args)
      (rent.Rent.is_exempt before args) (fun _ => Iff.rfl) recorded
      (outcomeJson arithmeticProfileJson Json.bool panicJson panicJson)

end SolanalibTest.Conformance.Library.Families.Utilities.Values

namespace SolanalibTest.Conformance.Library.Families.Utilities.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime

def legacyMinimum : Checker where
  function := "solana_program::rent::Rent::minimum_balance"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.rent.Rent.minimum_balance_run"
  decides := ["Solanalib.Specs.SolanaProgram.rent.Rent.minimum_balance_run"]
  check := fun c => do
    let before ← arithmeticProfile c.state
    let args := (← Rent.rent300 (← field c.args "rent"), ← u64 (← field c.args "data_len"))
    let recorded ← parseOutcome u64 arithmeticProfile panicReason panicReason c.outcome
    return decideGraph (rent.Rent.minimum_balance_run before args)
      (rent.Rent.minimum_balance before args) (fun _ => Iff.rfl)
      recorded (outcomeJson arithmeticProfileJson u64Json panicJson panicJson)

def epochValue (j : Json) : Result EpochSchedule.Value := do
  pure ⟨← u64 (← field j "slots_per_epoch"), ← u64 (← field j "leader_schedule_slot_offset"),
    ← bool (← field j "warmup"), ← u64 (← field j "first_normal_epoch"),
    ← u64 (← field j "first_normal_slot")⟩

def epochJson (v : EpochSchedule.Value) : Json := Json.mkObj [
  ("slots_per_epoch", u64Json v.slotsPerEpoch),
  ("leader_schedule_slot_offset", u64Json v.leaderScheduleSlotOffset),
  ("warmup", Json.bool v.warmup), ("first_normal_epoch", u64Json v.firstNormalEpoch),
  ("first_normal_slot", u64Json v.firstNormalSlot)]

def firstSlot : Checker where
  function := "solana_epoch_schedule::EpochSchedule::get_first_slot_in_epoch"
  generics := []
  reference := "Solanalib.Specs.SolanaEpochSchedule.EpochSchedule.get_first_slot_in_epoch_r\
    un"
  decides := ["Solanalib.Specs.SolanaEpochSchedule.EpochSchedule.get_first_slot_in_epoch_ru\
    n"]
  check := fun c => do
    asUnit c.state
    let args := (← epochValue (← field c.args "schedule"), ← u64 (← field c.args "epoch"))
    decideReturns (returnsOf
      Solanalib.Specs.SolanaEpochSchedule.EpochSchedule.get_first_slot_in_epoch_run)
      Solanalib.Specs.SolanaEpochSchedule.EpochSchedule.get_first_slot_in_epoch_run rfl () args
      u64 asUnit u64Json (fun _ => Json.null) c.outcome

end SolanalibTest.Conformance.Library.Families.Utilities.Values

namespace SolanalibTest.Conformance.Library.Families.Utilities.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime

def legacyToBytes : Checker where
  function := "solana_program::hash::Hash::to_bytes"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.hash.Hash.to_bytes_run"
  decides := ["Solanalib.Specs.SolanaProgram.hash.Hash.to_bytes_run"]
  check := fun c => do
    asUnit c.state
    decideReturns (returnsOf hash.Hash.to_bytes_run)
      hash.Hash.to_bytes_run rfl () (← Runtime.Values.hashValue
        c.args)
      Runtime.Values.array32 asUnit (fun a => bytesJson a.val) (fun _ => Json.null) c.outcome

end SolanalibTest.Conformance.Library.Families.Utilities.Values

namespace SolanalibTest.Conformance.Library.Families.Utilities.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime

def lastSlot : Checker where
  function := "solana_program::epoch_schedule::EpochSchedule::get_last_slot_in_epoch"
  generics := []
  reference :=
    "Solanalib.Specs.SolanaProgram.epoch_schedule.EpochSchedule.get_last_slot_in_epoch_run"
  decides :=
    ["Solanalib.Specs.SolanaProgram.epoch_schedule.EpochSchedule.get_last_slot_in_epoch_run"]
  check := fun c => do
    asUnit c.state
    let args := (← epochValue (← field c.args "schedule"), ← u64 (← field c.args "epoch"))
    decideReturns (returnsOf
      epoch_schedule.EpochSchedule.get_last_slot_in_epoch_run)
      epoch_schedule.EpochSchedule.get_last_slot_in_epoch_run rfl ()
        args
      u64 asUnit u64Json (fun _ => Json.null) c.outcome

end SolanalibTest.Conformance.Library.Families.Utilities.Values
