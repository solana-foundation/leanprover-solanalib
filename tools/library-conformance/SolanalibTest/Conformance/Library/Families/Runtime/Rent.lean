/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Common
import Solanalib.Specs.SolanaRent.Rent
import Solanalib.Specs.Pinocchio.Rent

/-!
# Rent arithmetic: solana-rent 3.0.0, pinocchio 0.10.2 and 0.11.1

The arithmetic profile (overflow checks, panic strategy, BPF target) is the state of the
record: it is a property of the recorded build, constant during the
call. `minimum_balance_run` and the `try_minimum_balance_run` of pinocchio 0.10.2
are registered as `Callback.ofFunction` of the outcome functions, so their
graph lemmas hold by `Iff.rfl`; the `try_minimum_balance` of pinocchio 0.11.1 is
registered as a total function and decided as `returnsOf` of it (`rfl`).
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Runtime.Rent

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Sysvar
open SolanalibTest.Conformance.Library.Families.Runtime

/-! ## solana-rent 3.0.0 -/

def rent300 (j : Json) : Result Rent300 := do
  pure ⟨← u64 (← field j "lamports_per_byte_year"), ← asF64Bits (← field j "exemption_thres\
    hold"),
    ← u8 (← field j "burn_percent")⟩

theorem minimum_balance_evaluated (before : ArithmeticProfile) (args : Rent300 × UInt64)
    (o : Outcome ArithmeticProfile UInt64 Panic Panic) :
    Solanalib.Specs.SolanaRent.Rent.minimum_balance_run before args o ↔
      Solanalib.Specs.SolanaRent.Rent.minimum_balance before args = o := Iff.rfl

def minimumBalance : Checker where
  function := "solana_rent::Rent::minimum_balance"
  generics := []
  reference := "Solanalib.Specs.SolanaRent.Rent.minimum_balance_run"
  decides := ["Solanalib.Specs.SolanaRent.Rent.minimum_balance_run"]
  check := fun c => do
    let before ← arithmeticProfile c.state
    let args := (← rent300 (← field c.args "rent"), ← u64 (← field c.args "data_len"))
    let recorded ← parseOutcome u64 arithmeticProfile panicReason panicReason c.outcome
    return decideGraph (Solanalib.Specs.SolanaRent.Rent.minimum_balance_run before args)
      (Solanalib.Specs.SolanaRent.Rent.minimum_balance before args) (minimum_balance_evaluated
        before args)
      recorded (outcomeJson arithmeticProfileJson u64Json panicJson panicJson)

/-! ## pinocchio 0.10.2 -/

def pinocchioProfile (j : Json) : Result PinocchioProfile := do
  pure ⟨← arithmeticProfile j, ← bool (← field j "target_bpf")⟩

def pinocchioProfileJson (p : PinocchioProfile) : Json :=
  Json.mkObj (arithmeticProfileFields p.arithmetic ++ [("target_bpf", Json.bool p.targetBpf)])

def rent102 (j : Json) : Result Rent102 := do
  pure ⟨← u64 (← field j "lamports_per_byte"), ← asF64Bits (← field j "exemption_threshold")⟩

def resultJson : Except ProgramError.Value UInt64 → Json := exceptJson programErrorJson u64Json

theorem try_minimum_balance_102_evaluated (before : PinocchioProfile) (args : Rent102 × UInt64)
    (o : Outcome PinocchioProfile (Except ProgramError.Value UInt64) Panic Panic) :
    Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate.try_minimum_balance_run before args
      o ↔
      Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate.try_minimum_balance before args =
        o := Iff.rfl

def tryMinimumBalance102 : Checker where
  function := "pinocchio::sysvars::rent::Rent::try_minimum_balance"
  generics := []
  reference := "Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate.try_minimum_bala\
    nce_run"
  decides := ["Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate.try_minimum_balan\
    ce_run"]
  check := fun c => do
    let before ← pinocchioProfile c.state
    let args := (← rent102 (← field c.args "rent"), ← u64 (← field c.args "data_len"))
    let recorded ← parseOutcome (asExcept programError u64) pinocchioProfile panicReason panicReason
      c.outcome
    return decideGraph
      (Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate.try_minimum_balance_run before
      args)
      (Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate.try_minimum_balance before args)
      (try_minimum_balance_102_evaluated before args) recorded
      (outcomeJson pinocchioProfileJson resultJson panicJson panicJson)

/-! ## pinocchio 0.11.1 -/

def rent111 (j : Json) : Result Rent111 := do pure ⟨← u64 (← field j "lamports_per_byte")⟩

def tryMinimumBalance111 : Checker where
  function := "pinocchio::sysvars::rent::Rent::try_minimum_balance"
  generics := []
  reference := "Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate.try_minimum_balance"
  decides := ["Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate.try_minimum_balance"]
  check := fun c => do
    asUnit c.state
    let args := (← rent111 (← field c.args "rent"), ← u64 (← field c.args "data_len"))
    decideReturns (returnsOf
      Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate.try_minimum_balance)
      Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate.try_minimum_balance rfl () args
      (asExcept programError u64) asUnit resultJson (fun _ => Json.null) c.outcome

end SolanalibTest.Conformance.Library.Families.Runtime.Rent
