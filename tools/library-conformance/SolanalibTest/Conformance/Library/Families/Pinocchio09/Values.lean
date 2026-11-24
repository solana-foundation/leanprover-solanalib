/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Pinocchio09.Common
import SolanalibTest.Conformance.Library.Families.Runtime.Syscalls
import Solanalib.Specs.Pinocchio.Instruction
import Solanalib.Specs.Pinocchio.Pubkey
import Solanalib.Specs.Pinocchio.Get

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.Pinocchio09.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AccountsV1
open Instruction.Borrowed

def metaChecker (name : String) (writable signer : Bool)
    (relation : FamilyRun (metaFamily writable signer))
    (evaluated : relation = metaRun writable signer) : Checker where
  function := "pinocchio::instruction::AccountMeta::<'a>::" ++ name
  generics := []
  reference := "Solanalib.Specs.Pinocchio.instruction.AccountMeta." ++ name ++ "_run"
  decides := ["Solanalib.Specs.Pinocchio.instruction.AccountMeta." ++ name ++ "_run"]
  check := fun c => do
    asUnit c.state
    let reference ← natField c.args "reference"
    let key ← pubkeyOf (← field c.args "key")
    let render : Instruction.RefMeta Nat → Unit → Json := fun value _ =>
      Json.mkObj [("reference", toJson value.address), ("key", pubkeyJson key),
        ("is_signer", toJson value.isSigner), ("is_writable", toJson value.isWritable)]
    let run : Unit → Nat → Instruction.RefMeta Nat × Unit := fun before ref => (⟨ref, signer,
      writable⟩, before)
    return observe (relation Nat () reference) (some (.returned ⟨reference, signer, writable⟩ ()))
      (fun outcome => by rw [evaluated]; exact returnsOf_graph run () reference outcome)
      (returnJson render (fun _ => Json.null)) c.outcome

def metas : List Checker := [
  metaChecker "readonly" false false Solanalib.Specs.Pinocchio.instruction.AccountMeta.readonly_run
    rfl,
  metaChecker "readonly_signer" false true
    Solanalib.Specs.Pinocchio.instruction.AccountMeta.readonly_signer_run rfl,
  metaChecker "writable" true false Solanalib.Specs.Pinocchio.instruction.AccountMeta.writable_run
    rfl,
  metaChecker "writable_signer" true true
    Solanalib.Specs.Pinocchio.instruction.AccountMeta.writable_signer_run rfl
]

def seed (size : Nat) : Checker where
  function := "<pinocchio::instruction::Seed<'a> as core::convert::From<&'a [u8; \
    SIZE]>>::from"
  generics := [("SIZE", toString size)]
  reference := "Solanalib.Specs.Pinocchio.instruction.Seed.from_array_run"
  decides := ["Solanalib.Specs.Pinocchio.instruction.Seed.from_array_run"]
  check := fun c => do
    asUnit c.state
    let reference ← natField c.args "reference"
    let bytes ← asBytes (← field c.args "bytes")
    unless (← natField c.args "size") = size ∧ bytes.length = size do
      throw "array size differs from its const argument"
    let index : SeedIndex := ⟨Nat, size⟩
    let run : Unit → Nat → SeedRef Nat × Unit := fun before ref => (⟨ref, size⟩, before)
    let render : SeedRef Nat → Unit → Json := fun value _ =>
      Json.mkObj [("reference", toJson value.source), ("length", toJson value.length),
        ("bytes", bytesJson bytes)]
    return observe (Solanalib.Specs.Pinocchio.instruction.Seed.from_array_run index () reference)
      (some (.returned ⟨reference, size⟩ ())) (returnsOf_graph run () reference)
      (returnJson render (fun _ => Json.null)) c.outcome

def equal : Checker where
  function := "pinocchio::pubkey::pubkey_eq"
  generics := []
  reference := "Solanalib.Specs.Pinocchio.pubkey.pubkey_eq_run"
  decides := ["Solanalib.Specs.Pinocchio.pubkey.pubkey_eq_run"]
  check := fun c => do
    asUnit c.state
    let args := (← pubkeyOf (← field c.args "left"), ← pubkeyOf (← field c.args "right"))
    let expected := Solanalib.Specs.Pinocchio.pubkey.pubkey_eq_run () args
    return observe (returnsOf Solanalib.Specs.Pinocchio.pubkey.pubkey_eq_run () args)
      (some (.returned expected.1 expected.2 : Outcome Unit Bool Empty Empty))
      (returnsOf_graph Solanalib.Specs.Pinocchio.pubkey.pubkey_eq_run () args)
      (returnJson (fun value _ => toJson value) (fun _ => Json.null)) c.outcome

open SolanalibTest.Conformance.Library.Families.Runtime
  SolanalibTest.Conformance.Library.Families.Runtime.Syscalls

def clockChecker : Checker :=
  getterChecker "<pinocchio::sysvars::clock::Clock as pinocchio::sysvars::Sysvar>::get"
    "Solanalib.Specs.Pinocchio.sysvars.clock.Clock.get_dedicated_run"
      Solanalib.Specs.Pinocchio.sysvars.clock.Clock.dedicatedConfig
    Solanalib.Specs.Pinocchio.sysvars.clock.Clock.get_dedicated_run rfl
    (fun before => @decide
      ((Solanalib.Specs.Pinocchio.sysvars.clock.Clock.get_dedicated_contract.contract (getterIndex
      clockLayout)).requires before ())
      (getterReadyDec Solanalib.Specs.Pinocchio.sysvars.clock.Clock.dedicatedConfig .solana
        (readStep clockLayout) before))
    clockLayout SolanalibTest.Conformance.Library.Families.Runtime.Syscalls.clock clockJson

def checkers : List Checker := metas ++ [0, 1, 2, 9, 32, 64].map seed ++ [equal, clockChecker]

end SolanalibTest.Conformance.Library.Families.Pinocchio09.Values
