/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.ProgramOption
import Solanalib.Specs.SolanaProgramOption.Operations
import Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull
import SolanalibTest.Conformance.Library.Families.SdkValues.Encoding
import Solanalib.Specs.SolanaProgramOption.COption

/-! Each checker decides the registered source relation at a fixed, nontrivial
native callback interpretation. The graph lemmas are checked against that
relation by Lean, and preserve all its return, unwind and terminal branches. -/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.SdkValues.Callbacks

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Values

def map : Checker where
  function := "solana_program_option::COption::<T>::map"
  generics := [("T", "Tracked"), ("U", "u64"), ("F", "closure")]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.map_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.map_run"]
  check := fun c => do
    let before ← state c.state
    let args ← pure (← cOption tracked (← field c.args "option"), ← tracked (← field c.args
      "closure"))
    let mode ← scriptMode (← field c.args "mode")
    pure (decideGraph (S := Script.State) (V := ProgramOption.Value UInt64) (U := String) (T :=
      Nat) (Solanalib.Specs.SolanaProgramOption.COption.map_run (Script.mapIndex mode) before args)
      (Script.map mode before args) (Script.map_graph mode before args)
      (← outcome (cOption u64) c.outcome) (outcomeJson (cOptionJson u64Json)))

def unwrapOr : Checker where
  function := "solana_program_option::COption::<T>::unwrap_or"
  generics := [("T", "Tracked")]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.unwrap_or_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.unwrap_or_run"]
  check := fun c => do
    let before ← state c.state
    let args ← pure (← cOption tracked (← field c.args "option"), ← tracked (← field c.args
      "fallback"))
    pure (decideGraph (S := Script.State) (V := Script.Tracked) (U := String) (T := Nat)
      (Solanalib.Specs.SolanaProgramOption.COption.unwrap_or_run Script.unwrapOrIndex before args)
      (Script.unwrapOr before args) (Script.unwrapOr_graph before args)
      (← outcome tracked c.outcome) (outcomeJson trackedJson))

end SolanalibTest.Conformance.Library.Families.SdkValues.Callbacks

namespace SolanalibTest.Conformance.Library.Families.SdkValues.Callbacks

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Values

def eq : Checker where
  function := "<solana_program_option::COption<T> as core::cmp::PartialEq>::eq"
  generics := [("T", "Tracked")]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.eq_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.eq_run"]
  check := fun c => do
    let before ← state c.state
    let args ← pure (← cOption tracked (← field c.args "left"), ← cOption tracked (← field c.args
      "right"))
    let mode ← scriptMode (← field c.args "mode")
    pure (decideGraph (S := Script.State) (V := Bool) (U := String) (T := Nat)
      (Solanalib.Specs.SolanaProgramOption.COption.eq_run (Script.eqIndex mode) before args)
      (Script.eq mode before args) (Script.eq_graph mode before args)
      (← outcome bool c.outcome) (outcomeJson Json.bool))

def unwrap : Checker where
  function := "solana_program_option::COption::<T>::unwrap"
  generics := [("T", "Tracked")]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.unwrap_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.unwrap_run"]
  check := fun c => do
    let before ← state c.state
    let args ← cOption tracked (← field c.args "option")
    pure (decideGraph (S := Script.State) (V := Script.Tracked) (U := String) (T := Nat)
      (Solanalib.Specs.SolanaProgramOption.COption.unwrap_run Script.unwrapIndex before args)
      (Script.unwrap before args) (Script.unwrap_graph before args)
      (← outcome tracked c.outcome) (outcomeJson trackedJson))

def nullable : Checker where
  function := "solana_nullable::maybe_null::MaybeNull::<T>::get"
  generics := [("T", "Tracked")]
  reference := "Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull.get_run"
  decides := ["Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull.get_run"]
  check := fun c => do
    let before ← state c.state
    let args ← tracked (← field c.args "value")
    let mode ← scriptMode (← field c.args "mode")
    let isNull ← bool (← field c.args "is_null")
    pure (decideGraph (S := Script.State) (V := Option Script.Tracked) (U := String) (T := Nat)
      (Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull.get_run
        (Script.nullableIndex mode isNull) before args)
      (Script.nullable mode isNull before args) (Script.nullable_graph mode isNull before args)
      (← outcome (option tracked) c.outcome) (outcomeJson (optionJson trackedJson)))

end SolanalibTest.Conformance.Library.Families.SdkValues.Callbacks

namespace SolanalibTest.Conformance.Library.Families.SdkValues.Callbacks

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Values

def contains : Checker where
  function := "solana_program::program_option::COption::<T>::contains"
  generics := [("T", "Tracked"), ("U", "Query")]
  reference := "Solanalib.Specs.SolanaProgram.program_option.COption.contains_run"
  decides := ["Solanalib.Specs.SolanaProgram.program_option.COption.contains_run"]
  check := fun c => do
    let before ← state c.state
    let args ← pure (← cOption tracked (← field c.args "option"), ← query (← field c.args
      "query"))
    let mode ← scriptMode (← field c.args "mode")
    pure (decideGraph (S := Script.State) (V := Bool) (U := String) (T := Nat)
      (Solanalib.Specs.SolanaProgram.program_option.COption.contains_run
        (Script.containsIndex mode) before args)
      (Script.containsRun mode before args) (Script.contains_graph mode before args)
      (← outcome bool c.outcome) (outcomeJson Json.bool))

def unwrapOrDefault : Checker where
  function := "solana_program::program_option::COption::<T>::unwrap_or_default"
  generics := [("T", "Tracked")]
  reference := "Solanalib.Specs.SolanaProgram.program_option.COption.unwrap_or_default_run"
  decides := ["Solanalib.Specs.SolanaProgram.program_option.COption.unwrap_or_default_run"]
  check := fun c => do
    let before ← state c.state
    let args ← cOption tracked (← field c.args "option")
    let mode ← scriptMode (← field c.args "mode")
    pure (decideGraph (S := Script.State) (V := Script.Tracked) (U := String) (T := Nat)
      (Solanalib.Specs.SolanaProgram.program_option.COption.unwrap_or_default_run
        (Script.defaultIndex mode) before args)
      (Script.unwrapOrDefault mode before args) (Script.default_graph mode before args)
      (← outcome tracked c.outcome) (outcomeJson trackedJson))

end SolanalibTest.Conformance.Library.Families.SdkValues.Callbacks
