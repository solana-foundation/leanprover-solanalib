/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.SdkValues.KeyEquality
import Solanalib.Specs.SolanaProgramOption.Operations
import SolanalibTest.Conformance.Library.Families.SdkValues.Values

/-! Additional exact native payload providers. The reference result records
both its original parent identity and all key bytes. The map provider is only the comparison of the
driver of two shared keys; general callbacks retain their
separate stateful interpretation. None.unwrap observes the real Linux child
wait status under the pinned panic-abort profile of the driver. -/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.SdkValues.Keys

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Values

def parent (j : Json) : Result (Nat × Solanalib.Runtime.Pubkey) := do
  pure (← (← field j "parent").getNat?, ← pubkey (← field j "key"))

def parentJson (value : Nat × Solanalib.Runtime.Pubkey) : Json :=
  Json.mkObj [("parent", toJson value.1), ("key", pubkeyJson value.2)]

def asRef : Checker where
  function := "solana_program_option::COption::<T>::as_ref"
  generics := [("T", "solana-pubkey@2.4.0::Pubkey")]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.as_ref_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.as_ref_run"]
  check := fun c => do
    unitState c
    let args ← pure (← parent c.args, ← bool (← field c.args "present"))
    decideReturns (State := Unit) (Args := (Nat × Solanalib.Runtime.Pubkey) × Bool)
      (Value := ProgramOption.Value (FieldReference (Nat × Solanalib.Runtime.Pubkey) Unit))
      (Solanalib.Specs.SolanaProgramOption.COption.as_ref_run (Nat × Solanalib.Runtime.Pubkey))
      (fun before args => (ProgramOption.asRef args.1 args.2, before)) rfl () args
      (cOption fun j => do pure (⟨← parent j, ()⟩ : FieldReference (Nat × Solanalib.Runtime.Pubkey)
        Unit))
      asUnit (cOptionJson fun value => parentJson value.parent) (fun _ => Json.null) c.outcome

def isNone : Checker where
  function := "solana_program_option::COption::<T>::is_none"
  generics := [("T", "solana-pubkey@2.4.0::Pubkey")]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.is_none_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.is_none_run"]
  check := fun c => do
    unitState c
    decideReturns (State := Unit) (Args := ProgramOption.Value Solanalib.Runtime.Pubkey) (Value :=
      Bool)
      (Solanalib.Specs.SolanaProgramOption.COption.is_none_run Solanalib.Runtime.Pubkey)
      (fun before value => (ProgramOption.isNone value, before)) rfl
      () (← cOption pubkey (← field c.args "option"))
      bool asUnit Json.bool (fun _ => Json.null) c.outcome

/-- This fixed native closure compares the complete shared keys and has no
state or destructor effect. This is an interpretation of the assumed callback
interface, not a proof of an application closure. -/
def mapIndex : ProgramOption.MapIndex where
  State := Unit
  T := Solanalib.Runtime.Pubkey
  U := Bool
  Closure := Solanalib.Runtime.Pubkey
  Unwind := Empty
  Terminal := Empty
  call := Callback.ofFunction fun before args => .returned (decide (args.2 = args.1)) before
  dropClosure := Callback.ofFunction fun before _ => .returned () before

def mapValue (value : ProgramOption.Value Solanalib.Runtime.Pubkey) (query :
  Solanalib.Runtime.Pubkey) :
    ProgramOption.Value Bool :=
  match value with
  | .none => .none
  | .some value => .some (decide (value = query))

theorem map_graph (before : Unit) (value : ProgramOption.Value Solanalib.Runtime.Pubkey)
    (query : Solanalib.Runtime.Pubkey) (outcome : Outcome Unit (ProgramOption.Value Bool) Empty
      Empty) :
    Solanalib.Specs.SolanaProgramOption.COption.map_run mapIndex before (value, query) outcome ↔
      .returned (mapValue value query) before = outcome := by
  cases value <;> simp [Solanalib.Specs.SolanaProgramOption.COption.map_run, ProgramOption.mapRun,
    mapIndex, mapValue, Callback.map, Callback.ofFunction, Outcome.map]

def map : Checker where
  function := "solana_program_option::COption::<T>::map"
  generics := [("T", "&solana-pubkey@2.4.0::Pubkey"), ("U", "bool"), ("F", "closure(&Pubkey\
    )")]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.map_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.map_run"]
  check := fun c => do
    unitState c
    let value ← cOption pubkey (← field c.args "option")
    let query ← pubkey (← field c.args "query")
    pure (decideGraph (S := Unit) (V := ProgramOption.Value Bool) (U := Empty) (T := Empty)
      (Solanalib.Specs.SolanaProgramOption.COption.map_run mapIndex () (value, query))
      (.returned (mapValue value query) ()) (map_graph () value query)
      (← parseOutcome (cOption bool) asUnit noReason noReason c.outcome)
      (fun outcome => match outcome with
        | .returned value _ => returnedJson (cOptionJson Json.bool value) Json.null
        | .unwound impossible _ | .terminated impossible => nomatch impossible))

end SolanalibTest.Conformance.Library.Families.SdkValues.Keys

namespace SolanalibTest.Conformance.Library.Families.SdkValues.Keys

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Values

def eq : Checker where
  function := "<solana_program_option::COption<T> as core::cmp::PartialEq>::eq"
  generics := [("T", "solana-address@2.6.1::Address")]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.eq_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.eq_run"]
  check := fun c => do
    unitState c
    let left ← cOption pubkey (← field c.args "left")
    let right ← cOption pubkey (← field c.args "right")
    pure (decideGraph (S := Unit) (V := Bool) (U := Empty) (T := Empty)
      (Solanalib.Specs.SolanaProgramOption.COption.eq_run KeyEquality.keyEqIndex () (left, right))
      (.returned (KeyEquality.keyEq left right) ())
      (fun outcome => (KeyEquality.keyEq_graph () left right outcome).trans eq_comm)
      (← parseOutcome bool asUnit noReason noReason c.outcome)
      (fun outcome => match outcome with
        | .returned value _ => returnedJson (Json.bool value) Json.null
        | .unwound impossible _ | .terminated impossible => nomatch impossible))

/-- The SIGABRT wait status of the pinned Linux runtime includes its core-dump bit
even with the recorded zero core-file limit. The source panic
still receives the exact unwrap diagnostic; this native provider observes its
terminal process status, with no fabricated post-state. -/
def unwrapIndex : ProgramOption.UnwrapIndex where
  State := Unit
  T := Solanalib.Runtime.Pubkey
  Unwind := Empty
  Terminal := Nat
  panic := Callback.ofFunction fun _ _ => .terminated 134

def unwrapValue (value : ProgramOption.Value Solanalib.Runtime.Pubkey) : Outcome Unit
  Solanalib.Runtime.Pubkey Empty Nat :=
  match value with
  | .some value => .returned value ()
  | .none => .terminated 134

theorem unwrap_graph (value : ProgramOption.Value Solanalib.Runtime.Pubkey)
    (outcome : Outcome Unit Solanalib.Runtime.Pubkey Empty Nat) :
    Solanalib.Specs.SolanaProgramOption.COption.unwrap_run unwrapIndex () value outcome ↔
      unwrapValue value = outcome := by
  cases value <;> simp [Solanalib.Specs.SolanaProgramOption.COption.unwrap_run,
    ProgramOption.unwrapRun,
    unwrapIndex, unwrapValue, Callback.map, Callback.ofFunction, Outcome.map, eq_comm]

def unwrapOutcome (j : Json) : Result (Option (Outcome Unit Solanalib.Runtime.Pubkey Empty Nat)) :=
  do
  if (← (← field j "exit").getStr?) == "terminated" then
    if (← (← field j "reason").getStr?) != "process" then pure none
    else pure (some (.terminated (← (← field (← field j "detail") "status").getNat?)))
  else parseOutcome pubkey asUnit noReason noReason j

def unwrapOutcomeJson : Outcome Unit Solanalib.Runtime.Pubkey Empty Nat → Json
  | .returned value _ => returnedJson (pubkeyJson value) Json.null
  | .unwound impossible _ => nomatch impossible
  | .terminated status => Json.mkObj [("exit", "terminated"), ("reason", "process"),
      ("detail", Json.mkObj [("status", toJson status)])]

def unwrap : Checker where
  function := "solana_program_option::COption::<T>::unwrap"
  generics := [("T", "solana-address@2.6.1::Address")]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.unwrap_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.unwrap_run"]
  check := fun c => do
    unitState c
    let value ← cOption pubkey (← field c.args "option")
    pure (decideGraph (S := Unit) (V := Solanalib.Runtime.Pubkey) (U := Empty) (T := Nat)
      (Solanalib.Specs.SolanaProgramOption.COption.unwrap_run unwrapIndex () value)
      (unwrapValue value) (unwrap_graph value) (← unwrapOutcome c.outcome) unwrapOutcomeJson)

end SolanalibTest.Conformance.Library.Families.SdkValues.Keys
