/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.EntryDeserialize.Common

set_option autoImplicit false
open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.EntryDeserialize

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.EntryDeserialize

def pinState (j : Json) : Result Pinocchio.State := do
  pure ⟨← stateBytes j, ← array nullableNat (← field j "outputs")⟩

def pinStateJson (state : Pinocchio.State) : Json := Json.mkObj [
  ("bytes", bytesJson state.bytes),
  ("outputs", Json.arr (state.outputs.map fun
    | none => Json.null | some offset => natJson offset).toArray)]

/-- The extra getter observations in the corpus must describe the bytes at the actual
returned pointer. They are redundant readback of the input allocation of the registered state,
not a second deserialization reference. -/
def pinInfoValid (bytes : Solanalib.Runtime.Bytes) (offset : Option Nat) (j : Json) : Result Unit
  := do
  let some offset := offset | throw "returned prefix contains an uninitialized AccountInfo"
  unless (← nat (← field j "header_offset")) = offset do
    throw "getter used a different AccountInfo pointer"
  let some (account, _) := account? bytes offset | throw "the getter header is outside the \
    input"
  unless (← byteArray (← field j "key")) = account.key ∧
      (← byteArray (← field j "owner")) = account.owner ∧
      (← nat (← field j "lamports")) = account.lamports.toNat ∧
      (← asBytes (← field j "data")) = account.data ∧
      (← nat (← field j "data_offset")) = account.dataOffset ∧
      (← (← field j "signer").getBool?) = (account.signer != 0) ∧
      (← (← field j "writable").getBool?) = (account.writable != 0) ∧
      (← (← field j "executable").getBool?) = (account.executable != 0) do
    throw "AccountInfo getter observation differs from its physical header"

abbrev PinOutcome := Outcome Pinocchio.State Pinocchio.Result Empty Empty

def pinRecorded (outcome : Json) : Result (Option PinOutcome) := do
  match ← (← field outcome "exit").getStr? with
  | "returned" =>
    regionConsistent (← field outcome "state")
    let after ← pinState (← field outcome "state")
    let result ← field outcome "result"
    let count ← nat (← field result "count")
    let accounts ← (← field result "accounts").getArr?
    unless accounts.size = count ∧ count ≤ after.outputs.length do
      throw "returned initialized prefix has the wrong length"
    unless (← (← field result "allocations").getArr?).isEmpty do
      throw "allocation-free deserializer unexpectedly allocated"
    (after.outputs.take count |>.zip accounts.toList).forM fun (offset, observed) =>
      pinInfoValid after.bytes offset observed
    pure (some (.returned ⟨← views (← field result "views"), count⟩ after))
  | "unwound" | "terminated" => pure none
  | other => throw s!"unknown exit {other}"

def pinComputed (maximum : Nat) (before : Pinocchio.State) : Option PinOutcome :=
  (Pinocchio.execute maximum before).map (fun (result, after) => .returned result after)

theorem pin_graph (maximum : Nat) (before : Pinocchio.State) (outcome : PinOutcome) :
    Solanalib.Specs.Pinocchio.entrypoint.deserialize_run ⟨maximum⟩ before () outcome ↔
      pinComputed maximum before = some outcome := by
  cases outcome with
  | returned result after =>
    change Pinocchio.execute maximum before = some (result, after) ↔ _
    cases computed : Pinocchio.execute maximum before with
    | none => simp [pinComputed, computed]
    | some pair => cases pair; simp [pinComputed, computed]
  | unwound impossible _ | terminated impossible => nomatch impossible

def pinOutcomeJson : PinOutcome → Json
  | .returned result after => returnedJson
    (Json.mkObj [("views", viewsJson result.views), ("count", natJson result.count)])
    (pinStateJson after)
  | .unwound impossible _ | .terminated impossible => nomatch impossible

def pinChecker (maximum : Nat) : Checker where
  function := "pinocchio::entrypoint::deserialize"
  generics := [("MAX_ACCOUNTS", toString maximum)]
  reference := "Solanalib.Specs.Pinocchio.entrypoint.deserialize_run"
  decides := ["Solanalib.Specs.Pinocchio.entrypoint.deserialize_run"]
  decidesRequires := ["Solanalib.Specs.Pinocchio.entrypoint.deserialize_run"]
  check := fun c => do
    let before ← pinState c.state
    unless pinRequires maximum before do
      throw "the input is outside the registered precondition"
    regionConsistent c.state
    let recorded ← pinRecorded c.outcome
    pure (Runtime.decideOptGraph (S := Pinocchio.State)
      (V := Pinocchio.Result) (U := Empty) (T := Empty)
      (Solanalib.Specs.Pinocchio.entrypoint.deserialize_run ⟨maximum⟩ before ())
      (pinComputed maximum before) (pin_graph maximum before) recorded pinOutcomeJson)

end SolanalibTest.Conformance.Library.Families.EntryDeserialize
