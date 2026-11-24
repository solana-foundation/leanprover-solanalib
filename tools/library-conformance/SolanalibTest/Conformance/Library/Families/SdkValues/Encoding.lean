/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Values
import SolanalibTest.Conformance.Library.Families.SdkValues.Script

/-! JSON codecs for the native SDK value observations. Process exits retain the
complete wait status; a double panic cannot match a scripted ordinary exit. -/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.SdkValues

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime

def option {T : Type} (payload : Json → Result T) : Json → Result (Option T)
  | .null => pure none
  | value => do pure (some (← payload (← field value "some")))

def optionJson {T : Type} (payload : T → Json) : Option T → Json
  | none => .null
  | some value => Json.mkObj [("some", payload value)]

def cOptionJson {T : Type} (payload : T → Json) : ProgramOption.Value T → Json
  | .none => .null
  | .some value => Json.mkObj [("some", payload value)]

def scriptMode (j : Json) : Result Nat := do
  let mode ← j.getNat?
  if mode ≤ 2 then pure mode else throw "SDK callback mode must be 0, 1 or 2"

def state (j : Json) : Result Script.State := do
  let events ← (← (← field j "events").getArr?).toList.mapM Json.getStr?
  let live ← (← (← field j "live").getArr?).toList.mapM (asUInt 64)
  pure ⟨events, live⟩

def stateJson (state : Script.State) : Json :=
  Json.mkObj [("events", toJson state.events), ("live", toJson state.live)]

def tracked (j : Json) : Result Script.Tracked := do
  pure ⟨← asUInt 64 (← field j "id"), ← u64 (← field j "value"),
    ← scriptMode (← field j "drop_mode")⟩

def trackedJson (value : Script.Tracked) : Json :=
  Json.mkObj [("id", toJson value.id), ("value", u64Json value.value),
    ("drop_mode", toJson value.dropMode)]

def query (j : Json) : Result Script.Query := do
  pure ⟨← asUInt 64 (← field j "id"), ← u64 (← field j "value")⟩

/-- Every terminal reason is an actual process wait status from the child.
Unknown terminal representations are rejected, including altered reason text. -/
def outcome {T : Type} (value : Json → Result T) (j : Json) :
    Result (Option (Script.Exit T)) := do
  match ← (← field j "exit").getStr? with
  | "returned" => pure (some (.returned (← value (← field j "result")) (← state (← field j
    "state"))))
  | "unwound" => pure (some (.unwound (← (← field j "reason").getStr?) (← state (← field j
    "state"))))
  | "terminated" =>
    if (← (← field j "reason").getStr?) != "process" then pure none
    else pure (some (.terminated (← (← field (← field j "detail") "status").getNat?)))
  | other => throw s!"unknown SDK exit {other}"

def outcomeJson {T : Type} (value : T → Json) : Script.Exit T → Json
  | .returned result after => returnedJson (value result) (stateJson after)
  | .unwound reason after =>
      Json.mkObj [("exit", "unwound"), ("reason", Json.str reason), ("state", stateJson after)]
  | .terminated status => Json.mkObj [("exit", "terminated"), ("reason", "process"),
      ("detail", Json.mkObj [("status", toJson status)])]

end SolanalibTest.Conformance.Library.Families.SdkValues
