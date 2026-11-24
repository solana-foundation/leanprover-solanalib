/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AccountsV1.Common
import SolanalibTest.Conformance.Library.Families.AccountsV1.Requires
import SolanalibTest.Conformance.Library.Families.Runtime.Common
import Solanalib.Specs.Core.PinocchioGuard

/-!
Native observations retain the loader allocation in full, including the spare
bytes and padding. Only guard generations and the hidden lease after an
unwinding map are ghost observations. A checker compares the projection of an
outcome admitted by the registered reference; the executable graph lemma is
what makes that existential decidable.
-/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.Pinocchio09

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.PinocchioAccount
open AccountsV1

def put (object : Json) (key : String) (value : Json) : Json :=
  match object with
  | .obj fields => Json.mkObj ((fields.toList.filter (fun entry => entry.1 != key)) ++ [(key,
    value)])
  | _ => Json.mkObj [(key, value)]

def puts (object : Json) (fields : List (String × Json)) : Json :=
  fields.foldl (fun out entry => put out entry.1 entry.2) object

def arrayJson (values : List Json) : Json := .arr values.toArray

def stringList (j : Json) : Result (List String) := do
  (← j.getArr?).toList.mapM Json.getStr?

structure Aux where
  events : List String
  syscalls : Json

def auxOf (j : Json) : Result Aux := do
  let calls ← field j "syscalls"
  let _ ← (← field calls "replies").getArr?
  let _ ← (← field calls "log").getArr?
  return ⟨← stringList (← field j "events"), calls⟩

def Aux.empty : Aux := ⟨[], Json.mkObj [("replies", arrayJson []), ("log", arrayJson [])]⟩

def Aux.record (aux : Aux) (request : Json) : Aux :=
  let prior := (aux.syscalls.getObjValAs? (Array Json) "log").toOption.getD #[]
  { aux with syscalls := put aux.syscalls "log" (arrayJson (prior.toList ++ [request])) }

def Aux.event (aux : Aux) (event : String) : Aux := { aux with events := aux.events ++ [event] }

def withAux (j : Json) (aux : Aux) : Json :=
  puts j [("events", toJson aux.events), ("syscalls", aux.syscalls)]

def outcomeJson {S V : Type} (value : V → Json) (state : S → Json) :
    Outcome S V String Json → Json
  | .returned v s => returnedJson (value v) (state s)
  | .unwound reason s => Json.mkObj [("exit", "unwound"), ("reason", toJson reason), (
    "state",
    state s)]
  | .terminated details => put details "exit" "terminated"

def returnJson {S V : Type} (value : V → S → Json) (state : S → Json) :
    Outcome S V Empty Empty → Json
  | .returned v s => returnedJson (value v s) (state s)
  | .unwound reason _ | .terminated reason => nomatch reason

def observe {O : Type} (relation : O → Prop) (computed : Option O)
    (graph : ∀ outcome, relation outcome ↔ computed = some outcome)
    (render : O → Json) (actual : Json) : Verdict :=
  admits relation computed graph (fun outcome => render outcome == actual) render

def guardOf (j : Json) : Result Guard := do
  return ⟨← natField j "guard", ← natField j "generation"⟩

def guardJson (guard : Guard) : Json :=
  Json.mkObj [("guard", toJson guard.id), ("generation", toJson guard.generation)]

def programErrorJson : ProgramError.Value → Json
  | .accountBorrowFailed => "AccountBorrowFailed"
  | .invalidRealloc => "InvalidRealloc"
  | other => Runtime.programErrorJson other

def withReady (ready : Bool) (verdict : Verdict) : Verdict :=
  Runtime.withRequires "registered requires" ready verdict

end SolanalibTest.Conformance.Library.Families.Pinocchio09
