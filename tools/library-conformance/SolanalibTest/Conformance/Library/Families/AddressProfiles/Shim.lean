/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AddressProfiles.Evaluation

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.AddressProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
  Solanalib.Specs.Core.Address.Syscall
open Solanalib.Specs.Core.Address.Operations
open Address (pubkey pubkeyJson asU8)

namespace Shim

abbrev Reply := Address.Syscall.ShimReply

inductive Request where
  | create (seeds : List Solanalib.Runtime.Bytes) (programId : Value)
  | find (seeds : List Solanalib.Runtime.Bytes) (programId : Value) (bump : UInt8)
  | hash (fields : List Solanalib.Runtime.Bytes)
  deriving DecidableEq

structure State where
  replies : List Reply
  log : List Request
  deriving DecidableEq

structure Terminal where
  reason : String
  detail : String
  state : State
  deriving DecidableEq

abbrev Exit (V : Type) := Outcome State V String Terminal

/-- The shim writes a prefix and retains every byte outside that prefix. -/
def overwrite (initial : Value) (data : Solanalib.Runtime.Bytes) : Value :=
  ⟨data.take 32 ++ initial.bytes.drop (min 32 data.length), by
    simp only [List.length_append, List.length_take, List.length_drop, initial.length_eq]
    omega⟩

def dispatch {V : Type} (syscall : String) (request : Request)
    (decode : Reply → V) (before : State) : Exit V :=
  match before.replies with
  | reply :: rest =>
    if reply.syscall = syscall then
      let after : State := ⟨rest, before.log ++ [request]⟩
      match reply.terminate with
      | some detail => .terminated ⟨syscall, detail, after⟩
      | none => .returned (decode reply) after
    else .terminated ⟨"shim", "script error", before⟩
  | [] => .terminated ⟨"shim", "script error", before⟩

def output (mode : Initialization) (initial : Option Value) (data : Solanalib.Runtime.Bytes) :
  mode.Output :=
  match mode with
  | .zeroed => overwrite (initial.getD .zero) data
  | .uninitialized => Address.Syscall.addressOut data

def createProvider (mode : Initialization) (before : State) (request : CreateRequest) :
    Exit (CreateReply mode) :=
  dispatch "sol_create_program_address"
    (.create (request.inputs.seeds.take request.seedCount.toNat) request.inputs.programId)
    (fun reply => ⟨reply.ret, output mode request.output reply.data⟩) before

def zeroFindProvider (before : State) (request : PdaRequest) : Exit ZeroFindReply :=
  dispatch "sol_try_find_program_address"
    (.find (request.seeds.take request.seedCount.toNat) request.programId request.bumpOutput)
    (fun reply => ⟨reply.ret, overwrite (request.addressOutput.getD .zero) reply.data,
      reply.bump.getD request.bumpOutput⟩) before

def uninitFindProvider (before : State) (request : PdaRequest) : Exit PdaReply :=
  dispatch "sol_try_find_program_address"
    (.find (request.seeds.take request.seedCount.toNat) request.programId request.bumpOutput)
    (fun reply => ⟨reply.ret, Address.Syscall.addressOut reply.data,
      reply.bump.getD request.bumpOutput⟩) before

/-- The selected hashv calls use a zeroed destination and ignore the status.
The scripted full reply is a test interpretation, not a cryptographic law. -/
def hashProvider (before : State) (fields : List Solanalib.Runtime.Bytes) : Exit Value :=
  dispatch "sol_sha256" (.hash fields) (fun reply => overwrite .zero reply.data) before

def stringPanic (before : State) (message : String) : Exit Empty := .unwound message before

def searchPanic (before : State) (_ : SearchPanic) : Exit Empty := .unwound panicMessage before

abbrev createIndex (mode : Initialization) := Evaluation.createIndex mode (createProvider mode)
  stringPanic
abbrev zeroFindIndex := Evaluation.zeroFindIndex zeroFindProvider searchPanic
abbrev uninitFindIndex := Evaluation.uninitFindIndex uninitFindProvider searchPanic
abbrev seedIndex := Evaluation.seedIndex hashProvider

def bytesList (j : Json) : Result (List Solanalib.Runtime.Bytes) := do
  (← j.getArr?).toList.mapM asBytes

def bytesListJson (values : List Solanalib.Runtime.Bytes) : Json := Json.arr (values.map
  bytesJson).toArray

def request (j : Json) : Result Request := do
  match ← (← field j "syscall").getStr? with
  | "sol_create_program_address" =>
    pure (.create (← bytesList (← field j "seeds")) (← pubkey (← field j "program_id")))
  | "sol_try_find_program_address" =>
    pure (.find (← bytesList (← field j "seeds")) (← pubkey (← field j "program_id"))
      (← asU8 (← field j "bump")))
  | "sol_sha256" => pure (.hash (← bytesList (← field j "fields")))
  | other => throw s!"address wrapper did not issue {other}"

def state (j : Json) : Result State := do
  let calls ← field j "syscalls"
  pure ⟨← (← (← field calls "replies").getArr?).toList.mapM Address.Syscall.shimReply,
    ← (← (← field calls "log").getArr?).toList.mapM request⟩

def requestJson : Request → Json
  | .create seeds programId => Json.mkObj [("syscall", "sol_create_program_address"),
      ("seeds", bytesListJson seeds), ("program_id", pubkeyJson programId)]
  | .find seeds programId bump => Json.mkObj [("syscall", "sol_try_find_program_address"),
      ("seeds", bytesListJson seeds), ("program_id", pubkeyJson programId), ("bump", toJson
        bump.toNat)]
  | .hash fields => Json.mkObj [("syscall", "sol_sha256"), ("fields", bytesListJson fields)]

def callsJson (st : State) : Json := Json.mkObj [
  ("replies", Json.arr (st.replies.map Address.Syscall.shimReplyJson).toArray),
  ("log", Json.arr (st.log.map requestJson).toArray)]

def stateJson (st : State) : Json := Json.mkObj [("syscalls", callsJson st)]

def exit {V : Type} (value : Json → Result V) (j : Json) : Result (Exit V) := do
  match ← (← field j "exit").getStr? with
  | "returned" => pure (.returned (← value (← field j "result")) (← state (← field j "state")))
  | "unwound" => pure (.unwound (← (← field j "reason").getStr?) (← state (← field j "state")))
  | "terminated" => pure (.terminated ⟨← (← field j "reason").getStr?,
      ← (← field j "detail").getStr?, ← state j⟩)
  | other => throw s!"unknown exit {other}"

def exitJson {V : Type} (render : V → Json) : Exit V → Json
  | .returned value st => returnedJson (render value) (stateJson st)
  | .unwound reason st => Json.mkObj [("exit", "unwound"), ("reason", Json.str reason), (
    "state",
    stateJson st)]
  | .terminated terminal => Json.mkObj [("exit", "terminated"), ("reason", Json.str
    terminal.reason),
      ("detail", Json.str terminal.detail), ("syscalls", callsJson terminal.state)]

def error (j : Json) : Result Error := do
  match ← j.getStr? with
  | "MaxSeedLengthExceeded" => pure .maxSeedLengthExceeded
  | "InvalidSeeds" => pure .invalidSeeds
  | "IllegalOwner" => pure .illegalOwner
  | other => throw s!"unknown address error {other}"

def errorJson : Error → Json
  | .maxSeedLengthExceeded => "MaxSeedLengthExceeded"
  | .invalidSeeds => "InvalidSeeds"
  | .illegalOwner => "IllegalOwner"

def result (j : Json) : Result (Except Error Value) :=
  match j.getObjVal? "ok" with
  | .ok value => do pure (.ok (← pubkey value))
  | .error _ => do pure (.error (← error (← field j "err")))

def resultJson : Except Error Value → Json
  | .ok value => Json.mkObj [("ok", pubkeyJson value)]
  | .error e => Json.mkObj [("err", errorJson e)]

def seedInputs (j : Json) : Result SeedInputs := do
  pure ⟨← pubkey (← field j "base"), ← (← field j "seed").getStr?, ← pubkey (← field j
    "owner")⟩

def associatedArgs (j : Json) : Result AssociatedInputs := do
  pure ⟨← pubkey (← field j "wallet"), ← pubkey (← field j "mint"),
    ← pubkey (← field j "token_program")⟩

/-- Decide the registered relation itself, via its proved executable graph. -/
def decideOpt {V : Type} [DecidableEq V] (relation : Exit V → Prop) (computed : Option (Exit V))
    (graph : ∀ o, relation o ↔ computed = some o) (recorded : Exit V)
    (render : V → Json) : Verdict :=
  have : Decidable (relation recorded) := decidable_of_iff _ (graph recorded).symm
  ⟨decide (relation recorded), match computed with
    | some o => exitJson render o
    | none => Json.str "no outcome: uninitialized success destination"⟩

def checkAdmission (precondition : Prop) (decision : Bool)
    (agreement : precondition ↔ decision = true) : Result Unit :=
  have : Decidable precondition := decidable_of_iff _ agreement.symm
  if decide precondition then pure ()
  else throw "outside the precondition (initialized-success destination)"

end Shim
end SolanalibTest.Conformance.Library.Families.AddressProfiles
