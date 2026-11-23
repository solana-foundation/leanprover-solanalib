/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Syscalls

/-!
# Host-target branches

Built without `--cfg target_os="solana"`, the getters of solana-sysvar and the `sol_log_data` and
`set_return_data` of solana-program call the overridable `program_stubs`, and the `sol_log` of
solana-msg prints a line. The registered references take the target from their family index
(`GetterTarget.hostStub`, `TextTarget.hostStd`, `DataTarget.hostStub`,
`ReturnData.Target.hostStub`); the checker instantiates the index with that target and with
the recording stubs of the driver as the provider:

* a getter stub logs its call, then consumes the next scripted reply: a panic message (the
  stub unwinds) or a status whose bytes are copied over the `Default` destination;
* the data and return-data stubs log their arguments;
* a standard-output line sink appends the line and a newline to the captured output.

State: `{"stubs": {"replies", "log"}, "stdout": hex}`.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Runtime.Host

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
  SolanalibTest.Conformance.Library.Families.Runtime.Syscalls

structure HostReply where
  syscall : String
  ret : Nat
  data : Solanalib.Runtime.Bytes
  panic : Option String
  deriving DecidableEq

structure HostState where
  replies : List HostReply
  log : List Logged
  stdout : Solanalib.Runtime.Bytes
  deriving DecidableEq

def hostReply (j : Json) : Result HostReply := do
  pure ⟨← (← field j "syscall").getStr?, ← (← field j "return").getNat?, ← asBytes (← field j
    "data"),
    ← Runtime.optField j "panic" Json.getStr?⟩

def hostState (j : Json) : Result HostState := do
  let stubs ← field j "stubs"
  pure ⟨← (← (← field stubs "replies").getArr?).toList.mapM hostReply,
    ← (← (← field stubs "log").getArr?).toList.mapM fun r => do logged (← Runtime.request r),
    ← asBytes (← field j "stdout")⟩

def hostReplyJson (r : HostReply) : Json :=
  Json.mkObj ([("syscall", Json.str r.syscall), ("return", natJson r.ret), ("data", bytesJson
    r.data)] ++
    (match r.panic with | some p => [("panic", Json.str p)] | none => []))

def hostStateJson (s : HostState) : Json :=
  Json.mkObj [("stubs", Json.mkObj [("replies", Json.arr (s.replies.map hostReplyJson).toArray),
    ("log", Json.arr (s.log.map loggedJson).toArray)]), ("stdout", bytesJson s.stdout)]

def someString (s : String) : Option String := some s

/-! ## Getters through `program_stubs` -/

def stubRequest {V : Type} : Sysvar.GetterTarget × Sysvar.ReadRequest V → Option String
  | (.hostStub, ⟨.typed kind, _⟩) => some (typedName kind)
  | _ => none

/-- The recording getter stub: log, consume the reply, panic or copy and return the status. -/
def stubReadStep {V : Type} (layout : Layout V) (s : HostState)
    (request : Sysvar.GetterTarget × Sysvar.ReadRequest V) :
    Outcome HostState (Sysvar.ReadReply V) String Empty :=
  match stubRequest request with
  | none => .unwound "no host stub" { s with log := s.log ++ [.unobservable "getter request"] }
  | some name =>
    let logged := { s with log := s.log ++ [.stubGetter name] }
    match s.replies with
    | r :: rest =>
      if r.syscall = name then
        let after := { logged with replies := rest }
        match r.panic with
        | some m => .unwound m after
        | none => .returned ⟨UInt64.ofNat r.ret, destination layout request.2.initial r.data⟩ after
      else .unwound "stub script error" logged
    | [] => .unwound "a scripted stub reply" logged

abbrev HostGetterOutcome (V : Type) := Outcome HostState (Except ProgramError.Value V) String Empty

def hostGetterChecker {V : Type} [DecidableEq V] (function reference : String)
    (config : Sysvar.GetterConfig V) (run : FamilyRun (Sysvar.getterFamily config))
    (evaluated : run = Sysvar.getterRun config) (ready : HostState → Bool)
    (layout : Layout V) (value : Json → Result V) (render : V → Json) : Checker where
  function := function
  generics := []
  reference := reference
  decides := [reference]
  decidesRequires := [reference]
  check := fun c => do
    let before ← hostState c.state
    asUnit c.args
    let recorded ← parseOutcome (asExcept programError value) hostState someString noReason
      c.outcome
    let index := fnGetterIndex .hostStub (stubReadStep layout)
    return withRequires "GetterReady" (ready before) <| decideOptGraph (S := HostState) (V :=
      Except ProgramError.Value V) (U := String) (T := Empty)
      (run index before ())
      (forwardComputed config (stubReadStep layout before (.hostStub, config.request)))
      (fun o => evaluated ▸ fn_get_graph config .hostStub (stubReadStep layout) before o) recorded
      (outcomeJson hostStateJson (exceptJson programErrorJson render) Json.str emptyJson)

def sdkClockGet : Checker :=
  hostGetterChecker
    "solana_sysvar::clock::<impl solana_sysvar::Sysvar for solana_clock::Clock>::get"
    "Solanalib.Specs.SolanaSysvar.clock.Clock.get_run" Sysvar.sdkClockConfig
    Solanalib.Specs.SolanaSysvar.clock.Clock.get_run rfl
    (fun before => @decide ((Solanalib.Specs.SolanaSysvar.clock.Clock.get_contract.contract
      (fnGetterIndex .hostStub (stubReadStep clockLayout))).requires before ())
      (getterReadyDec Sysvar.sdkClockConfig .hostStub (stubReadStep clockLayout) before))
        clockLayout clock clockJson

def sdkRentGet : Checker :=
  hostGetterChecker "solana_sysvar::rent::<impl solana_sysvar::Sysvar for \
    solana_rent::Rent>::get"
    "Solanalib.Specs.SolanaSysvar.rent.Rent.get_run" Sysvar.sdkRentConfig
    Solanalib.Specs.SolanaSysvar.rent.Rent.get_run rfl
    (fun before => @decide ((Solanalib.Specs.SolanaSysvar.rent.Rent.get_contract.contract
      (fnGetterIndex .hostStub (stubReadStep rent300Layout))).requires before ())
      (getterReadyDec Sysvar.sdkRentConfig .hostStub (stubReadStep rent300Layout) before))
        rent300Layout rent300 rent300Json

/-! ## Standard output, log data and return data -/

def sink (s : HostState) : Log.Event → Outcome HostState Unit String Empty
  | .stdoutLine m => .returned () { s with stdout := s.stdout ++ Log.utf8Bytes m ++ [10] }
  | .stubData f => .returned () { s with log := s.log ++ [.stubLogData f] }
  | .text _ => .returned () { s with log := s.log ++ [.unobservable "text event"] }
  | .data _ => .returned () { s with log := s.log ++ [.unobservable "data event"] }

def logIndex : Solanalib.Specs.SolanaMsg.LogIndex where
  State := HostState
  Unwind := String
  Terminal := Empty
  target := .hostStd
  sink := Callback.ofFunction sink

def dataIndex : Solanalib.Specs.SolanaProgram.log.DataIndex where
  State := HostState
  Unwind := String
  Terminal := Empty
  target := .hostStub
  sink := Callback.ofFunction sink

def returnDataStub (s : HostState) : ReturnData.Request → Outcome HostState Unit String Empty
  | .hostStub data => .returned () { s with log := s.log ++ [.stubReturnData data] }
  | .solana _ _ => .returned () { s with log := s.log ++ [.unobservable "syscall request"] }

def returnDataIndex : ReturnData.Index where
  State := HostState
  Unwind := String
  Terminal := Empty
  target := .hostStub
  provider := Callback.ofFunction returnDataStub

abbrev UnitOutcome := Outcome HostState Unit String Empty

theorem sol_log_graph (before : HostState) (message : String) (o : UnitOutcome) :
    Solanalib.Specs.SolanaMsg.sol_log_run logIndex before message o ↔ sink before (.stdoutLine
      message) = o :=
  Iff.rfl

theorem sol_log_data_graph (before : HostState) (fields : List Solanalib.Runtime.Bytes) (o :
  UnitOutcome) :
    Solanalib.Specs.SolanaProgram.log.sol_log_data_run dataIndex before fields o ↔
      sink before (.stubData fields) = o := Iff.rfl

theorem set_return_data_graph (before : HostState) (data : Solanalib.Runtime.Bytes) (o :
  UnitOutcome) :
    Solanalib.Specs.SolanaProgram.program.set_return_data_model returnDataIndex before data o ↔
      returnDataStub before (.hostStub data) = o := Iff.rfl

def unitJson : UnitOutcome → Json := outcomeJson hostStateJson (fun _ => Json.null) Json.str
  emptyJson

def solLog : Checker where
  function := "solana_msg::sol_log"
  generics := []
  reference := "Solanalib.Specs.SolanaMsg.sol_log_run"
  decides := ["Solanalib.Specs.SolanaMsg.sol_log_run"]
  check := fun c => do
    let before ← hostState c.state
    let message ← utf8 (← field c.args "message")
    let recorded ← parseOutcome asUnit hostState someString noReason c.outcome
    return decideGraph (S := HostState) (V := Unit) (U := String) (T := Empty)
      (Solanalib.Specs.SolanaMsg.sol_log_run logIndex before message) (sink before (.stdoutLine
        message))
      (sol_log_graph before message) recorded unitJson

def solLogData : Checker where
  function := "solana_program::log::sol_log_data"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.log.sol_log_data_run"
  decides := ["Solanalib.Specs.SolanaProgram.log.sol_log_data_run"]
  check := fun c => do
    let before ← hostState c.state
    let fields ← fieldsOf c.args "fields"
    let recorded ← parseOutcome asUnit hostState someString noReason c.outcome
    return decideGraph (S := HostState) (V := Unit) (U := String) (T := Empty)
      (Solanalib.Specs.SolanaProgram.log.sol_log_data_run dataIndex before fields) (sink before
        (.stubData fields))
      (sol_log_data_graph before fields) recorded unitJson

def setReturnData : Checker where
  function := "solana_program::program::set_return_data"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.program.set_return_data_model"
  decides := ["Solanalib.Specs.SolanaProgram.program.set_return_data_model"]
  check := fun c => do
    let before ← hostState c.state
    let data ← asBytes (← field c.args "data")
    let recorded ← parseOutcome asUnit hostState someString noReason c.outcome
    return decideGraph (S := HostState) (V := Unit) (U := String) (T := Empty)
      (Solanalib.Specs.SolanaProgram.program.set_return_data_model returnDataIndex before data)
      (returnDataStub before (.hostStub data)) (set_return_data_graph before data) recorded unitJson

end SolanalibTest.Conformance.Library.Families.Runtime.Host
