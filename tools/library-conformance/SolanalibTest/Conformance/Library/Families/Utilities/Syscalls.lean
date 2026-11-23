/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.Hash
import Solanalib.Specs.SolanaProgram.Get
import Solanalib.Specs.SolanaProgram.Log
import Solanalib.Specs.SolanaSysvar.EpochSchedule
import Solanalib.Specs.SolanaSha256Hasher.Hash
import SolanalibTest.Conformance.Library.Families.Runtime.Syscalls
import SolanalibTest.Conformance.Library.Families.Utilities.Values
import SolanalibTest.Conformance.Library.Families.Utilities.CheckedRuntime
import Solanalib.Specs.SolanaSysvar.GetStringError
import Solanalib.Specs.SolanaSha256Hasher.HashInitialized
import Solanalib.Specs.SolanaMsg.LogHostStdout

set_option autoImplicit false

open Lean (Json toJson)

open Solanalib.Specs.SolanaProgram

namespace SolanalibTest.Conformance.Library.Families.Utilities.Syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Syscalls

/-- Reuse the established shim state, extending only its request parser for the
new typed epoch getter and the zero-argument compute-unit logging request. -/
def utilityLogged (request : Runtime.Request) : Result Logged :=
  if request.syscall = "sol_get_epoch_schedule_sysvar" ∨ request.syscall = "sol_log_compute\
    _units_"
    then
    pure (.typedSysvar request.syscall)
  else logged request

def utilityState (state : Json) : Result ShimState := do
  let s ← Runtime.syscallsOf state
  pure ⟨s.replies, ← s.log.mapM utilityLogged⟩

def utilityOutcome {V : Type} (value : Json → Result V) (j : Json) :
    Result (Option (Outcome ShimState V Empty ShimTerminal)) := do
  match ← Runtime.terminated? j with
  | some t =>
    let syscalls ← match t.syscalls with
      | some st => do pure (⟨st.replies, ← st.log.mapM utilityLogged⟩ : ShimState)
      | none => throw "terminated outcome without syscall state"
    pure (some (.terminated ⟨t.reason, detailText t.detail, syscalls⟩))
  | none => parseOutcome value utilityState noReason noReason j

/-- Typed sysvar outputs are copied only for status zero, as in the shared shim.
A partial successful write preserves the remaining initialized Default fields. -/
def typedStep {V : Type} (layout : Layout V) (state : ShimState)
    (request : Sysvar.GetterTarget × Sysvar.ReadRequest V) :
    Outcome ShimState (Sysvar.ReadReply V) Empty ShimTerminal :=
  let (observed, syscall, copied) := readRequest request
  answer state observed syscall fun reply =>
    ⟨UInt64.ofNat reply.ret,
      destination layout request.2.initial (if reply.ret = 0 then copied reply.data else [])⟩

def typedIndex {V : Type} (layout : Layout V) : Sysvar.GetterIndex V :=
  fnGetterIndex .solana (typedStep layout)

def legacyError (j : Json) : Result Sysvar.Legacy.Error := do
  let text ← j.getStr?
  if text.startsWith "BorshIoError(" && text.endsWith ")" then
    let payload ← Json.parse ((text.drop 13).dropEnd 1).toString
    pure (.borshIoError (← payload.getStr?))
  else pure (.plain (← programError j))

def legacyErrorJson : Sysvar.Legacy.Error → Json
  | .plain error => programErrorJson error
  | .borshIoError text => Json.str s!"BorshIoError({(Json.str text).compress})"

/-- Only the returned SDK-owned String is projected from allocator tracing;
shim bookkeeping lives in the separate explicit syscall provider state. -/
structure StringAllocation where
  text : String
  capacity : Nat
  fresh : Bool
  live : Bool
  deriving DecidableEq

structure LegacyState where
  shim : ShimState
  strings : List StringAllocation
  deriving DecidableEq

def stringAllocation (j : Json) : Result StringAllocation := do
  pure ⟨← (← field j "text").getStr?, ← (← field j "capacity").getNat?,
    ← bool (← field j "fresh"), ← bool (← field j "live")⟩

def legacyState (j : Json) : Result LegacyState := do
  pure ⟨← utilityState j, ← (← (← field j "strings").getArr?).toList.mapM stringAllocation⟩

/-- Render the established request-log projection, without losing its fields. -/
def legacyRenderState (state : LegacyState) : Json :=
  match shimStateJson state.shim with
  | .obj object => Json.mkObj (object.toList ++ [("strings", Json.arr
      ((state.strings.map fun string => Json.mkObj [
        ("text", Json.str string.text), ("capacity", toJson string.capacity),
        ("fresh", Json.bool string.fresh), ("live", Json.bool string.live)]).toArray))])
  | _ => Json.null

def legacyOutcome {V : Type} (value : Json → Result V) (j : Json) :
    Result (Option (Outcome LegacyState V Empty ShimTerminal)) := do
  match ← Runtime.terminated? j with
  | some t =>
    let syscalls ← match t.syscalls with
      | some st => do pure (⟨st.replies, ← st.log.mapM utilityLogged⟩ : ShimState)
      | none => throw "terminated outcome without syscall state"
    pure (some (.terminated ⟨t.reason, detailText t.detail, syscalls⟩))
  | none => parseOutcome value legacyState noReason noReason j

def legacyRead {V : Type} (layout : Layout V) (before : LegacyState)
    (request : Sysvar.GetterTarget × Sysvar.ReadRequest V) :
    Outcome LegacyState (Sysvar.ReadReply V) Empty ShimTerminal :=
  match typedStep layout before.shim request with
  | .returned reply after => .returned reply { before with shim := after }
  | .unwound impossible _ => nomatch impossible
  | .terminated reason => .terminated reason

def copyString (before : LegacyState) (text : String) :
    Outcome LegacyState Nat Empty ShimTerminal :=
  .returned before.strings.length { before with strings := before.strings ++
    [⟨text, text.toUTF8.size, true, true⟩] }

def currentString (before : LegacyState) (resource : Nat) : Option String := do
  let allocation ← before.strings[resource]?
  if allocation.live then some allocation.text else none

abbrev legacyIndexOf {V : Type}
    (step : LegacyState → Sysvar.GetterTarget × Sysvar.ReadRequest V →
      Outcome LegacyState (Sysvar.ReadReply V) Empty ShimTerminal) : Sysvar.Legacy.Index V := {
  getter := fnGetterIndex .solana step
  StringResource := Nat
  currentString := currentString
  copyLiteral := Callback.ofFunction copyString
}

abbrev legacyIndex {V : Type} (layout : Layout V) : Sysvar.Legacy.Index V := legacyIndexOf
  (legacyRead layout)

theorem stringReady {V : Type} (table : Sysvar.Legacy.ErrorTable) (request : Sysvar.ReadRequest V)
    (step : LegacyState → Sysvar.GetterTarget × Sysvar.ReadRequest V →
      Outcome LegacyState (Sysvar.ReadReply V) Empty ShimTerminal) (before : LegacyState) :
    Sysvar.Legacy.StringReady table request (legacyIndexOf step) before := by
  intro afterRead _ resource afterCopy copied
  change copyString afterRead "Unknown" = .returned resource afterCopy at copied
  cases copied
  simp [currentString]

def legacyReadyDec {V : Type} (table : Sysvar.Legacy.ErrorTable) (request : Sysvar.ReadRequest V)
    (step : LegacyState → Sysvar.GetterTarget × Sysvar.ReadRequest V →
      Outcome LegacyState (Sysvar.ReadReply V) Empty ShimTerminal) (before : LegacyState) :
    Decidable (((Sysvar.Legacy.family table request).contract (legacyIndexOf step)).requires before
      ()) :=
  @instDecidableAnd _ _ (getterReadyDec (Sysvar.Legacy.config table request) .solana step before)
    (isTrue (stringReady table request step before))

abbrev LegacyOutcome (V : Type) := Outcome LegacyState (Except (Sysvar.Legacy.OwnedError Nat) V)
  Empty ShimTerminal
abbrev LegacyObserved (V : Type) := Outcome LegacyState (Except Sysvar.Legacy.Error V) Empty
  ShimTerminal

def legacyNext {V : Type} : Except ProgramError.Value V → LegacyState → LegacyOutcome V
  | .ok value, before => .returned (.ok value) before
  | .error .borshIoError, before =>
    Outcome.map (fun resource => Except.error (Sysvar.Legacy.OwnedError.borshIoError resource))
      (copyString before "Unknown")
  | .error other, before => .returned (.error (.plain other)) before

theorem legacy_next_graph {V : Type} (layout : Layout V) (result : Except ProgramError.Value V)
    (before : LegacyState) (outcome : LegacyOutcome V) :
    Sysvar.Legacy.next (legacyIndex layout) result before outcome ↔ legacyNext result before =
      outcome := by
  cases result with
  | ok value => exact eq_comm
  | error error =>
    cases error <;> try exact eq_comm
    exact Callback.map_ofFunction _ _ _ _ _

def legacyComputed {V : Type} (table : Sysvar.Legacy.ErrorTable) (request : Sysvar.ReadRequest V)
    (layout : Layout V) (before : LegacyState) : Option (LegacyOutcome V) :=
  (forwardComputed (Sysvar.Legacy.config table request)
    (legacyRead layout before (.solana, request))).map (fun pending => Outcome.bind pending
      legacyNext)

theorem legacy_graph {V : Type} (table : Sysvar.Legacy.ErrorTable) (request : Sysvar.ReadRequest V)
    (layout : Layout V) (before : LegacyState) (outcome : LegacyOutcome V) :
    Sysvar.Legacy.run table request (legacyIndex layout) before () outcome ↔
      legacyComputed table request layout before = some outcome := by
  have graph (middle : Outcome LegacyState (Except ProgramError.Value V) Empty ShimTerminal) :
      Sysvar.get (Sysvar.Legacy.config table request) (legacyIndex layout).getter before () middle ↔
        forwardComputed (Sysvar.Legacy.config table request)
          (legacyRead layout before (.solana, request)) = some middle :=
    fn_get_graph (Sysvar.Legacy.config table request) .solana (legacyRead layout) before middle
  have nextGraph (middle : Outcome LegacyState (Except ProgramError.Value V) Empty ShimTerminal) :
      (match middle with
        | .returned value after => Sysvar.Legacy.next (legacyIndex layout) value after outcome
        | .unwound reason after => outcome = .unwound reason after
        | .terminated reason => outcome = .terminated reason) ↔
        Outcome.bind middle legacyNext = outcome := by
    cases middle with
    | returned value after => exact legacy_next_graph layout value after outcome
    | unwound impossible _ => nomatch impossible
    | terminated reason => exact eq_comm
  unfold legacyComputed
  constructor
  · rintro ⟨middle, called, continued⟩
    rw [(graph middle).mp called]
    exact congrArg some ((nextGraph middle).mp (by cases middle <;> exact continued))
  · intro computed
    cases step : forwardComputed (Sysvar.Legacy.config table request)
        (legacyRead layout before (.solana, request)) with
    | none => rw [step] at computed; cases computed
    | some middle =>
      rw [step] at computed
      refine ⟨middle, (graph middle).mpr step, ?_⟩
      have continued := (nextGraph middle).mpr (Option.some.inj computed)
      cases middle <;> exact continued

def legacyProject {V : Type} (layout : Layout V) : LegacyOutcome V → Option (LegacyObserved V)
  | .returned (.ok value) after => some (.returned (.ok value) after)
  | .returned (.error error) after => do
    pure (.returned (.error (← Sysvar.Legacy.observeError (legacyIndex layout) after error)) after)
  | .unwound impossible _ => nomatch impossible
  | .terminated reason => some (.terminated reason)

def legacyGetter {V : Type} [DecidableEq V] (function reference : String)
    (table : Sysvar.Legacy.ErrorTable) (request : Sysvar.ReadRequest V) (layout : Layout V)
    (parse : Json → Result V) (render : V → Json)
    (run : Callback.Run LegacyState Unit (Except (Sysvar.Legacy.OwnedError Nat) V) Empty
      ShimTerminal)
    (binding : run = Sysvar.Legacy.run table request (legacyIndex layout))
    (ready : LegacyState → Bool) : Checker where
  function := function
  generics := []
  reference := reference
  decides := [reference]
  decidesRequires := [reference]
  check := fun c => do
    let before ← legacyState c.state
    asUnit c.args
    let recorded ← legacyOutcome (asExcept legacyError parse) c.outcome
    let actual := legacyComputed table request layout before
    return withRequires "GetterReady and StringReady" (ready before) <|
      decideOptGraph (S := LegacyState) (V := Except Sysvar.Legacy.Error V) (U := Empty) (T :=
        ShimTerminal)
        (fun observed => ∃ output, run before () output ∧ legacyProject layout output = some
          observed)
        (actual.bind (legacyProject layout))
        (CheckedRuntime.projected_graph (run before ()) actual
          (fun o => by rw [binding]; exact legacy_graph table request layout before o)
            (legacyProject layout)) recorded
        (outcomeJson legacyRenderState (exceptJson legacyErrorJson render) emptyJson
          shimTerminalJson)

def splitClock : Checker := legacyGetter
  "solana_sysvar::clock::<impl solana_sysvar::Sysvar for solana_clock::Clock>::get"
  "Solanalib.Specs.SolanaSysvar.clock.Clock.string_error.get_run" .split222 ⟨.typed .clock, some
    Sysvar.zeroClock⟩
  clockLayout clock clockJson (Solanalib.Specs.SolanaSysvar.clock.Clock.string_error.get_run
    (legacyIndex clockLayout)) rfl
  (fun before => @decide
    ((Solanalib.Specs.SolanaSysvar.clock.Clock.string_error.get_contract.contract (legacyIndex
    clockLayout)).requires before ())
    (legacyReadyDec .split222 ⟨.typed .clock, some Sysvar.zeroClock⟩ (legacyRead clockLayout)
      before))

def splitRent : Checker := legacyGetter
  "solana_sysvar::rent::<impl solana_sysvar::Sysvar for solana_rent::Rent>::get"
  "Solanalib.Specs.SolanaSysvar.rent.Rent.string_error.get_run" .split222 ⟨.typed .rent, some
    Sysvar.defaultRent300⟩
  rent300Layout Rent.rent300 rent300Json
    (Solanalib.Specs.SolanaSysvar.rent.Rent.string_error.get_run (legacyIndex rent300Layout)) rfl
  (fun before => @decide
    ((Solanalib.Specs.SolanaSysvar.rent.Rent.string_error.get_contract.contract (legacyIndex
    rent300Layout)).requires before ())
    (legacyReadyDec .split222 ⟨.typed .rent, some Sysvar.defaultRent300⟩ (legacyRead rent300Layout)
      before))

/-- Earlier hash wrappers always retain a complete zero-initialized buffer.
Only its overwritten prefix comes from the scripted provider. -/
def initializedHash (bytes : Solanalib.Runtime.Bytes) : Hash.Value :=
  let output := bytes.take 32 ++ List.replicate (32 - bytes.length) 0
  ⟨output, by dsimp only [output]; simp only [List.length_append, List.length_take,
    List.length_replicate]; omega⟩

def initializedHashStep (state : ShimState) (request : Hash.Syscall.Request) :
    Outcome ShimState Hash.Initialized.Reply Empty ShimTerminal :=
  answer state (.sha256 request.slices request.count.toNat) "sol_sha256" fun reply =>
    ⟨UInt64.ofNat reply.ret, initializedHash reply.data⟩

def initializedHashIndex : Hash.Initialized.Index where
  State := ShimState
  Unwind := Empty
  Terminal := ShimTerminal
  provider := Callback.ofFunction initializedHashStep

abbrev InitializedOutcome := Outcome ShimState Hash.Value Empty ShimTerminal

def initializedComputed (before : ShimState) (slices : List Solanalib.Runtime.Bytes) :
  InitializedOutcome :=
  Outcome.map Hash.Initialized.Reply.output (initializedHashStep before (Hash.Initialized.request
    slices))

theorem initialized_graph (before : ShimState) (slices : List Solanalib.Runtime.Bytes) (outcome :
  InitializedOutcome) :
    Solanalib.Specs.SolanaSha256Hasher.zero_initialized.hashv_run initializedHashIndex before
      slices outcome ↔
      initializedComputed before slices = outcome :=
  Callback.map_ofFunction _ _ _ _ _

def hashv222 : Checker where
  function := "solana_sha256_hasher::hashv"
  generics := []
  reference := "Solanalib.Specs.SolanaSha256Hasher.zero_initialized.hashv_run"
  decides := ["Solanalib.Specs.SolanaSha256Hasher.zero_initialized.hashv_run"]
  check := fun c => do
    let before ← utilityState c.state
    let slices ← (← c.args.getArr?).toList.mapM asBytes
    let recorded ← utilityOutcome hashValue c.outcome
    return decideGraph (S := ShimState) (V := Hash.Value) (U := Empty) (T := ShimTerminal)
      (Solanalib.Specs.SolanaSha256Hasher.zero_initialized.hashv_run initializedHashIndex before
      slices)
      (initializedComputed before slices) (initialized_graph before slices) recorded
      (outcomeJson shimStateJson (fun hash => bytesJson hash.bytes) emptyJson shimTerminalJson)

def hash222 (function : String) : Checker where
  function := function
  generics := []
  reference := "Solanalib.Specs.SolanaSha256Hasher.zero_initialized.hash_run"
  decides := ["Solanalib.Specs.SolanaSha256Hasher.zero_initialized.hash_run"]
  check := fun c => do
    let before ← utilityState c.state
    let bytes ← asBytes c.args
    let recorded ← utilityOutcome hashValue c.outcome
    return decideGraph (S := ShimState) (V := Hash.Value) (U := Empty) (T := ShimTerminal)
      (Solanalib.Specs.SolanaSha256Hasher.zero_initialized.hash_run initializedHashIndex before
      bytes)
      (initializedComputed before [bytes]) (initialized_graph before [bytes]) recorded
      (outcomeJson shimStateJson (fun hash => bytesJson hash.bytes) emptyJson shimTerminalJson)

def programHash (function : String) : Checker where
  function := function
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.hash.hash_run"
  decides := ["Solanalib.Specs.SolanaProgram.hash.hash_run"]
  check := fun c => do
    let before ← utilityState c.state
    let bytes ← asBytes c.args
    let recorded ← utilityOutcome hashValue c.outcome
    return decideGraph (S := ShimState) (V := Hash.Value) (U := Empty) (T := ShimTerminal)
      (hash.hash_run initializedHashIndex before bytes)
      (initializedComputed before [bytes]) (initialized_graph before [bytes]) recorded
      (outcomeJson shimStateJson (fun hash => bytesJson hash.bytes) emptyJson shimTerminalJson)

def msgIndex : Solanalib.Specs.SolanaMsg.host_stdout.Index where
  State := ShimState
  Unwind := Empty
  Terminal := ShimTerminal
  target := .solana
  sink := logIndex.sink

def msgLog : Checker where
  function := "solana_msg::sol_log"
  generics := []
  reference := "Solanalib.Specs.SolanaMsg.host_stdout.sol_log_run"
  decides := ["Solanalib.Specs.SolanaMsg.host_stdout.sol_log_run"]
  check := fun c => do
    let before ← utilityState c.state
    let message ← c.args.getStr?
    let recorded ← utilityOutcome asUnit c.outcome
    return decideGraph (S := ShimState) (V := Unit) (U := Empty) (T := ShimTerminal)
      (Solanalib.Specs.SolanaMsg.host_stdout.sol_log_run msgIndex before message)
      (logOnly before (.log (Log.utf8Bytes message))) (fun _ => Iff.rfl) recorded unitOutcomeJson

def legacyUninitialized {V : Type} (before : LegacyState) (_ : Sysvar.GetterTarget ×
  Sysvar.ReadRequest V) :
    Outcome LegacyState (Sysvar.ReadReply V) Empty ShimTerminal := .returned ⟨0, none⟩ before

theorem splitClock_decider_rejects :
    @decide ((Solanalib.Specs.SolanaSysvar.clock.Clock.string_error.get_contract.contract
      (legacyIndexOf (legacyUninitialized (V := Sysvar.Clock)))).requires ⟨⟨[], []⟩, []⟩ ())
      (legacyReadyDec .split222 ⟨.typed .clock, some Sysvar.zeroClock⟩ legacyUninitialized ⟨⟨[],
        []⟩, []⟩) = false := by decide

theorem splitRent_decider_rejects :
    @decide ((Solanalib.Specs.SolanaSysvar.rent.Rent.string_error.get_contract.contract
      (legacyIndexOf (legacyUninitialized (V := Sysvar.Rent300)))).requires ⟨⟨[], []⟩, []⟩ ())
      (legacyReadyDec .split222 ⟨.typed .rent, some Sysvar.defaultRent300⟩ legacyUninitialized
        ⟨⟨[], []⟩, []⟩) = false := by decide

end SolanalibTest.Conformance.Library.Families.Utilities.Syscalls

namespace SolanalibTest.Conformance.Library.Families.Utilities.Syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Syscalls

/-- repr(C) has seven padding bytes after warmup. They are not logical fields;
all five fields, including partially preserved Default fields, are compared. -/
def epochLayout : Layout EpochSchedule.Value where
  size := 40
  encode := fun value => Solanalib.Runtime.u64le value.slotsPerEpoch.toNat ++
    Solanalib.Runtime.u64le value.leaderScheduleSlotOffset.toNat ++ [if value.warmup then 1 else 0]
      ++
    List.replicate 7 0 ++ Solanalib.Runtime.u64le value.firstNormalEpoch.toNat ++
    Solanalib.Runtime.u64le value.firstNormalSlot.toNat
  decode := fun bytes => ⟨UInt64.ofNat (word bytes 0), UInt64.ofNat (word bytes 8),
    bytes.getD 16 0 != 0, UInt64.ofNat (word bytes 24), UInt64.ofNat (word bytes 32)⟩

def epochGet : Checker where
  function :=
    "solana_sysvar::epoch_schedule::<impl solana_sysvar::Sysvar for \
      solana_epoch_schedule::EpochSchedule>::get"
  generics := []
  reference := "Solanalib.Specs.SolanaSysvar.epoch_schedule.EpochSchedule.get_run"
  decides := ["Solanalib.Specs.SolanaSysvar.epoch_schedule.EpochSchedule.get_run"]
  decidesRequires := ["Solanalib.Specs.SolanaSysvar.epoch_schedule.EpochSchedule.get_run"]
  check := fun c => do
    let before ← utilityState c.state
    asUnit c.args
    let recorded ← utilityOutcome (asExcept programError Values.epochValue) c.outcome
    let config := EpochSchedule.getterConfig
    return withRequires "GetterReady"
      (@decide ((Solanalib.Specs.SolanaSysvar.epoch_schedule.EpochSchedule.get_contract.contract
        (typedIndex epochLayout)).requires before ())
        (getterReadyDec config .solana (typedStep epochLayout) before)) <|
      decideOptGraph (S := ShimState) (V := Except ProgramError.Value EpochSchedule.Value) (U :=
        Empty) (T := ShimTerminal)
        (Solanalib.Specs.SolanaSysvar.epoch_schedule.EpochSchedule.get_run (typedIndex epochLayout)
        before ())
        (forwardComputed config (typedStep epochLayout before (.solana, config.request)))
        (fn_get_graph config .solana (typedStep epochLayout) before) recorded
        (outcomeJson shimStateJson (exceptJson programErrorJson Values.epochJson) emptyJson
          shimTerminalJson)

def hash310 : Checker where
  function := "solana_sha256_hasher::hash"
  generics := []
  reference := "Solanalib.Specs.SolanaSha256Hasher.hash_run"
  decides := ["Solanalib.Specs.SolanaSha256Hasher.hash_run"]
  decidesRequires := ["Solanalib.Specs.SolanaSha256Hasher.hash_run"]
  check := fun c => do
    let before ← utilityState c.state
    let bytes ← asBytes c.args
    let recorded ← utilityOutcome hashValue c.outcome
    letI : Decidable ((Solanalib.Specs.SolanaSha256Hasher.hash_contract.contract
      hashIndex).requires before bytes) :=
      decidable_of_iff _ (hashv_requires_iff before [bytes]).symm
    return withRequires "EveryReturnInitialized"
      (decide ((Solanalib.Specs.SolanaSha256Hasher.hash_contract.contract hashIndex).requires
        before bytes)) <|
      decideOptGraph (S := ShimState) (V := Hash.Value) (U := Empty) (T := ShimTerminal)
        (Solanalib.Specs.SolanaSha256Hasher.hash_run hashIndex before bytes)
        (hashComputed before [bytes]) (hashv_graph before [bytes]) recorded
        (outcomeJson shimStateJson (fun hash => bytesJson hash.bytes) emptyJson shimTerminalJson)

theorem epoch_decider_rejects :
    @decide ((Solanalib.Specs.SolanaSysvar.epoch_schedule.EpochSchedule.get_contract.contract
      (fnGetterIndex .solana (uninitializedStep (V := EpochSchedule.Value)))).requires () ())
      (getterReadyDec EpochSchedule.getterConfig .solana uninitializedStep ()) = false := by
  decide

end SolanalibTest.Conformance.Library.Families.Utilities.Syscalls

namespace SolanalibTest.Conformance.Library.Families.Utilities.Syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Syscalls

def legacy118Clock : Checker := legacyGetter
  "solana_program::sysvar::clock::<impl solana_program::sysvar::Sysvar for \
    solana_program::clock::Clock>::get"
  "Solanalib.Specs.SolanaProgram.sysvar.clock.Clock.get_run" .program118 ⟨.typed .clock, some
    Sysvar.zeroClock⟩
  clockLayout clock clockJson (sysvar.clock.Clock.get_run
    (legacyIndex clockLayout)) rfl
  (fun before => @decide ((sysvar.clock.Clock.get_contract.contract
    (legacyIndex clockLayout)).requires before ())
    (legacyReadyDec .program118 ⟨.typed .clock, some Sysvar.zeroClock⟩ (legacyRead clockLayout)
      before))

def legacy118Rent : Checker := legacyGetter
  "solana_program::sysvar::rent::<impl solana_program::sysvar::Sysvar for \
    solana_program::rent::Rent>::get"
  "Solanalib.Specs.SolanaProgram.sysvar.rent.Rent.get_run" .program118 ⟨.typed .rent, some
    Sysvar.defaultRent300⟩
  rent300Layout Rent.rent300 rent300Json (sysvar.rent.Rent.get_run
    (legacyIndex rent300Layout)) rfl
  (fun before => @decide ((sysvar.rent.Rent.get_contract.contract
    (legacyIndex rent300Layout)).requires before ())
    (legacyReadyDec .program118 ⟨.typed .rent, some Sysvar.defaultRent300⟩ (legacyRead
      rent300Layout) before))

def sdkLogStep (before : ShimState) : SdkLog.Request → Outcome ShimState Unit Empty ShimTerminal
  | .text .solana message => logOnly before (.log (Log.utf8Bytes message))
  | .computeUnits .solana => logOnly before (.typedSysvar "sol_log_compute_units_")
  | _ => logOnly before (.unobservable "legacy host stub")

def sdkLogIndex : SdkLog.Index where
  State := ShimState
  Unwind := Empty
  Terminal := ShimTerminal
  target := .solana
  sink := Callback.ofFunction sdkLogStep

def legacyLog : Checker where
  function := "solana_program::log::sol_log"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.log.sol_log_run"
  decides := ["Solanalib.Specs.SolanaProgram.log.sol_log_run"]
  check := fun c => do
    let before ← utilityState c.state
    let message ← c.args.getStr?
    let recorded ← utilityOutcome asUnit c.outcome
    return decideGraph (S := ShimState) (V := Unit) (U := Empty) (T := ShimTerminal)
      (log.sol_log_run sdkLogIndex before message)
      (sdkLogStep before (.text .solana message)) (fun _ => Iff.rfl) recorded unitOutcomeJson

theorem legacy118Clock_decider_rejects :
    @decide ((sysvar.clock.Clock.get_contract.contract
      (legacyIndexOf (legacyUninitialized (V := Sysvar.Clock)))).requires ⟨⟨[], []⟩, []⟩ ())
      (legacyReadyDec .program118 ⟨.typed .clock, some Sysvar.zeroClock⟩ legacyUninitialized ⟨⟨[],
        []⟩, []⟩) = false := by decide

theorem legacy118Rent_decider_rejects :
    @decide ((sysvar.rent.Rent.get_contract.contract
      (legacyIndexOf (legacyUninitialized (V := Sysvar.Rent300)))).requires ⟨⟨[], []⟩, []⟩ ())
      (legacyReadyDec .program118 ⟨.typed .rent, some Sysvar.defaultRent300⟩ legacyUninitialized
        ⟨⟨[], []⟩, []⟩) = false := by decide

end SolanalibTest.Conformance.Library.Families.Utilities.Syscalls

namespace SolanalibTest.Conformance.Library.Families.Utilities.Syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Syscalls

def legacy115Rent : Checker := legacyGetter
  "solana_program::sysvar::rent::<impl solana_program::sysvar::Sysvar for \
    solana_program::rent::Rent>::get"
  "Solanalib.Specs.SolanaProgram.sysvar.rent.Rent.get_legacy_error_table_run" .program115 ⟨.typed
    .rent, some Sysvar.defaultRent300⟩
  rent300Layout Rent.rent300 rent300Json
    (sysvar.rent.Rent.get_legacy_error_table_run (legacyIndex
    rent300Layout)) rfl
  (fun before => @decide
    ((sysvar.rent.Rent.get_legacy_error_table_contract.contract
    (legacyIndex rent300Layout)).requires before ())
    (legacyReadyDec .program115 ⟨.typed .rent, some Sysvar.defaultRent300⟩ (legacyRead
      rent300Layout) before))

def computeLog : Checker where
  function := "solana_program::log::sol_log_compute_units"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.log.sol_log_compute_units_run"
  decides := ["Solanalib.Specs.SolanaProgram.log.sol_log_compute_units_run"]
  check := fun c => do
    let before ← utilityState c.state
    asUnit c.args
    let recorded ← utilityOutcome asUnit c.outcome
    return decideGraph (S := ShimState) (V := Unit) (U := Empty) (T := ShimTerminal)
      (log.sol_log_compute_units_run sdkLogIndex before ())
      (sdkLogStep before (.computeUnits .solana)) (fun _ => Iff.rfl) recorded unitOutcomeJson

theorem legacy115Rent_decider_rejects :
    @decide
      ((sysvar.rent.Rent.get_legacy_error_table_contract.contract
      (legacyIndexOf (legacyUninitialized (V := Sysvar.Rent300)))).requires ⟨⟨[], []⟩, []⟩ ())
      (legacyReadyDec .program115 ⟨.typed .rent, some Sysvar.defaultRent300⟩ legacyUninitialized
        ⟨⟨[], []⟩, []⟩) = false := by decide

end SolanalibTest.Conformance.Library.Families.Utilities.Syscalls
