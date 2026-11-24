/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AddressProfiles.Shim
import Solanalib.Specs.Core.AddressBorsh

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.AddressProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Borsh (IoError ErrorKind)
open Address (pubkey pubkeyJson)

namespace Io

inductive ReadMode where
  | ok | shortOk | eof | other | unwind | eofDrop | eofDropUnwind
  deriving DecidableEq

def ReadMode.count : ReadMode → Nat
  | .ok => 32
  | .shortOk => 5
  | .eof | .eofDrop | .eofDropUnwind => 7
  | .other => 3
  | .unwind => 4

def ReadMode.name : ReadMode → String
  | .ok => "ok"
  | .shortOk => "short_ok"
  | .eof => "eof"
  | .other => "other"
  | .unwind => "unwind"
  | .eofDrop => "eof_drop"
  | .eofDropUnwind => "eof_drop_unwind"

def ReadMode.ownsPayload : ReadMode → Bool
  | .eofDrop | .eofDropUnwind => true
  | _ => false

structure Reader where
  input : Solanalib.Runtime.Bytes
  position : Nat
  exactCalls : Nat
  readCalls : Nat
  initial : Solanalib.Runtime.Bytes
  mode : ReadMode
  drops : Nat
  deriving DecidableEq

inductive WriteMode where
  | ok | error | unwind
  deriving DecidableEq

def WriteMode.name : WriteMode → String
  | .ok => "ok"
  | .error => "error"
  | .unwind => "unwind"

structure Writer where
  written : Solanalib.Runtime.Bytes
  calls : List Solanalib.Runtime.Bytes
  writeCalls : Nat
  mode : WriteMode
  deriving DecidableEq

/-- Exactly the overridden read_exact of the recording reader. The generic address
model invokes this whole boundary once, including ordinary partial errors. -/
def readProvider (before : Reader) (initial : Value) :
    Outcome Reader Borsh.ReadReply String Empty :=
  let count := before.mode.count
  let buffer := Shim.overwrite initial ((before.input.drop before.position).take count)
  let after : Reader := { before with
    position := before.position + count
    exactCalls := before.exactCalls + 1
    initial := initial.bytes }
  match before.mode with
  | .ok | .shortOk => .returned ⟨.ok (), buffer⟩ after
  | .eof => .returned ⟨.error ⟨⟨"UnexpectedEof"⟩, "reader stopped"⟩, buffer⟩ after
  | .other => .returned ⟨.error ⟨⟨"Other"⟩, "chosen read error"⟩, buffer⟩ after
  | .eofDrop | .eofDropUnwind =>
    .returned ⟨.error ⟨⟨"UnexpectedEof"⟩, "owned EOF payload"⟩, buffer⟩ after
  | .unwind => .unwound "chosen read unwind" after

/-- Only destruction of the actual driver-local owned EOF payload updates this
counter. Destroying the replacement or another error cannot invoke that payload.
The original recording modes retain their exact observations. -/
def dropErrorProvider (before : Reader) (error : IoError) : Outcome Reader Unit String Empty :=
  if before.mode.ownsPayload && error.kind.debugName == "UnexpectedEof" &&
      error.message == "owned EOF payload" then
    let after := { before with drops := before.drops + 1 }
    match before.mode with
    | .eofDropUnwind => .unwound "EOF payload drop" after
    | _ => .returned () after
  else .returned () before

theorem replacement_destruction_cannot_run_owned_payload_drop (before : Reader) (kind : ErrorKind) :
    dropErrorProvider before ⟨kind, Solanalib.Specs.Core.Borsh.unexpectedLengthMessage⟩ =
      .returned () before := by
  simp [dropErrorProvider, Solanalib.Specs.Core.Borsh.unexpectedLengthMessage]

theorem owned_payload_unwind_follows_exactly_one_drop :
    dropErrorProvider ⟨[], 0, 0, 0, [], .eofDropUnwind, 4⟩
      ⟨⟨"UnexpectedEof"⟩, "owned EOF payload"⟩ =
      .unwound "EOF payload drop" ⟨[], 0, 0, 0, [], .eofDropUnwind, 5⟩ := rfl

abbrev readIndex : Borsh.ReadIndex where
  State := Reader
  Unwind := String
  Terminal := Empty
  readExact := Callback.ofFunction readProvider
  -- Allocations are successful in this observer; allocator state is not in Reader.
  constructError := Callback.ofFunction fun before _ => .returned () before
  dropError := Callback.ofFunction dropErrorProvider
  -- The pinned rustc retains the already constructed return place on this unwind.
  unwindReturnPlace := Callback.ofFunction fun before _ => .returned () before
  doubleUnwind := fun _ _ _ _ => False

def readEval (kind : ErrorKind) (before : Reader) : Outcome Reader (Except IoError Value) String
  Empty :=
  Outcome.bind (readProvider before .zero) fun reply after =>
    match reply.result with
    | .ok () => .returned (.ok reply.buffer) after
    | .error error =>
      if error.kind.debugName = "UnexpectedEof" then
        Outcome.map (fun () => .error ⟨kind, Solanalib.Specs.Core.Borsh.unexpectedLengthMessage⟩)
          (dropErrorProvider after error)
      else .returned (.error error) after

theorem readRun_evaluated (kind : ErrorKind) (before : Reader) (args : Unit)
    (o : Outcome Reader (Except IoError Value) String Empty) :
    Borsh.readRun kind readIndex before args o ↔ readEval kind before = o := by
  cases before with
  | mk input position exactCalls readCalls initial mode drops =>
    cases mode <;>
      simp [Borsh.readRun, Borsh.readAfter, Borsh.mapReadErrorRun, readIndex, readEval,
        readProvider, dropErrorProvider, ReadMode.count, ReadMode.ownsPayload,
        Callback.bind, Callback.map, Callback.ofFunction, Owned.protect, Owned.onUnwind,
        Owned.cleanup, Outcome.bind, Outcome.map] <;> exact eq_comm

def writeProvider (before : Writer) (bytes : Solanalib.Runtime.Bytes) : Outcome Writer (Except
  IoError Unit) String Empty :=
  let count := if before.mode = .ok then bytes.length else 3
  let after : Writer := { before with
    written := before.written ++ bytes.take count
    calls := before.calls ++ [bytes] }
  match before.mode with
  | .ok => .returned (.ok ()) after
  | .error => .returned (.error ⟨⟨"WriteZero"⟩, "chosen partial write"⟩) after
  | .unwind => .unwound "chosen write unwind" after

abbrev writeIndex : Solanalib.Specs.Core.Borsh.WriterIndex :=
  ⟨Writer, String, Empty, Callback.ofFunction writeProvider⟩

theorem serializeRun_evaluated (before : Writer) (value : Value)
    (o : Outcome Writer (Except IoError Unit) String Empty) :
    Borsh.serializeRun writeIndex before value o ↔ writeProvider before value.bytes = o :=
  Borsh.serializeRun_iff writeIndex before value o

def readMode (j : Json) : Result ReadMode := do
  match ← j.getStr? with
  | "ok" => pure .ok
  | "short_ok" => pure .shortOk
  | "eof" => pure .eof
  | "other" => pure .other
  | "unwind" => pure .unwind
  | "eof_drop" => pure .eofDrop
  | "eof_drop_unwind" => pure .eofDropUnwind
  | mode => throw s!"unknown reader mode {mode}"

def reader (j : Json) : Result Reader := do
  let mode ← readMode (← field j "mode")
  let drops ← if mode.ownsPayload then asUInt 64 (← field j "drops") else pure 0
  pure ⟨← asBytes (← field j "input"), ← asUInt 64 (← field j "position"),
    ← asUInt 64 (← field j "exact_calls"), ← asUInt 64 (← field j "read_calls"),
    ← asBytes (← field j "initial"), mode, drops⟩

def readerJson (r : Reader) : Json := Json.mkObj (
  [("input", bytesJson r.input), ("position", toJson r.position), ("exact_calls", toJson
    r.exactCalls),
    ("read_calls", toJson r.readCalls), ("initial", bytesJson r.initial), ("mode", Json.str
      r.mode.name)] ++
  if r.mode.ownsPayload then [("drops", toJson r.drops)] else [])

def writeMode (j : Json) : Result WriteMode := do
  match ← j.getStr? with
  | "ok" => pure .ok
  | "error" => pure .error
  | "unwind" => pure .unwind
  | mode => throw s!"unknown writer mode {mode}"

def writer (j : Json) : Result Writer := do
  pure ⟨← asBytes (← field j "written"), ← Shim.bytesList (← field j "calls"),
    ← asUInt 64 (← field j "write_calls"), ← writeMode (← field j "mode")⟩

def writerJson (w : Writer) : Json := Json.mkObj [
  ("written", bytesJson w.written), ("calls", Shim.bytesListJson w.calls),
  ("write_calls", toJson w.writeCalls), ("mode", Json.str w.mode.name)]

def ioError (j : Json) : Result IoError := do
  pure ⟨⟨← (← field j "kind").getStr?⟩, ← (← field j "message").getStr?⟩

def ioErrorJson (e : IoError) : Json :=
  Json.mkObj [("kind", Json.str e.kind.debugName), ("message", Json.str e.message)]

def ioResult {V : Type} (value : Json → Result V) (j : Json) : Result (Except IoError V) :=
  match j.getObjVal? "ok" with
  | .ok j => do pure (.ok (← value j))
  | .error _ => do pure (.error (← ioError (← field j "err")))

def ioResultJson {V : Type} (render : V → Json) : Except IoError V → Json
  | .ok value => Json.mkObj [("ok", render value)]
  | .error e => Json.mkObj [("err", ioErrorJson e)]

def outcomeJson {S V : Type} (value : V → Json) (state : S → Json) : Outcome S V String Empty → Json
  | .returned v s => returnedJson (value v) (state s)
  | .unwound reason s => Json.mkObj [("exit", "unwound"), ("reason", Json.str reason), (
    "state",
    state s)]
  | .terminated impossible => nomatch impossible

def readerChecker (function reference : String) (kind : ErrorKind)
    (run : Reader → Unit → Outcome Reader (Except IoError Value) String Empty → Prop)
    (graph : ∀ before args o, run before args o ↔ readEval kind before = o) : Checker where
  function := function
  generics := []
  reference := reference
  decides := [reference]
  check := fun c => do
    let before ← reader c.state
    unless before.position + before.mode.count ≤ before.input.length && before.exactCalls + 1 <
      2^64 &&
        (!before.mode.ownsPayload || before.drops + 1 < 2^64) do
      throw "reader script would exceed its input or counter"
    let args ← asUnit c.args
    let parsed ← parseOutcome (ioResult pubkey) reader some noReason c.outcome
    pure (decideGraph (run before args) (readEval kind before) (graph before args) parsed
      (outcomeJson (ioResultJson pubkeyJson) readerJson))

def writerChecker (function reference : String)
    (run : Writer → Value → Outcome Writer (Except IoError Unit) String Empty → Prop)
    (graph : ∀ before value o, run before value o ↔ writeProvider before value.bytes = o) : Checker
      where
  function := function
  generics := []
  reference := reference
  decides := [reference]
  check := fun c => do
    let before ← writer c.state
    let value ← Address.selfArg c.args
    let parsed ← parseOutcome (ioResult asUnit) writer some noReason c.outcome
    pure (decideGraph (run before value) (writeProvider before value.bytes) (graph before value)
      parsed
      (outcomeJson (ioResultJson (fun _ => Json.null)) writerJson))

def legacyResult (j : Json) : Result (Except IoError Value × Solanalib.Runtime.Bytes) :=
  Address.pairOf (ioResult pubkey) asBytes j

def legacyResultJson (result : Except IoError Value × Solanalib.Runtime.Bytes) : Json :=
  Json.arr #[ioResultJson pubkeyJson result.1, bytesJson result.2]

end Io
end SolanalibTest.Conformance.Library.Families.AddressProfiles
