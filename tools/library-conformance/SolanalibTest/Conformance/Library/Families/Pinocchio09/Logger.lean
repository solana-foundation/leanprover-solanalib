/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Pinocchio09.Common
import Solanalib.Specs.Core.FixedLoggerReference
import Solanalib.Specs.PinocchioLog.Logger

/-!
The driver observes only the initialized prefix; it never reads uninitialized
spare logger storage. The model retains that storage and callback writes, while
the native projection forgets unobservable tail bytes. Scripted callbacks and
destructors preserve their actual unwind, terminal and event order.
-/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.Pinocchio09.Logger

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.FixedLogger
open AccountsV1

abbrev World := Buffer × Aux

def stateJson (capacity : Nat) (world : World) : Json :=
  withAux (Json.mkObj [("bytes", bytesJson world.1.bytes), ("len", toJson world.1.len),
    ("capacity", toJson capacity)]) world.2

def beforeOf (capacity : Nat) (j : Json) : Result World := do
  unless (← natField j "capacity") = capacity do throw "capacity differs from BUFFER"
  let bytes ← asBytes (← field j "bytes")
  return (⟨bytes.map some ++ List.replicate (capacity - bytes.length) none, ← natField j
    "len"⟩, ←
    auxOf j)

instance bufferValidDec (capacity : Nat) (buffer : Buffer) : Decidable (buffer.Valid capacity) := by
  unfold Buffer.Valid initialized
  infer_instance

inductive Operand where
  | bytes (value : Solanalib.Runtime.Bytes)
  | unsigned (value : UInt64)
  | probe (writePanics dropPanics terminal : Bool)

def operandOf (kind : String) (j : Json) : Result Operand := do
  unless (← strField j "kind") = kind do throw "value kind differs from T"
  match kind with
  | "str" => return .bytes (← asBytes (← field j "value"))
  | "u64" => return .unsigned (UInt64.ofNat (← asUInt 64 (← field j "value")))
  | "probe" => return .probe (← boolField j "write_panics") (← boolField j "drop_panics") (←
    boolField j "terminal")
  | _ => throw s!"unknown operand {kind}"

def copyWrite (before : List (Option UInt8) × Aux) (raw : Solanalib.Runtime.Bytes) (copy : Bool) :
    Outcome (List (Option UInt8) × Aux) Nat String Json :=
  let bytes := formatBytes before.1.length raw
  let aux := if copy && !raw.isEmpty then
    before.2.record (Json.mkObj [("syscall", "sol_memcpy_"), ("bytes", bytesJson (raw.take
      before.1.length))])
    else before.2
  .returned bytes.length (bytes.map some ++ before.1.drop bytes.length, aux)

def probeWrite (before : List (Option UInt8) × Aux) (panics terminal : Bool) :
    Outcome (List (Option UInt8) × Aux) Nat String Json :=
  let after := (before.1.set 0 (some 42), before.2.event "write")
  if terminal then .terminated (Json.mkObj [("reason", "sol_panic_"),
    ("detail", Json.mkObj [("file", bytesJson (Log.utf8Bytes "formatter")),
      ("line", toJson (7 : Nat)), ("column", toJson (3 : Nat))]), ("syscalls", before.2.syscalls)])
  else if panics then .unwound "formatter panic" after
  else .returned (min 1 before.1.length) after

def writeStep (before : List (Option UInt8) × Aux) : Operand →
    Outcome (List (Option UInt8) × Aux) Nat String Json
  | .bytes value => copyWrite before value true
  | .unsigned value => copyWrite before (Log.utf8Bytes (toString value.toNat)) (value != 0)
  | .probe panics _ terminal => probeWrite before panics terminal

def WriteLaw (before : List (Option UInt8) × Aux) :
    Outcome (List (Option UInt8) × Aux) Nat String Json → Prop
  | .returned count after => after.1.length = before.1.length ∧ count ≤ before.1.length ∧
      initialized (after.1.take count)
  | .unwound _ after => after.1.length = before.1.length
  | .terminated _ => True

theorem copyWrite_law (before : List (Option UInt8) × Aux) (raw : Solanalib.Runtime.Bytes) (copy :
  Bool) :
    WriteLaw before (copyWrite before raw copy) := by
  have safe := renderedWrite_safe (fun (_ : Unit) => raw) (before.1, ()) () _ rfl
  exact safe

theorem probeWrite_law (before : List (Option UInt8) × Aux) (panics terminal : Bool) :
    WriteLaw before (probeWrite before panics terminal) := by
  unfold probeWrite
  split
  · trivial
  · split
    · simp [WriteLaw]
    · simp only [WriteLaw, List.length_set]
      refine ⟨trivial, Nat.min_le_right _ _, ?_⟩
      cases before.1 <;> simp [initialized]

theorem writeSafe : WriterSafe (Callback.ofFunction writeStep) := by
  rintro before value produced called
  cases called
  cases value with
  | bytes value => exact copyWrite_law before value true
  | unsigned value => exact copyWrite_law before (Log.utf8Bytes (toString value.toNat)) (value != 0)
  | probe panics drop terminal =>
    rcases before with ⟨bytes, aux⟩
    cases bytes <;> cases panics <;> cases terminal <;> simp [writeStep, probeWrite, initialized]

def dropStep (before : Aux) : Operand → Outcome Aux Unit String Json
  | .probe _ panics _ =>
    let after := before.event "drop"
    if panics then .unwound "operand drop" after else .returned () after
  | _ => .returned () before

def doubleStep (before : Aux) (first later : String) : Json :=
  Json.mkObj [("reason", "double unwind"), ("first", toJson first), ("later", toJson later),
    ("syscalls", before.syscalls)]

abbrev appendIndex (capacity : Nat) : AppendIndex where
  capacity := capacity
  Ref := Nat
  Value := Operand
  Aux := Aux
  Unwind := String
  Terminal := Json
  write := Callback.ofFunction writeStep
  writerSafe := writeSafe
  drop := Callback.ofFunction dropStep
  double := fun before first later terminal => terminal = doubleStep before first later

def computed (capacity : Nat) (before : World) (args : Nat × Operand) : Outcome World Nat String
  Json :=
  appendComputed (appendIndex capacity) writeStep dropStep doubleStep before args

theorem append_graph (capacity : Nat) (before : World) (args : Nat × Operand)
    (outcome : Outcome World Nat String Json) :
    Solanalib.Specs.PinocchioLog.logger.Logger.append_run (appendIndex capacity) before args
      outcome ↔
      some (computed capacity before args) = some outcome := by
  change appendAt (appendIndex capacity) before args outcome ↔ _
  rw [FixedLogger.append_graph (appendIndex capacity) writeStep dropStep doubleStep rfl rfl
    (by intros; rfl)]
  exact ⟨fun h => congrArg some h.symm, fun h => (Option.some.inj h).symm⟩

def appendChecker (capacity : Nat) (kind type : String) : Checker where
  function := "pinocchio_log::logger::Logger::<BUFFER>::append"
  generics := [("BUFFER", toString capacity), ("T", type)]
  reference := "Solanalib.Specs.PinocchioLog.logger.Logger.append_run"
  decides := ["Solanalib.Specs.PinocchioLog.logger.Logger.append_run"]
  decidesRequires := ["Solanalib.Specs.PinocchioLog.logger.Logger.append_run"]
  check := fun c => do
    let before ← beforeOf capacity c.state
    let args := (← natField c.args "receiver", ← operandOf kind c.args)
    return withReady (@decide ((Solanalib.Specs.PinocchioLog.logger.Logger.append_contract.contract
      (appendIndex capacity)).requires before args)
      (bufferValidDec capacity before.1)) <|
      observe (Solanalib.Specs.PinocchioLog.logger.Logger.append_run (appendIndex capacity) before
        args)
        (some (computed capacity before args)) (append_graph capacity before args)
        (outcomeJson (fun (value : Nat) => toJson value) (stateJson capacity)) c.outcome

def defaultChecker (capacity : Nat) : Checker where
  function := "<pinocchio_log::logger::Logger<BUFFER> as core::default::Default>::default"
  generics := [("BUFFER", toString capacity)]
  reference := "Solanalib.Specs.PinocchioLog.logger.Logger.default_run"
  decides := ["Solanalib.Specs.PinocchioLog.logger.Logger.default_run"]
  check := fun c => do
    asUnit c.state
    asUnit c.args
    let run : Unit → Unit → Buffer × Unit := fun before _ => (Buffer.empty capacity, before)
    return observe (Solanalib.Specs.PinocchioLog.logger.Logger.default_run ⟨capacity⟩ () ())
      (some (.returned (Buffer.empty capacity) ())) (returnsOf_graph run () ())
      (returnJson (fun buffer _ => stateJson capacity (buffer, Aux.empty)) (fun _ => Json.null))
        c.outcome

def sinkStep (before : Aux) (bytes : Solanalib.Runtime.Bytes) : Outcome Aux Unit String Json :=
  .returned () (before.record (Json.mkObj [("syscall", "sol_log_"), ("bytes", bytesJson bytes)]))

abbrev logIndex (capacity : Nat) : LogIndex :=
  ⟨capacity, Aux, String, Json, Callback.ofFunction sinkStep⟩

def logComputed (capacity : Nat) (before : World) : Outcome World Unit String Json :=
  liftSinkOutcome (logIndex capacity) before.1 (sinkStep before.2 before.1.bytes)

theorem log_graph (capacity : Nat) (before : World) (outcome : Outcome World Unit String Json) :
    Solanalib.Specs.PinocchioLog.logger.Logger.log_run (logIndex capacity) before () outcome ↔
      some (logComputed capacity before) = some outcome := by
  change (∃ produced, sinkStep before.2 before.1.bytes = produced ∧
    outcome = liftSinkOutcome (logIndex capacity) before.1 produced) ↔ _
  simp only [logComputed, Option.some.injEq]
  constructor
  · rintro ⟨_, called, finished⟩; cases called; exact finished.symm
  · intro finished; exact ⟨_, rfl, finished.symm⟩

def logChecker (capacity : Nat) : Checker where
  function := "pinocchio_log::logger::Logger::<BUFFER>::log"
  generics := [("BUFFER", toString capacity)]
  reference := "Solanalib.Specs.PinocchioLog.logger.Logger.log_run"
  decides := ["Solanalib.Specs.PinocchioLog.logger.Logger.log_run"]
  decidesRequires := ["Solanalib.Specs.PinocchioLog.logger.Logger.log_run"]
  check := fun c => do
    let before ← beforeOf capacity c.state
    asUnit c.args
    return withReady (@decide ((Solanalib.Specs.PinocchioLog.logger.Logger.log_contract.contract
      (logIndex capacity)).requires before ())
      (bufferValidDec capacity before.1)) <|
      observe (Solanalib.Specs.PinocchioLog.logger.Logger.log_run (logIndex capacity) before ())
        (some (logComputed capacity before)) (log_graph capacity before)
        (outcomeJson (fun _ => Json.null) (stateJson capacity)) c.outcome

def checkers : List Checker :=
  [0, 3, 200].map defaultChecker ++
  [0, 1, 2, 3, 4, 200].map (fun n => appendChecker n "str" "&str") ++
  [0, 1, 5, 200].map (fun n => appendChecker n "u64" "u64") ++
  [0, 3].map (fun n => appendChecker n "probe" "Probe") ++
  [0, 2, 200].map logChecker

end SolanalibTest.Conformance.Library.Families.Pinocchio09.Logger
