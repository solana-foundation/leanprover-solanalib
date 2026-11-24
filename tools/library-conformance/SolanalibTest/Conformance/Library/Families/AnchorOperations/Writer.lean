/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Common
import SolanalibTest.Conformance.Library.BorshCommon
import Solanalib.Specs.AnchorLang.bpf_writer

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations.Writer

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorCodec
open SolanalibTest.Conformance.Library.Families.Anchor

structure State where
  copies : List CopyRequest := []
  errors : List Borsh.IoError := []

def copied (before : State) (request : CopyRequest) : Outcome State Unit Empty Empty :=
  .returned () { before with copies := before.copies ++ [request] }

def errorCreated (before : State) (error : Borsh.IoError) : Outcome State Nat Empty Empty :=
  .returned before.errors.length { before with errors := before.errors ++ [error] }

abbrev types : WriteTypes := ⟨State, Nat, Empty, Callback.ofFunction copied, Callback.ofFunction
  errorCreated⟩

def copyState (step : WriteStep) (before : State) : State :=
  match step.copy with
  | none => before
  | some request => { before with copies := before.copies ++ [request] }

theorem copyGraph (step : WriteStep) (before : State) :
    PGraph (copyStep types step before ()) (some (.returned () (copyState step before))) := by
  unfold copyStep copyState
  cases step.copy with
  | none => exact PGraph.eq_left _
  | some request => exact PGraph.ofFunction copied before request

def runFn (before : WriteState State) (input : Solanalib.Runtime.Bytes) :
    Outcome (WriteState State) (Except Nat Unit) Empty Empty :=
  let step := writeStep before.writer input
  let ambient := copyState step before.ambient
  if step.count = input.length then .returned (.ok ()) ⟨step.writer, ambient⟩
  else .returned (.error ambient.errors.length)
    ⟨step.writer, { ambient with errors := ambient.errors ++ [Borsh.writeZeroError] }⟩

theorem runGraph (before : WriteState State) (input : Solanalib.Runtime.Bytes) :
    PGraph (Solanalib.Specs.AnchorLang.bpf_writer.BpfWriter.write_all_run types before input)
      (some (runFn before input)) := by
  intro outcome
  change (∃ copied, copyStep types (writeStep before.writer input) before.ambient () copied ∧ _) ↔ _
  have copyExact (result : Outcome State Unit Empty Empty) :
      copyStep types (writeStep before.writer input) before.ambient () result ↔
        Outcome.returned () (copyState (writeStep before.writer input) before.ambient) = result :=
    by
      simpa only [Option.some.injEq] using
        copyGraph (writeStep before.writer input) before.ambient result
  simp only [copyExact, exists_eq_left', runFn]
  split
  · exact (PGraph.eq_left _ outcome)
  · simp only [Callback.map, Owned.Focus.lift, types, Callback.ofFunction, errorCreated,
      exists_eq_left', ambientFocus, Owned.Focus.liftOutcome, Outcome.map]
    exact (PGraph.eq_right _ outcome)

def stateJson (state : WriteState State) : Json := Json.mkObj [
  ("writer", Json.mkObj [("bytes", bytesJson state.writer.bytes), ("position", toJson
    state.writer.position)]),
  ("syscalls", Json.mkObj [("replies", Json.arr #[]), ("log", listJson (fun request =>
    Json.mkObj [("syscall", "sol_memcpy_"), ("bytes", bytesJson (request.source.take
      request.count))]) state.ambient.copies)])]

def project : Outcome (WriteState State) (Except Nat Unit) Empty Empty → String
  | .returned result state =>
    let value := exceptJson (fun owner => (state.ambient.errors[owner]?).map
      SolanalibTest.Conformance.Library.Borsh.ioErrorJson |>.getD Json.null) (fun _ => Json.null)
        result
    (returnedJson value (stateJson state)).compress
  | .unwound impossible _ | .terminated impossible => nomatch impossible

/-- The `fresh_live` of the recorder includes syscall-JSON bookkeeping allocations.
That count is not an SDK allocator observation, so the checked projection is
the actual writer bytes/cursor, IO result, and complete copy syscall trace. -/
def checker (function : String) : Checker := ofModel function []
    "Solanalib.Specs.AnchorLang.bpf_writer.BpfWriter.write_all_run" fun case => do
  unless (← field case.state "syscalls").compress = emptySyscalls.compress do
    throw "writer fixture requires an empty syscall prefix"
  let writer ← field case.state "writer"
  let before : WriteState State := ⟨⟨← asBytes (← field writer "bytes"), ← natField writer
    "position"⟩, ⟨[], []⟩⟩
  let input ← asBytes (← field case.args "input")
  let stateProjection := fun state => do
    return Json.mkObj [("writer", ← field state "writer"), ("syscalls", ← field state
      "syscalls")]
  let observed ← parseOutcome pure stateProjection (noReason (α := Empty)) (noReason (α := Empty))
    case.outcome
  return decideProjected (Solanalib.Specs.AnchorLang.bpf_writer.BpfWriter.write_all_run types
    before input)
    _ (runGraph before input) project (observed.map fun
      | .returned value state => (returnedJson value state).compress
      | .unwound impossible _ | .terminated impossible => nomatch impossible) (optionJson Json.str)

end SolanalibTest.Conformance.Library.Families.AnchorOperations.Writer
