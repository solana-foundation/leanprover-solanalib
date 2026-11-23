/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.Input
import SolanalibTest.Conformance.Library.Families.Anchor.Graph

/-!
Native observations retain the actual request, aliases, cell effects and Rc
counts. Allocation slots are model resources; the native fixture additionally
checks the allocation and release counts of its nonempty, preallocated vectors.
Terminal exits have no after-state. Their request/getter observations are
computed from the actual finite prefixes, never a substitute successful run.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTokenOperations
open SolanalibTest.Conformance.Library.Borsh (listJson)

abbrev Counts := List ((AccountInfoRc.Field × Borrow.Handle) × Nat)

def countsJson (counts : Counts) (infos : List AccountInfo.Value) : Json :=
  listJson (fun info => listJson (fun value => (value.map toJson).getD .null)
    [counts.lookup (.lamports, info.lamports), counts.lookup (.data, info.data)]) infos

def instructionJson (instruction : Solanalib.Runtime.CpiInstruction) : Json :=
  Json.mkObj [("program", bytesJson instruction.programId.bytes),
    ("metas", listJson (fun entry => Json.mkObj [("key", bytesJson entry.key.bytes),
      ("signer", toJson (entry.signerByte == 1)),
      ("writable", toJson (entry.writableByte == 1))]) instruction.metas),
    ("data", bytesJson instruction.data)]

def callJson (identities : List AccountInfo.Value) (call : Reference.RecordedCall) : Json :=
  Json.mkObj [("instruction", instructionJson call.instruction),
    ("accounts", listJson (fun info =>
      ((identities.findIdx? fun known => known.data == info.data).map toJson).getD .null)
        call.accounts),
    ("signers", listJson (listJson bytesJson) call.signers),
    ("seed_reference", (call.seedReference.map toJson).getD .null),
    ("counts", countsJson call.counts call.accounts)]

def getterJson (identities : List AccountInfo.Value) (getter : Reference.GetterObservation) : Json
  :=
  Json.mkObj [("counts", countsJson getter.counts identities),
    ("metas_live", toJson ((getter.metas.current 0).isSome)),
    ("data_live", toJson ((getter.bytes.current 0).isSome))]

def legacyErrorJson (strings : List (Option String)) : ProgramErrorOwned.Value Nat → Json
  | .custom code => Json.mkObj [("custom", toJson code.toNat)]
  | .incorrectProgramId => "incorrect_program_id"
  | .invalidArgument => "invalid_argument"
  | .invalidInstructionData => "invalid_instruction_data"
  | .borshIoError resource => Json.mkObj [("borsh", ((strings[resource]?.join).map toJson).getD
    .null)]
  | other => Json.mkObj [("unselected_error", toJson (reprStr other))]

def modernErrorJson : ProgramError.Value → Json
  | .custom code => Json.mkObj [("custom", toJson code.toNat)]
  | .incorrectProgramId => "incorrect_program_id"
  | .invalidArgument => "invalid_argument"
  | .invalidInstructionData => "invalid_instruction_data"
  | other => Json.mkObj [("unselected_error", toJson (reprStr other))]

def programErrorJson (release : Release) (strings : List (Option String)) : release.ProgramError
  Nat → Json :=
  match release with
  | .v027 | .v029 | .v0321 => legacyErrorJson strings
  | .v102 | .v112 => modernErrorJson

def errorJson {binding : Binding} (prepared : Prepared binding)
    (state : Reference.State binding.release) (error : Error (Reference.types binding
      prepared.script)) : Json :=
  match AnchorErrorOperations.currentPayload binding.release.storage
      (Reference.errors prepared.script) state error with
  | some (.program payload) => Json.mkObj [
      ("program_error", programErrorJson binding.release state.strings payload.error),
      ("origin", (payload.origin.map fun value => toJson (reprStr value)).getD .null),
      ("compared", (payload.compared.map fun value => toJson (reprStr value)).getD .null),
      ("boxed", toJson (binding.release.storage == .boxed))]
  | _ => Json.mkObj [("missing_program_payload", true)]

def sameString {binding : Binding} (prepared : Prepared binding)
    (final : Exit (Reference.types binding prepared.script)) : Json :=
  match Reference.programErrorOf prepared.script final with
  | none => .null
  | some error =>
      match Reference.programStrings binding.release error with
      | [] => .null
      | strings => toJson (strings == [0])

def freedJson {release : Release} (state : Reference.State release) : Json :=
  listJson toJson (state.events.filterMap fun event => match event with
    | .release .metas 0 => if state.calls.isEmpty then none else some "metas"
    | .release .bytes 0 => if state.calls.isEmpty then none else some "data"
    | .release .remaining 0 => some "remaining"
    | _ => none)

def returnedResource {release : Release} (script : Reference.Script release)
    (state : Reference.State release) : Option Nat :=
  match script.returned, state.getters.head? with
  | .present _ _, some getter => some getter.bytes.length
  | _, _ => none

def conversionOrder {release : Release} (state : Reference.State release) (returned : Nat) : Json :=
  match state.events.findIdx? (· == .release .bytes returned),
      state.events.findIdx? (fun event => match event with | .newBox _ => true | _ => false) with
  | some released, some converted => toJson (decide (released < converted))
  | _, _ => .null

def heapJson {release : Release} (state : Reference.State release) : Json :=
  Json.mkObj [
    ("allocations", toJson (state.bytes.length + state.metas.length + state.extensions.length +
      state.boxes.length)),
    ("frees", toJson (state.bytes.count none + state.metas.count none + state.extensions.count none
      +
      state.remaining.count none + state.boxes.count none)),
    ("live", toJson (state.boxes.filterMap id).length)]

def stateJson {binding : Binding} (prepared : Prepared binding)
    (final : Exit (Reference.types binding prepared.script)) (state : Reference.State
      binding.release)
    (normal : Bool) : Json :=
  Json.mkObj [
    ("cells", listJson (fun info => Json.mkObj [
      ("lamports", ((state.lamports.lookup info.lamports).map toJson).getD .null),
      ("data", ((state.dataCells.lookup info.data).map bytesJson).getD .null)])
        prepared.identities),
    ("counts", countsJson state.counts prepared.identities),
    ("calls", listJson (callJson prepared.identities) state.calls),
    ("getters", listJson (getterJson prepared.identities) state.getters),
    ("freed", freedJson state),
    ("fresh_boxes", toJson (state.boxes.filterMap id).length),
    ("same_string", sameString prepared final),
    ("heap", if normal then heapJson state else .null),
    ("returned_freed", ((returnedResource prepared.script state).map
      fun resource => toJson ((state.bytes.current resource).isNone)).getD .null),
    ("conversion_after_return_free", ((returnedResource prepared.script state).map
      (conversionOrder state)).getD .null)]

structure InvocationPrefix (binding : Binding) (script : Reference.Script binding.release) where
  instruction : InstructionOwner (Reference.types binding script)
  accounts : List AccountInfo.Value
  state : Reference.State binding.release

/-- This is the real builder and preparation point, before the opaque call. -/
def invocationPrefix {binding : Binding} (prepared : Prepared binding) :
    Option (InvocationPrefix binding prepared.script) := do
  let .returned (.ok instruction) built ←
    Execution.buildFn (Reference.functions binding prepared.script) prepared.before
      (argsConstruction prepared.args)
    | none
  let .returned accounts state ←
    Execution.prepareFn (Reference.functions binding prepared.script) prepared.args built | none
  pure ⟨instruction, accounts, state⟩

/-- Prefix computation is connected to both actual relations, not to a
successful complete wrapper outcome. -/
theorem invocationPrefix_actual {binding : Binding} (prepared : Prepared binding)
    (point : InvocationPrefix binding prepared.script) (found : invocationPrefix prepared = some
      point) :
    ∃ built, build (Reference.types binding prepared.script).builder prepared.before
        (argsConstruction prepared.args) (.returned (.ok point.instruction) built) ∧
      prepareAccounts (Reference.types binding prepared.script) prepared.args built ()
        (.returned point.accounts point.state) := by
  unfold invocationPrefix at found
  cases built : Execution.buildFn (Reference.functions binding prepared.script) prepared.before
      (argsConstruction prepared.args) with
  | none => simp [built] at found
  | some outcome =>
    cases outcome with
    | unwound _ _ | terminated _ => simp [built] at found
    | returned value state =>
      cases value with
      | error _ => simp [built] at found
      | ok instruction =>
        rw [built] at found
        change ((Execution.prepareFn (Reference.functions binding prepared.script) prepared.args
          state).bind
          (fun result => match result with
            | .returned accounts after => some ⟨instruction, accounts, after⟩
            | _ => none)) = some point at found
        cases ready : Execution.prepareFn (Reference.functions binding prepared.script)
          prepared.args state with
        | none => simp [ready] at found
        | some result =>
          cases result with
          | unwound _ _ | terminated _ => simp [ready] at found
          | returned accounts after =>
            rw [ready] at found
            change some ⟨instruction, accounts, after⟩ = some point at found
            have found := Option.some.inj found
            cases found
            exact ⟨state,
              (Execution.build_graph _ (Reference.graphs binding prepared.script) _ _ _).mpr built,
              (Execution.prepare_graph _ (Reference.graphs binding prepared.script) _ _ _).mpr
                ready⟩

/-- A terminal provider logs its input before it exits. Getter entry is reached
through the actual normal sizeInvoke point, including the destruction of the array. -/
def terminalDetail {binding : Binding} (prepared : Prepared binding) (reason : Nat) : Json :=
  ((invocationPrefix prepared).bind fun point => do
    let call ← request (Reference.types binding prepared.script) point.state prepared.args
      point.instruction point.accounts
    if (show Nat from reason) = 71 then
      pure (Json.mkObj [("calls", listJson (callJson prepared.identities)
        (point.state.calls ++ [⟨call.instruction, call.accounts, call.signers,
          seedReference prepared.args, point.state.counts⟩])),
        ("getters", listJson (getterJson prepared.identities) point.state.getters)])
    else if (show Nat from reason) = 91 then
      let .returned (.ok ()) after ← Execution.sizeInvokeFn (Reference.functions binding
        prepared.script)
        prepared.args point.instruction point.accounts point.state | none
      pure (Json.mkObj [("calls", listJson (callJson prepared.identities) after.calls),
        ("getters", listJson (getterJson prepared.identities)
          (after.getters ++ [⟨after.counts, after.bytes, after.metas⟩]))])
    else none).getD .null

def outcomeJson {binding : Binding} (prepared : Prepared binding) :
    Exit (Reference.types binding prepared.script) → Json
  | .returned value state =>
      let final := Outcome.returned value state
      returnedJson (exceptJson (errorJson prepared state)
        (fun value => match value with | .unit => .null | .size size => toJson size.toNat) value)
        (stateJson prepared final state true)
  | .unwound reason state => Json.mkObj [("exit", "unwound"),
      ("reason", if (show Nat from reason) = 23 then "opaque invoke unwind" else if (show Nat from
        reason) = 29 then "opaque getter unwind"
        else toJson (show Nat from reason)),
      ("state", stateJson prepared (.unwound reason state) state false)]
  | .terminated reason => Json.mkObj [("exit", "terminated"),
      ("reason", if (show Nat from reason) = 71 then "opaque invoke terminal" else if (show Nat
        from reason) = 91 then "opaque getter terminal"
        else toJson (show Nat from reason)),
      ("detail", terminalDetail prepared reason), ("syscalls", Json.arr #[])]

end SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations
