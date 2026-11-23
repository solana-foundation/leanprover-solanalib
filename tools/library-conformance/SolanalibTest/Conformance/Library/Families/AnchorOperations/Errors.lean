/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.AnchorLang.error_operations
import Solanalib.Specs.AnchorLang.error_codes
import Solanalib.Specs.AnchorLangError.error_operations
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Callbacks

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorErrorOperations
open SolanalibTest.Conformance.Library.Families.Anchor

inductive Version where
  | v027 | v029 | v032 | v102 | v112
  deriving DecidableEq

def Version.storage : Version → Storage
  | .v027 => .inline
  | _ => .boxed

def Version.program : Version → Option ProgramErrorOwned.Release
  | .v027 => some .solana1_15_2
  | .v029 => some .solana1_18_26
  | .v032 => some .programError2_2_2
  | .v102 | .v112 => none

def Version.codes : Version → Array Code
  | .v027 => CodeTables.v0_27_0
  | .v029 => CodeTables.v0_29_0
  | .v032 => CodeTables.v0_32_1
  | .v102 => CodeTables.v1_0_2
  | .v112 => CodeTables.v1_1_2

def codeNameIndex : CodeNameTypes := ⟨Heap, Nat, String, Callback.ofFunction newString⟩

def codeNameRel (version : Version) : Heap → Fin version.codes.size → Outcome Heap Nat Empty String
  → Prop :=
  match version with
  | .v027 => Solanalib.Specs.AnchorLang.error.ErrorCode.name_pre_token_program_checks_run
    codeNameIndex
  | .v029 => Solanalib.Specs.AnchorLang.error.ErrorCode.name_legacy_run codeNameIndex
  | .v032 => Solanalib.Specs.AnchorLang.error.ErrorCode.name_run codeNameIndex
  | .v102 => Solanalib.Specs.AnchorLang.error.ErrorCode.name_account_migration_run codeNameIndex
  | .v112 => Solanalib.Specs.AnchorLangError.ErrorCode.name_run codeNameIndex

def codeNameModel : Version → String
  | .v027 => "Solanalib.Specs.AnchorLang.error.ErrorCode.name_pre_token_program_checks_run"
  | .v029 => "Solanalib.Specs.AnchorLang.error.ErrorCode.name_legacy_run"
  | .v032 => "Solanalib.Specs.AnchorLang.error.ErrorCode.name_run"
  | .v102 => "Solanalib.Specs.AnchorLang.error.ErrorCode.name_account_migration_run"
  | .v112 => "Solanalib.Specs.AnchorLangError.ErrorCode.name_run"

def codeRel (version : Version) : Heap → Fin version.codes.size →
    Outcome Heap (Error version.storage (Program Nat) Nat Nat) Empty String → Prop :=
  match version with
  | .v027 => Solanalib.Specs.AnchorLang.error.Error.from_error_code_inline_run ⟨heapTypes .inline,
    rfl⟩
  | .v029 => Solanalib.Specs.AnchorLang.error.Error.from_legacy_error_code_run ⟨heapTypes .boxed,
    rfl⟩
  | .v032 => Solanalib.Specs.AnchorLang.error.Error.from_error_code_run ⟨heapTypes .boxed, rfl⟩
  | .v102 => Solanalib.Specs.AnchorLang.error.Error.from_error_code_account_migration_run
    ⟨heapTypes .boxed, rfl⟩
  | .v112 => Solanalib.Specs.AnchorLangError.Error.from_error_code_run ⟨heapTypes .boxed, rfl⟩

def codeModel : Version → String
  | .v027 => "Solanalib.Specs.AnchorLang.error.Error.from_error_code_inline_run"
  | .v029 => "Solanalib.Specs.AnchorLang.error.Error.from_legacy_error_code_run"
  | .v032 => "Solanalib.Specs.AnchorLang.error.Error.from_error_code_run"
  | .v102 => "Solanalib.Specs.AnchorLang.error.Error.from_error_code_account_migration_run"
  | .v112 => "Solanalib.Specs.AnchorLangError.Error.from_error_code_run"

theorem codeNameGraph (version : Version) (before : Heap) (code : Fin version.codes.size) :
    PGraph (codeNameRel version before code) (some (newString before version.codes[code].name)) :=
      by
  cases version <;> exact PGraph.ofFunction newString before _

theorem codeGraph (version : Version) (before : Heap) (code : Fin version.codes.size) :
    PGraph (codeRel version before code) (Fn.fromCode version.storage heapFn before
      version.codes[code]) := by
  cases version <;> exact Fn.fromCode_graph heapGraph _ before _

def emptyReason : Empty → Json := fun value => nomatch value

def errorDecision {U : Type} (storage : Storage) (before : Heap)
    (relation : Outcome Heap (Error storage (Program Nat) Nat Nat) U String → Prop)
    (values : List (Outcome Heap (Error storage (Program Nat) Nat Nat) U String))
    (graph : LGraph relation values) (unwind : String → Option U) (reason : U → Json)
    (case : Case) : Result Verdict := do
  let recorded ← parseOutcome pure pure unwind some case.outcome
  return decideProjectedList relation values graph
    (fun outcome => (jsonOutcome reason (project before.strings.length before.boxes.length
      (errorJson storage before.strings.length before.boxes.length) outcome)).compress)
    (recorded.map fun outcome => (jsonOutcome reason outcome).compress) (listJson Json.str)

def codeChecker (version : Version) (function : String)
    (relation : Heap → Fin version.codes.size →
      Outcome Heap (Error version.storage (Program Nat) Nat Nat) Empty String → Prop)
    (graph : ∀ before code, PGraph (relation before code)
      (Fn.fromCode version.storage heapFn before version.codes[code])) : Checker :=
  ofModel function [] (codeModel version) fun case => do
    let before ← asHeap version.program case.state
    let number ← natField case.args "index"
    if bound : number < version.codes.size then
      let code := (⟨number, bound⟩ : Fin version.codes.size)
      return ← errorDecision version.storage before (relation before code) _
        (LGraph.ofPGraph (graph before code)) noReason emptyReason case
    else throw "ErrorCode index is absent from the selected release"

def codeNameChecker (version : Version) (function : String)
    (relation : Heap → Fin version.codes.size → Outcome Heap Nat Empty String → Prop)
    (graph : ∀ before code, PGraph (relation before code)
      (some (newString before version.codes[code].name))) : Checker :=
  ofModel function [] (codeNameModel version) fun case => do
    let before ← asHeap version.program case.state
    let number ← natField case.args "index"
    if bound : number < version.codes.size then
      let code := (⟨number, bound⟩ : Fin version.codes.size)
      let recorded ← parseOutcome pure pure (noReason (α := Empty)) some case.outcome
      return decideProjected (relation before code) _ (graph before code)
        (fun outcome => (jsonOutcome emptyReason (project before.strings.length before.boxes.length
          (fun after owner => Json.mkObj [("text", stringJson after owner),
            ("owned", toJson ((currentString after owner).any (· != "")))]) outcome)).compress)
        (recorded.map fun outcome => (jsonOutcome emptyReason outcome).compress) (optionJson
          Json.str)
    else throw "ErrorCode index is absent from the selected release"

def pubkey (byte : UInt8) : Solanalib.Runtime.Pubkey := ⟨List.replicate 32 byte, by simp⟩

def pubkeysChecker (version : Version) (function : String)
    (relation : Heap → Error version.storage (Program Nat) Nat Nat →
      Outcome Heap (Error version.storage (Program Nat) Nat Nat) Empty String → Prop)
    (graph : ∀ before error, PGraph (relation before error)
      (Fn.withCompared version.storage heapOps heapFn
        (some (.pubkeys (pubkey 3) (pubkey 7))) before error)) : Checker := ofModel function []
    (match version.storage with
      | .inline => "Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_inline_run"
      | .boxed => "Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_pubkeys_run") fun
        case => do
  let before ← asHeap version.program case.state
  let payload ← asPayload version.program Json.getNat? (← field case.args "error")
  let error ← errorArg version.storage before payload
  return ← errorDecision version.storage before (relation before error) _
    (LGraph.ofPGraph (graph before error)) noReason emptyReason case

def nameModel : Version → String
  | .v027 => "Solanalib.Specs.AnchorLang.error.Error.with_account_name_inline_run"
  | .v029 => "Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_account_name_run"
  | .v032 => "Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_account_name_run"
  | .v102 => "Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_account_name_run"
  | .v112 => "Solanalib.Specs.AnchorLangError.Error.with_account_name_run"

def nameChecker (version : Version) (function : String)
    (relation : Heap → Error version.storage (Program Nat) Nat Nat × Operand →
      Outcome Heap (Error version.storage (Program Nat) Nat Nat) String String → Prop)
    (graph : ∀ before args, LGraph (relation before args)
      (nameFn version.storage before args)) : Checker := ofModel function []
    (nameModel version) fun case => do
  let before ← asHeap version.program case.state
  let payload ← asPayload version.program Json.getNat? (← field case.args "error")
  let error ← errorArg version.storage before payload
  let mode ← strField case.args "operation"
  unless mode = "name" ∨ mode = "name_panic" do throw "unknown Name callback script"
  let args := (error, Operand.mk "name" "new account" (mode == "name_panic") false)
  return ← errorDecision version.storage before (relation before args) _
    (graph before args) some Json.str case

def valuesChecker (version : Version) (function : String)
    (relation : Heap → Args version.storage →
      Outcome Heap (Error version.storage (Program Nat) Nat Nat) String String → Prop)
    (graph : ∀ before args, LGraph (relation before args)
      (valuesFn version.storage before args)) : Checker := ofModel function []
    (match version.storage with
      | .inline => "Solanalib.Specs.AnchorLang.error.Error.with_values_inline_run"
      | .boxed => "Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_values_run") fun case
        => do
  let before ← asHeap version.program case.state
  let payload ← asPayload version.program Json.getNat? (← field case.args "error")
  let error ← errorArg version.storage before payload
  let mode ← natField case.args "mode"
  unless mode < 8 do throw "unknown ToString pair callback script"
  let left := Operand.mk "left" "11" (mode == 1 || mode == 5) (mode == 4 || mode == 6 || mode == 7)
  let right := Operand.mk "right" "22" (mode == 2 || mode == 6) (mode == 3 || mode == 5 || mode ==
    7)
  let args : Args version.storage := ⟨error, left, right⟩
  return ← errorDecision version.storage before (relation before args) _
    (graph before args) some Json.str case

/-- The equality model receives the full legacy payload, without any numeric
status projection of its owned Borsh String. -/
def legacyPayload : ErrorPayload → Option (Payload (ProgramErrorOwned.Value Nat) Nat)
  | .anchor value => some (.anchor value)
  | .program value => match value.error with
    | .inl error => some (.program ⟨error, value.origin, value.compared⟩)
    | .inr _ => none

def equalityTypes : EqualityTypes where
  State := Heap
  StringResource := Nat
  BoxResource := Nat
  currentString := currentString
  currentBox := fun heap owner => (currentBox heap owner).bind legacyPayload

def equalityFn (before : Heap) (left right : Nat) : Option (Outcome Heap Bool Empty Empty) := do
  let left ← equalityTypes.currentBox before left
  let right ← equalityTypes.currentBox before right
  let value ← equalPayload currentString before left right
  return .returned value before

theorem equalityGraph (before : Heap) (left right : Nat) :
    PGraph (Solanalib.Specs.AnchorLang.error.Error.eq_run equalityTypes before (⟨left⟩, ⟨right⟩))
      (equalityFn before left right) := by
  have composed := PGraph.exists_step (PGraph.ofOption (equalityTypes.currentBox before left))
    (fun l => PGraph.exists_step (PGraph.ofOption (equalityTypes.currentBox before right))
      (fun r => PGraph.exists_step (PGraph.ofOption (equalPayload currentString before l r))
        (fun result => PGraph.eq_left (Outcome.returned result before : Outcome Heap Bool Empty
          Empty))))
  apply PGraph.congr composed
  intro outcome
  constructor
  · rintro ⟨l, r, value, hl, hr, hv, ho⟩
    exact ⟨l, hl, r, hr, value, hv, ho⟩
  · rintro ⟨l, hl, r, hr, value, hv, ho⟩
    exact ⟨l, r, value, hl, hr, hv, ho⟩

def equalityProjection (strings boxes : Nat) : Outcome Heap Bool Empty Empty → String
  | .returned value heap => (returnedJson (toJson value) (heapJson strings boxes heap)).compress
  | .unwound impossible _ => nomatch impossible
  | .terminated impossible => nomatch impossible

def equalityChecker (function : String) : Checker := ofModel function []
    "Solanalib.Specs.AnchorLang.error.Error.eq_run" fun case => do
  let before ← asHeap (some .programError2_2_2) case.state
  let some left := currentBox before 0 | throw "left equality receiver is missing"
  let some right := currentBox before 1 | throw "right equality receiver is missing"
  unless (← field case.args "left").compress = (payloadJson (stringJson before) left).compress ∧
      (← field case.args "right").compress = (payloadJson (stringJson before) right).compress do
    throw "borrowed equality arguments do not match their actual Box payloads"
  let recorded ← parseOutcome pure pure (noReason (α := Empty)) (noReason (α := Empty)) case.outcome
  let observed := recorded.map fun
    | .returned value after => (returnedJson value after).compress
    | .unwound impossible _ => nomatch impossible
    | .terminated impossible => nomatch impossible
  return decideProjected (Solanalib.Specs.AnchorLang.error.Error.eq_run equalityTypes before (⟨(0 :
    Nat)⟩, ⟨(1 : Nat)⟩))
    _ (equalityGraph before 0 1) (equalityProjection before.strings.length before.boxes.length)
    observed (optionJson Json.str)


def ioChecker (function : String) : Checker := ofModel function []
    "Solanalib.Specs.AnchorLang.error.Error.from_io_error_run" fun case => do
  let before ← asHeap (some .programError2_2_2) case.state
  let mode ← natField case.args "mode"
  unless mode < 4 do throw "unknown IO conversion script"
  let relation := Solanalib.Specs.AnchorLang.error.Error.from_io_error_run ⟨ioTypes, rfl⟩ before
    mode
  return ← errorDecision .boxed before relation _ (LGraph.ofPGraph (ioGraph before mode)) some
    Json.str case


end SolanalibTest.Conformance.Library.Families.AnchorOperations

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorErrorOperations
open SolanalibTest.Conformance.Library.Families.Anchor

def fromAnchorChecker (function : String) : Checker := ofModel function []
    "Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_inline_run" fun case => do
  let before ← asHeap (some .solana1_15_2) case.state
  let .anchor payload ← asPayload (some .solana1_15_2) Json.getNat? (← field case.args
    "error")
    | throw "From<AnchorError> requires an AnchorError payload"
  let relation := Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_inline_run ⟨heapTypes
    .inline, rfl⟩ before payload
  return ← errorDecision .inline before relation _
    (LGraph.ofPGraph (Fn.fromPayload_graph heapGraph .inline before (.anchor payload)))
    noReason emptyReason case

def fromProgramChecker (function : String) : Checker := ofModel function []
    "Solanalib.Specs.AnchorLang.error.Error.from_program_error_inline_run" fun case => do
  let before ← asHeap (some .solana1_15_2) case.state
  let inputString := fun value => do
    let text ← value.getStr?
    let some owner := before.strings.findIdx? (· == some text)
      | throw "legacy input ProgramError String is absent from the input heap"
    pure owner
  let program ← asProgram (some .solana1_15_2) inputString (← field case.args "error")
  let relation := Solanalib.Specs.AnchorLang.error.Error.from_program_error_inline_run ⟨heapTypes
    .inline, rfl⟩ before program
  return ← errorDecision .inline before relation _
    (LGraph.ofPGraph (Fn.fromProgram_graph heapGraph .inline before program)) noReason emptyReason
      case

def pubkeysRel (storage : Storage) : Heap → Error storage (Program Nat) Nat Nat →
    Outcome Heap (Error storage (Program Nat) Nat Nat) Empty String → Prop :=
  match storage with
  | .inline => fun before error => Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_inline_run
      ⟨heapTypes .inline, rfl⟩ before (error, pubkey 3, pubkey 7)
  | .boxed => fun before error =>
    Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_pubkeys_run
      ⟨heapTypes .boxed, rfl⟩ before (error, pubkey 3, pubkey 7)

def sourceChecker (function : String) : Checker := ofModel function []
    "Solanalib.Specs.AnchorLang.error.Error.with_source_inline_run" fun case => do
  let before ← asHeap (some .solana1_15_2) case.state
  let payload ← asPayload (some .solana1_15_2) Json.getNat? (← field case.args "error")
  let source : AnchorError.Source := ⟨"src/example.rs", 4294967295⟩
  let relation := Solanalib.Specs.AnchorLang.error.Error.with_source_inline_run ⟨heapTypes .inline,
    rfl⟩ before (payload, source)
  return ← errorDecision .inline before relation _
    (LGraph.ofPGraph (Fn.withOrigin_graph heapGraph .inline (some (.source source)) before payload))
    noReason emptyReason case

def namesRel (storage : Storage) : Heap → Error storage (Program Nat) Nat Nat × Operand →
    Outcome Heap (Error storage (Program Nat) Nat Nat) String String → Prop :=
  match storage with
  | .inline => Solanalib.Specs.AnchorLang.error.Error.with_account_name_inline_run ⟨nameTypes
    .inline, rfl⟩
  | .boxed => Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_account_name_run
    ⟨nameTypes .boxed, rfl⟩

def valuesRel (storage : Storage) : Heap → Args storage →
    Outcome Heap (Error storage (Program Nat) Nat Nat) String String → Prop :=
  match storage with
  | .inline => Solanalib.Specs.AnchorLang.error.Error.with_values_inline_run ⟨valuesTypes .inline,
    rfl⟩
  | .boxed => Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_values_run ⟨valuesTypes
    .boxed, rfl⟩

end SolanalibTest.Conformance.Library.Families.AnchorOperations
