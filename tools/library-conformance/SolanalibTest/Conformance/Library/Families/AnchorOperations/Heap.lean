/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Graph
import SolanalibTest.Conformance.Library.Families.Anchor.World
import Solanalib.Specs.Core.ProgramErrorOwnedValues

/-!
Finite, observable String and Box identities for the recorded Anchor calls.
The old ProgramError is kept separately from the modern unit Borsh variant.
Input IDs, live fresh allocations, callback order and full diagnostic values
are projected from the same reached state. No numeric error-code erasure is
used to model ownership or equality.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorErrorOperations
open SolanalibTest.Conformance.Library.Families.Anchor

abbrev Program (S : Type) := Sum (ProgramErrorOwned.Value S) ProgramError.Value
abbrev ErrorPayload := Payload (Program Nat) Nat

structure Heap where
  strings : List (Option String)
  boxes : List (Option ErrorPayload)
  callbacks : List String := []
  deriving DecidableEq

def programStrings : Program Nat → List Nat
  | .inl error => ProgramErrorOwned.strings error
  | .inr _ => []

def currentString (heap : Heap) (owner : Nat) : Option String :=
  (heap.strings[owner]?).join

def currentBox (heap : Heap) (owner : Nat) : Option ErrorPayload :=
  (heap.boxes[owner]?).join

def newString (heap : Heap) (text : String) : Outcome Heap Nat Empty String :=
  .returned heap.strings.length { heap with strings := heap.strings ++ [some text] }

def newBox (heap : Heap) (payload : ErrorPayload) : Outcome Heap Nat Empty String :=
  .returned heap.boxes.length { heap with boxes := heap.boxes ++ [some payload] }

def writeBox (heap : Heap) (owner : Nat) (payload : ErrorPayload) : Option Heap :=
  (currentBox heap owner).map fun _ => { heap with boxes := heap.boxes.set owner (some payload) }

def retireString (heap : Heap) (owner : Nat) : Option (Outcome Heap Unit Empty String) :=
  (currentString heap owner).map fun _ => .returned () {
    heap with strings := heap.strings.set owner none }

def retireBox (heap : Heap) (owner : Nat) : Option (Outcome Heap Unit Empty String) :=
  (currentBox heap owner).map fun _ => .returned () { heap with boxes := heap.boxes.set owner none }

def heapOps : Ops Heap (Program Nat) Nat Nat String where
  currentString := currentString
  currentBox := currentBox
  programStrings := programStrings
  copyLiteral := Callback.ofFunction newString
  formatLiteral := Callback.ofFunction newString
  newBox := Callback.ofFunction newBox
  writeBox := writeBox
  dropString := fun before owner outcome => retireString before owner = some outcome
  freeBox := fun before owner outcome => retireBox before owner = some outcome

def heapFn : OpsFn Heap (Program Nat) Nat Nat String where
  copy := fun before text => some (newString before text)
  format := fun before text => some (newString before text)
  newBox := fun before payload => some (newBox before payload)
  dropString := retireString
  freeBox := retireBox

theorem heapGraph : OpsGraph heapOps heapFn where
  copy := PGraph.ofFunction newString
  format := PGraph.ofFunction newString
  newBox := PGraph.ofFunction newBox
  dropString := fun _ _ => PGraph.ofOption _
  freeBox := fun _ _ => PGraph.ofOption _

def heapTypes (storage : Storage) : Types where
  State := Heap
  Program := Program Nat
  StringResource := Nat
  BoxResource := Nat
  Terminal := String
  storage := storage
  ops := heapOps

/-- This conversion is only for a non-Borsh tag; the legacy Borsh constructor
is parsed with its actual String separately. -/
def legacyBuiltin {S : Type} : ProgramError.Value → Option (ProgramErrorOwned.Value S)
  | .custom code => some (.custom code)
  | .borshIoError => none
  | .invalidArgument => some .invalidArgument
  | .invalidInstructionData => some .invalidInstructionData
  | .invalidAccountData => some .invalidAccountData
  | .accountDataTooSmall => some .accountDataTooSmall
  | .insufficientFunds => some .insufficientFunds
  | .incorrectProgramId => some .incorrectProgramId
  | .missingRequiredSignature => some .missingRequiredSignature
  | .accountAlreadyInitialized => some .accountAlreadyInitialized
  | .uninitializedAccount => some .uninitializedAccount
  | .notEnoughAccountKeys => some .notEnoughAccountKeys
  | .accountBorrowFailed => some .accountBorrowFailed
  | .maxSeedLengthExceeded => some .maxSeedLengthExceeded
  | .invalidSeeds => some .invalidSeeds
  | .accountNotRentExempt => some .accountNotRentExempt
  | .unsupportedSysvar => some .unsupportedSysvar
  | .illegalOwner => some .illegalOwner
  | .maxAccountsDataAllocationsExceeded => some .maxAccountsDataAllocationsExceeded
  | .invalidRealloc => some .invalidRealloc
  | .maxInstructionTraceLengthExceeded => some .maxInstructionTraceLengthExceeded
  | .builtinProgramsMustConsumeComputeUnits => some .builtinProgramsMustConsumeComputeUnits
  | .invalidAccountOwner => some .invalidAccountOwner
  | .arithmeticOverflow => some .arithmeticOverflow
  | .immutable => some .immutable
  | .incorrectAuthority => some .incorrectAuthority

def asProgram {S : Type} (release : Option ProgramErrorOwned.Release)
    (string : Json → Result S) (value : Json) : Result (Program S) := do
  match release with
  | none => return .inr (← asProgramError value)
  | some release =>
    let (tag, fields) ← asVariant value
    let error ← if tag = "BorshIoError" then
      match fields with
      | [message] => pure (.borshIoError (← string message))
      | _ => throw "legacy BorshIoError requires its owned String"
    else do
      let modern ← asProgramError value
      let some legacy := legacyBuiltin modern | throw "legacy BorshIoError requires its \
        String"
      pure legacy
    unless ProgramErrorOwned.available release error do
      throw "ProgramError variant is absent from the selected dependency release"
    return .inl error

def origin {S : Type} : Option (Sum AnchorError.Source S) → Option (Origin S)
  | none => none
  | some (.inl source) => some (.source source)
  | some (.inr name) => some (.accountName name)

def compared {S : Type} : Option (Sum (S × S) (Solanalib.Runtime.Pubkey ×
  Solanalib.Runtime.Pubkey)) → Option (Compared S)
  | none => none
  | some (.inl (left, right)) => some (.values left right)
  | some (.inr (left, right)) => some (.pubkeys left right)

def asPayload {S : Type} (release : Option ProgramErrorOwned.Release)
    (string : Json → Result S) (value : Json) : Result (Payload (Program S) S) := do
  let (tag, fields) ← asTagged value
  match tag with
  | "AnchorError" => return .anchor ⟨← string (← field fields "name"),
      ← asU32 (← field fields "code"), ← string (← field fields "message"),
      origin (← asOrigin string (← field fields "origin")),
      compared (← asCompared string (← field fields "compared"))⟩
  | "ProgramError" => return .program ⟨← asProgram release string (← field fields "error"),
      origin (← asOrigin string (← field fields "origin")),
      compared (← asCompared string (← field fields "compared"))⟩
  | _ => throw s!"unknown Anchor error variant {tag}"

def asHeap (release : Option ProgramErrorOwned.Release) (value : Json) : Result Heap := do
  return ⟨(← asList Json.getStr? (← field value "strings")).map some,
    (← asList (asPayload release Json.getNat?) (← field value "boxes")).map some,
    ← asList Json.getStr? (← field value "callbacks")⟩

def errorArg (storage : Storage) (heap : Heap) (payload : ErrorPayload) :
    Result (Error storage (Program Nat) Nat Nat) :=
  match storage with
  | .inline => pure payload
  | .boxed =>
    if currentBox heap 0 = some payload then pure ⟨0⟩
    else throw "receiver payload must be the actual input Box payload"

def programJson {S : Type} (string : S → Json) : Program S → Json
  | .inl (.borshIoError message) => variantJson "BorshIoError" [string message]
  | .inl error => programErrorJson (ProgramErrorOwned.statusVariant error)
  | .inr error => programErrorJson error

def originJson {S : Type} (string : S → Json) : Option (Origin S) → Json
  | none => .null
  | some (.source source) => tagged "Source"
      (Json.mkObj [("filename", toJson source.filename), ("line", toJson source.line.toNat)])
  | some (.accountName name) => tagged "AccountName" (string name)

def comparedJson {S : Type} (string : S → Json) : Option (Compared S) → Json
  | none => .null
  | some (.values left right) => tagged "Values" (Json.arr #[string left, string right])
  | some (.pubkeys left right) => tagged "Pubkeys" (Json.arr #[pubkeyJson left, pubkeyJson right])

def payloadJson {S : Type} (string : S → Json) : Payload (Program S) S → Json
  | .anchor value => tagged "AnchorError" (Json.mkObj [
      ("name", string value.name), ("code", toJson value.number.toNat),
      ("message", string value.message), ("origin", originJson string value.origin),
      ("compared", comparedJson string value.compared)])
  | .program value => tagged "ProgramError" (Json.mkObj [
      ("error", programJson string value.error), ("origin", originJson string value.origin),
      ("compared", comparedJson string value.compared)])

def stringJson (heap : Heap) (owner : Nat) : Json :=
  optionJson Json.str (currentString heap owner)

def observedId (inputCount : Nat) (owner : Nat) : Json :=
  if owner < inputCount then toJson owner else .null

def errorJson (storage : Storage) (strings boxes : Nat) (heap : Heap)
    (error : Error storage (Program Nat) Nat Nat) : Json :=
  let box := match storage with
    | .inline => Json.null
    | .boxed => observedId boxes error.resource
  match currentPayload storage heapOps heap error with
  | none => Json.null
  | some payload => Json.mkObj [("box", box), ("value", payloadJson (stringJson heap) payload),
      ("strings", listJson (observedId strings) (payload.strings programStrings))]

def emptySyscalls : Json := Json.mkObj [("replies", Json.arr #[]), ("log", Json.arr #[])]

def heapJson (strings boxes : Nat) (heap : Heap) : Json :=
  let freshStrings := ((heap.strings.drop strings).filterMap id).filter (· != "") |>.length
  let freshBoxes := ((heap.boxes.drop boxes).filterMap id).length
  Json.mkObj [("strings_live", listJson (toJson ∘ Option.isSome) (heap.strings.take strings)),
    ("boxes_live", listJson (toJson ∘ Option.isSome) (heap.boxes.take boxes)),
    ("fresh_live", toJson (freshStrings + freshBoxes)),
    ("callbacks", toJson heap.callbacks), ("syscalls", emptySyscalls)]

def project {V U : Type} (strings boxes : Nat) (value : Heap → V → Json) :
    Outcome Heap V U String → Outcome Json Json U String
  | .returned result after => .returned (value after result) (heapJson strings boxes after)
  | .unwound reason after => .unwound reason (heapJson strings boxes after)
  | .terminated reason => .terminated reason

def jsonOutcome {U : Type} (reason : U → Json) : Outcome Json Json U String → Json
  | .returned result after => returnedJson result after
  | .unwound value after => Json.mkObj [("exit", "unwound"), ("reason", reason value), (
    "state",
    after)]
  | .terminated value => Json.mkObj [("exit", "terminated"), ("reason", Json.str value)]

end SolanalibTest.Conformance.Library.Families.AnchorOperations
