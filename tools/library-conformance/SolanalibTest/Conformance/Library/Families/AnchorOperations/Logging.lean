/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.AnchorLang.error_log
import Solanalib.Specs.AnchorLangError.error_operations
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Errors

/-!
Exact format requests and primitive clone/drop/log sequences at the recorded
Solana syscall profile. The callback model also permits host logger unwind;
this corpus uses the explicitly non-unwinding scripted syscall provider.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations.Logging

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorErrorOperations
open SolanalibTest.Conformance.Library.Families.Anchor

structure State (profile : ProgramProfile) where
  strings : List (Option String)
  boxes : List (Option (Payload (profile.Value Nat) Nat))
  trace : List Json := []

def current {profile : ProgramProfile} (state : State profile) (owner : Nat) :=
  (state.strings[owner]?).join

def alloc {profile : ProgramProfile} (state : State profile) (text : String) : Outcome (State
  profile) Nat Empty String :=
  .returned state.strings.length { state with strings := state.strings ++ [some text] }

def clone {profile : ProgramProfile} (state : State profile) (owner : Nat) :=
  (current state owner).map (alloc state)

def dropString {profile : ProgramProfile} (state : State profile) (owner : Nat) :
    Option (Outcome (State profile) Unit Empty String) :=
  (current state owner).map fun _ => .returned () {
    state with strings := state.strings.set owner none }

def hex32 (number : UInt32) : String :=
  let digits := ((hexOf ((Solanalib.Runtime.leBytes 4 number.toNat).reverse)).toList.dropWhile (·
    == '0'))
  if digits.isEmpty then "0" else String.ofList digits

def programName (error : ProgramError.Value) : Option String :=
  (programErrorNames.find? (·.2 == error)).map (·.1)

/-- Primitive formatting is interpreted on the recorded enum variants. An
unsupported Display argument is rejected, never replaced by an arbitrary log. -/
def formatProgram (profile : ProgramProfile) (state : State profile) (debug : Bool) :
    profile.Value Nat → Option String :=
  match profile with
  | .legacy _ => fun error =>
    match error with
    | .borshIoError owner => (current state owner).map fun text =>
        if debug then "BorshIoError(" ++ (Json.str text).compress ++ ")" else "IO Error: " ++ text
    | .custom code => some (if debug then "Custom(" ++ toString code.toNat ++ ")"
        else "Custom program error: 0x" ++ hex32 code)
    | _ => if debug then
        programName (ProgramErrorOwned.statusVariant error)
      else none
  | .modern => fun error => match error with
    | .custom code => some (if debug then "Custom(" ++ toString code.toNat ++ ")"
        else "Custom program error: 0x" ++ hex32 code)
    | _ => if debug then programName error else none

def formatArg (profile : ProgramProfile) (state : State profile) :
    FormatArg Nat (profile.Value Nat) → Option String
  | .text text => some text
  | .string owner => current state owner
  | .number value => some (toString value.toNat)
  | .debugProgram error => formatProgram profile state true error
  | .displayProgram error => formatProgram profile state false error

def interpolate : List String → List String → Option String
  | [last], [] => some last
  | first :: rest, argument :: args => (interpolate rest args).map (first ++ argument ++ ·)
  | _, _ => none

def format (profile : ProgramProfile) (state : State profile) (request : FormatRequest Nat
  (profile.Value Nat)) := do
  let arguments ← request.arguments.mapM (formatArg profile state)
  let text ← interpolate ((request.template.replace "{:?}" "{}").splitOn "{}") arguments
  return alloc state text

def textEvent (text : String) : Json := Json.mkObj [
  ("syscall", "sol_log_"), ("bytes", bytesJson text.toUTF8.data.toList)]

def logText {profile : ProgramProfile} (state : State profile) (text : String) :
    Outcome (State profile) Unit Empty String :=
  .returned () { state with trace := state.trace ++ [textEvent text] }

def logOwner {profile : ProgramProfile} (state : State profile) (owner : Nat) :=
  (current state owner).map (logText state)

def logKey {profile : ProgramProfile} (state : State profile) (key : Solanalib.Runtime.Pubkey) :
    Outcome (State profile) Unit Empty String :=
  .returned () { state with trace := state.trace ++ [Json.mkObj [
    ("syscall", "sol_log_pubkey"), ("address", pubkeyJson key)]] }

def types (profile : ProgramProfile) (storage : Storage) : LogTypes profile where
  State := State profile
  StringResource := Nat
  BoxResource := Nat
  Unwind := Empty
  Terminal := String
  storage := storage
  currentBox := fun state owner => (state.boxes[owner]?).join
  cloneString := match profile with
    | .legacy _ => fun state owner outcome => clone state owner = some outcome
    | .modern => ()
  format := fun state request outcome => format profile state request = some outcome
  logString := fun state owner outcome => logOwner state owner = some outcome
  logLiteral := Callback.ofFunction logText
  logPubkey := Callback.ofFunction logKey
  dropString := fun state owner outcome => dropString state owner = some outcome
  double := AnchorErrorOwned.noDouble

def statusFn (profile : ProgramProfile) (before : State profile) :
    profile.Value Nat → Option (Outcome (State profile) UInt64 Empty String) :=
  match profile with
  | .modern => fun error => some (.returned (ProgramError.V3_0_1.toStatus error) before)
  | .legacy _ => fun error => match error with
    | .borshIoError owner => (clone before owner).bind (PGraph.bindK fun copied after =>
        (dropString after copied).map (Outcome.map (fun _ => ProgramErrorOwned.toStatus error)))
    | _ => some (.returned (ProgramErrorOwned.toStatus error) before)

theorem statusGraph (profile : ProgramProfile) (storage : Storage) (before : State profile)
    (error : profile.Value Nat) :
    PGraph (cloneStatus profile (types profile storage) before error) (statusFn profile before
      error) := by
  cases profile with
  | modern => exact PGraph.eq_left _
  | legacy release =>
    cases error <;> try exact PGraph.eq_left _
    exact PGraph.bind (PGraph.ofOption _) fun copied after => PGraph.map _ (PGraph.ofOption
      (dropString after copied))

def formatFn (profile : ProgramProfile) (before : State profile)
    (request : FormatRequest Nat (profile.Value Nat)) :=
  ((format profile before request).map OwnedFn.liftO).bind (PGraph.bindK fun owner after =>
    (logOwner after owner).bind (PGraph.cleanupFn OwnedFn.noDoubleFn
      [fun state => (dropString state owner).map OwnedFn.liftO]))

theorem formatGraph (profile : ProgramProfile) (storage : Storage) (before : State profile)
    (request : FormatRequest Nat (profile.Value Nat)) :
    PGraph (formatLog (types profile storage) before request) (formatFn profile before request) :=
  PGraph.bind (OwnedFn.lift_graph (PGraph.ofOption _)) fun owner after =>
    PGraph.scope OwnedFn.noDouble_graph
      (PGraph.DropsGraph.cons (fun state => OwnedFn.lift_graph (PGraph.ofOption (dropString state
        owner)))
        PGraph.DropsGraph.nil) (PGraph.ofOption (logOwner after owner))

def comparedFn (profile : ProgramProfile) (before : State profile) :
    Option (Compared Nat) → Option (Outcome (State profile) Unit Empty String)
  | none => some (.returned () before)
  | some (.values left right) => (formatFn profile before ⟨"Left: {}", [.string left]⟩).bind
      (PGraph.bindK fun _ after => formatFn profile after ⟨"Right: {}", [.string right]⟩)
  | some (.pubkeys left right) => (some (logText before "Left:")).bind (PGraph.bindK fun _ s₁ =>
      (some (logKey s₁ left)).bind (PGraph.bindK fun _ s₂ =>
        (some (logText s₂ "Right:")).bind (PGraph.bindK fun _ s₃ => some (logKey s₃ right))))

theorem comparedGraph (profile : ProgramProfile) (storage : Storage) (before : State profile)
    (value : Option (Compared Nat)) :
    PGraph (comparedLog (types profile storage) before value) (comparedFn profile before value) :=
      by
  cases value with
  | none => exact PGraph.eq_left _
  | some value => cases value with
    | values left right =>
      exact PGraph.bind (formatGraph profile storage before _) fun _ after => formatGraph profile
        storage after _
    | pubkeys left right =>
      exact PGraph.bind (PGraph.ofFunction logText before _) fun _ s₁ =>
        PGraph.bind (PGraph.ofFunction logKey s₁ left) fun _ s₂ =>
          PGraph.bind (PGraph.ofFunction logText s₂ _) fun _ s₃ => PGraph.ofFunction logKey s₃ right

def payloadFn (profile : ProgramProfile) (before : State profile)
    (payload : Payload (profile.Value Nat) Nat) :=
  let base := match payload with
    | .anchor value => formatFn profile before (anchorRequest value)
    | .program value => ((statusFn profile before value.error).map OwnedFn.liftO).bind
        (PGraph.bindK fun status after => formatFn profile after (programRequest value status))
  base.bind (PGraph.bindK fun _ after => comparedFn profile after payload.compared)

theorem payloadGraph (profile : ProgramProfile) (storage : Storage) (before : State profile)
    (payload : Payload (profile.Value Nat) Nat) :
    PGraph (payloadLog (types profile storage) before payload) (payloadFn profile before payload)
      := by
  apply PGraph.bind
  · cases payload with
    | anchor value => exact formatGraph profile storage before _
    | program value =>
      exact PGraph.bind (OwnedFn.lift_graph (statusGraph profile storage before value.error))
        fun status after => formatGraph profile storage after (programRequest value status)
  · intro _ after
    exact comparedGraph profile storage after payload.compared

/-- Every owned input String receives its own owner, even when text is equal.
The corpus observes log bytes; these owners additionally keep clone/drop order
inside the exact mathematical logging relation. -/
def ownString (text : String) : StateM (List (Option String)) Nat := do
  let strings ← get
  set (strings ++ [some text])
  return strings.length

def ownOrigin : Option (Origin String) → StateM (List (Option String)) (Option (Origin Nat))
  | none => pure none
  | some (.source source) => pure (some (.source source))
  | some (.accountName name) => return some (.accountName (← ownString name))

def ownCompared : Option (Compared String) → StateM (List (Option String)) (Option (Compared Nat))
  | none => pure none
  | some (.pubkeys left right) => pure (some (.pubkeys left right))
  | some (.values left right) => return some (.values (← ownString left) (← ownString right))

def ownLegacy (error : ProgramErrorOwned.Value String) :
    StateM (List (Option String)) (ProgramErrorOwned.Value Nat) :=
  match error with
  | .invalidArgument => pure .invalidArgument
  | .invalidInstructionData => pure .invalidInstructionData
  | .invalidAccountData => pure .invalidAccountData
  | .accountDataTooSmall => pure .accountDataTooSmall
  | .insufficientFunds => pure .insufficientFunds
  | .incorrectProgramId => pure .incorrectProgramId
  | .missingRequiredSignature => pure .missingRequiredSignature
  | .accountAlreadyInitialized => pure .accountAlreadyInitialized
  | .uninitializedAccount => pure .uninitializedAccount
  | .notEnoughAccountKeys => pure .notEnoughAccountKeys
  | .accountBorrowFailed => pure .accountBorrowFailed
  | .maxSeedLengthExceeded => pure .maxSeedLengthExceeded
  | .invalidSeeds => pure .invalidSeeds
  | .accountNotRentExempt => pure .accountNotRentExempt
  | .unsupportedSysvar => pure .unsupportedSysvar
  | .illegalOwner => pure .illegalOwner
  | .maxAccountsDataAllocationsExceeded => pure .maxAccountsDataAllocationsExceeded
  | .invalidRealloc => pure .invalidRealloc
  | .maxInstructionTraceLengthExceeded => pure .maxInstructionTraceLengthExceeded
  | .builtinProgramsMustConsumeComputeUnits => pure .builtinProgramsMustConsumeComputeUnits
  | .invalidAccountOwner => pure .invalidAccountOwner
  | .arithmeticOverflow => pure .arithmeticOverflow
  | .immutable => pure .immutable
  | .incorrectAuthority => pure .incorrectAuthority

  | .custom code => pure (.custom code)
  | .borshIoError text => return .borshIoError (← ownString text)

def ownProgram : (profile : ProgramProfile) → profile.Value String →
    StateM (List (Option String)) (profile.Value Nat)
  | .legacy _, error => ownLegacy error
  | .modern, error => pure error

def ownPayload (profile : ProgramProfile) (payload : Payload (profile.Value String) String) :
    StateM (List (Option String)) (Payload (profile.Value Nat) Nat) := do
  match payload with
  | .anchor value => return .anchor ⟨← ownString value.name, value.number,
      ← ownString value.message, ← ownOrigin value.origin, ← ownCompared value.compared⟩
  | .program value =>
    let program ← ownProgram profile value.error
    return .program ⟨program, ← ownOrigin value.origin, ← ownCompared value.compared⟩

def programProfile : Version → ProgramProfile
  | .v027 => .legacy .solana1_15_2
  | .v029 => .legacy .solana1_18_26
  | .v032 => .legacy .programError2_2_2
  | .v102 | .v112 => .modern

def selectPayload (profile : ProgramProfile) (payload : Payload (Program String) String) :
    Option (Payload (profile.Value String) String) :=
  match payload with
  | .anchor value => some (.anchor value)
  | .program value => match profile, value.error with
    | .legacy _, .inl error => some (.program ⟨error, value.origin, value.compared⟩)
    | .modern, .inr error => some (.program ⟨error, value.origin, value.compared⟩)
    | _, _ => none

def inputError (storage : Storage) {profile : ProgramProfile}
    (payload : Payload (profile.Value Nat) Nat) : Error storage (profile.Value Nat) Nat Nat :=
  match storage with
  | .inline => payload
  | .boxed => ⟨0⟩

def logFn (profile : ProgramProfile) (storage : Storage) (before : State profile)
    (error : Error storage (profile.Value Nat) Nat Nat) : Option (Outcome (State profile) Unit
      Empty String) :=
  match storage with
  | .inline => payloadFn profile before error
  | .boxed => ((before.boxes[error.resource]?).join).bind (payloadFn profile before)

theorem logGraph (profile : ProgramProfile) (storage : Storage) (before : State profile)
    (error : Error storage (profile.Value Nat) Nat Nat) :
    PGraph (logRun (types profile storage) before error) (logFn profile storage before error) := by
  cases storage with
  | inline => exact payloadGraph profile .inline before error
  | boxed =>
    exact PGraph.exists_step (PGraph.ofOption ((before.boxes[error.resource]?).join))
      (fun payload => payloadGraph profile .boxed before payload)

def relation (version : Version) : State (programProfile version) →
    Error version.storage ((programProfile version).Value Nat) Nat Nat →
    Outcome (State (programProfile version)) Unit Empty String → Prop :=
  match version with
  | .v027 => Solanalib.Specs.AnchorLang.error.Error.log_inline_run ⟨types (.legacy .solana1_15_2)
    .inline, rfl⟩
  | .v029 => Solanalib.Specs.AnchorLang.error.Error.log_legacy_program_run ⟨types (.legacy
    .solana1_18_26) .boxed, rfl⟩
  | .v032 => Solanalib.Specs.AnchorLang.error.Error.log_run ⟨types (.legacy .programError2_2_2)
    .boxed, rfl⟩
  | .v102 => Solanalib.Specs.AnchorLang.error.Error.log_modern_run ⟨types .modern .boxed, rfl⟩
  | .v112 => Solanalib.Specs.AnchorLangError.Error.log_run ⟨types .modern .boxed, rfl⟩

def projection {profile : ProgramProfile} : Outcome (State profile) Unit Empty String → String
  | .returned () after => (returnedJson Json.null (Json.mkObj [("syscalls", Json.mkObj [
      ("replies", Json.arr #[]), ("log", toJson after.trace)])])).compress
  | .unwound impossible _ => nomatch impossible
  | .terminated reason => (Json.mkObj [("exit", "terminated"), ("reason", toJson reason)]).compress

def modelName : Version → String
  | .v027 => "Solanalib.Specs.AnchorLang.error.Error.log_inline_run"
  | .v029 => "Solanalib.Specs.AnchorLang.error.Error.log_legacy_program_run"
  | .v032 => "Solanalib.Specs.AnchorLang.error.Error.log_run"
  | .v102 => "Solanalib.Specs.AnchorLang.error.Error.log_modern_run"
  | .v112 => "Solanalib.Specs.AnchorLangError.Error.log_run"

def checker (version : Version) (function : String)
    (selectedRelation : State (programProfile version) →
      Error version.storage ((programProfile version).Value Nat) Nat Nat →
      Outcome (State (programProfile version)) Unit Empty String → Prop)
    (graph : ∀ before error, PGraph (selectedRelation before error)
      (logFn (programProfile version) version.storage before error)) : Checker :=
  ofModel function [] (modelName version) fun case => do
    unless (← field case.state "syscalls").compress = emptySyscalls.compress do
      throw "logging fixture requires the recorded empty syscall prefix"
    let parsed ← asPayload version.program Json.getStr? (← field case.args "error")
    let some selected := selectPayload (programProfile version) parsed
      | throw "error payload belongs to a different ProgramError release"
    let (payload, strings) := (ownPayload (programProfile version) selected).run []
    let before : State (programProfile version) := ⟨strings,
      if version.storage = .boxed then [some payload] else [], []⟩
    let error := inputError version.storage payload
    let observed ← parseOutcome pure pure (noReason (α := Empty)) some case.outcome
    return decideProjected (selectedRelation before error) _ (graph before error) projection
      (observed.map fun value => (jsonOutcome emptyReason value).compress) (optionJson Json.str)

end SolanalibTest.Conformance.Library.Families.AnchorOperations.Logging
