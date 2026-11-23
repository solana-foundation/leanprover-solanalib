/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOperations
public import Solanalib.Specs.Core.ProgramErrorOwnedValues

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOperations

/-- The complete ProgramError representation of the reviewed dependency. The legacy
profile also fixes the builtin enum range and the source wording of Display. -/
inductive ProgramProfile where
  | legacy (release : ProgramErrorOwned.Release)
  | modern
  deriving DecidableEq, Repr

def ProgramProfile.Value (profile : ProgramProfile) (StringResource : Type) : Type :=
  match profile with
  | .legacy _ => ProgramErrorOwned.Value StringResource
  | .modern => ProgramError.Value

/-- Arguments to the exact std formatting invocation. String resources are
borrowed, and Debug/Display are distinct operations on the full program error. -/
inductive FormatArg (StringResource Program : Type) where
  | text (value : String)
  | string (resource : StringResource)
  | number (value : UInt64)
  | debugProgram (error : Program)
  | displayProgram (error : Program)
  deriving DecidableEq, Repr

structure FormatRequest (StringResource Program : Type) where
  template : String
  arguments : List (FormatArg StringResource Program)
  deriving DecidableEq, Repr

/-- String::clone is reached only for a legacy Borsh error. The modern profile
has no such dependency: it cannot demand or invent an unused allocation. -/
def CloneString (profile : ProgramProfile) (State StringResource Terminal : Type) : Type :=
  match profile with
  | .legacy _ => Callback.Run State StringResource StringResource Empty Terminal
  | .modern => Unit

/-- Each actual formatting, logging and temporary-destruction dependency is
separate. There is no callback for the whole Error::log operation. Binding a
formatter must interpret the exact template and typed argument list below. -/
structure LogTypes (profile : ProgramProfile) where
  State : Type
  StringResource : Type
  BoxResource : Type
  Unwind : Type
  Terminal : Type
  storage : Storage
  currentBox : State → BoxResource →
    Option (Payload (profile.Value StringResource) StringResource)
  cloneString : CloneString profile State StringResource Terminal
  format : Callback.Run State (FormatRequest StringResource (profile.Value StringResource))
    StringResource Empty Terminal
  logString : Callback.Run State StringResource Unit Unwind Terminal
  logLiteral : Callback.Run State String Unit Unwind Terminal
  logPubkey : Callback.Run State Solanalib.Runtime.Pubkey Unit Unwind Terminal
  dropString : Callback.Run State StringResource Unit Empty Terminal
  double : Owned.DoubleUnwind State Unwind Terminal

abbrev LogTypes.Error {profile : ProgramProfile} (types : LogTypes profile) :=
  AnchorErrorOperations.Error types.storage (profile.Value types.StringResource)
    types.StringResource types.BoxResource

/-- Source evaluation of u64::from(program_error.clone()). A legacy cloned
Borsh String is consumed by the integer conversion before formatting starts. -/
def cloneStatus : (profile : ProgramProfile) → (types : LogTypes profile) →
    Callback.Run types.State (profile.Value types.StringResource) UInt64 Empty types.Terminal
  | .modern, _ => fun before error outcome =>
      outcome = .returned (ProgramError.V3_0_1.toStatus error) before
  | .legacy _, types => fun before error outcome =>
      match error with
      | .borshIoError message =>
          Callback.bind types.cloneString
            (fun cloned actual => Callback.map
              (fun _ => ProgramErrorOwned.toStatus error) types.dropString actual cloned)
            before message outcome
      | other => outcome = .returned (ProgramErrorOwned.toStatus other) before

/-- One temporary format String lives through the borrowed logging call, then
is dropped on normal return or host logger unwind. Terminal logging stops
without cleanup; the Solana syscall instantiation can use Empty unwind. -/
def formatLog {profile : ProgramProfile} (types : LogTypes profile) :
    Callback.Run types.State (FormatRequest types.StringResource (profile.Value
      types.StringResource))
      Unit types.Unwind types.Terminal :=
  fun before request => Callback.bind (AnchorErrorOwned.lift types.format)
    (fun resource afterFormat => Owned.scope types.double
      [fun state outcome => AnchorErrorOwned.lift types.dropString state resource outcome]
      types.logString afterFormat resource) before request

/-- Exact fixed source templates, including origin-dependent prefix and
argument order. Account-name Strings are borrowed without being cloned. -/
def anchorRequest {S Program : Type} (payload : AnchorPayload S) : FormatRequest S Program :=
  let suffix : List (FormatArg S Program) :=
    [.string payload.name, .number (UInt64.ofNat payload.number.toNat), .string payload.message]
  match payload.origin with
  | none => ⟨"AnchorError occurred. Error Code: {}. Error Number: {}. Error Message: {}.", suffix⟩
  | some (.source source) => ⟨
      "AnchorError thrown in {}:{}. Error Code: {}. Error Number: {}. Error Message: {}.",
      [.text source.filename, .number (UInt64.ofNat source.line.toNat)] ++ suffix⟩
  | some (.accountName name) => ⟨
      "AnchorError caused by account: {}. Error Code: {}. Error Number: {}. Error Message: \
        {}.",
      .string name :: suffix⟩

def programRequest {S Program : Type} (payload : ProgramPayload Program S)
    (status : UInt64) : FormatRequest S Program :=
  let suffix : List (FormatArg S Program) :=
    [.debugProgram payload.error, .number status, .displayProgram payload.error]
  match payload.origin with
  | none => ⟨"ProgramError occurred. Error Code: {:?}. Error Number: {}. Error Message: {}.",
    suffix⟩
  | some (.source source) => ⟨
      "ProgramError thrown in {}:{}. Error Code: {:?}. Error Number: {}. Error Message: {}.",
      [.text source.filename, .number (UInt64.ofNat source.line.toNat)] ++ suffix⟩
  | some (.accountName name) => ⟨
      "ProgramError caused by account: {}. Error Code: {:?}. Error Number: {}. Error \
        Message: {}.",
      .string name :: suffix⟩

/-- Pubkey comparisons make four logging calls. Value comparisons allocate,
log and drop two independent formatted Strings, in left/right order. -/
def comparedLog {profile : ProgramProfile} (types : LogTypes profile) :
    Callback.Run types.State (Option (Compared types.StringResource)) Unit types.Unwind
      types.Terminal :=
  fun before compared outcome =>
    match compared with
    | none => outcome = .returned () before
    | some (.pubkeys left right) =>
      Callback.bind types.logLiteral
        (fun _ afterLabel => Callback.bind types.logPubkey
          (fun _ afterLeft => Callback.bind types.logLiteral
            (fun _ afterRightLabel => types.logPubkey afterRightLabel right)
            afterLeft "Right:") afterLabel left) before "Left:" outcome
    | some (.values left right) =>
      Callback.bind (formatLog types)
        (fun _ afterLeft => formatLog types afterLeft ⟨"Right: {}", [.string right]⟩)
        before ⟨"Left: {}", [.string left]⟩ outcome

def payloadLog {profile : ProgramProfile} (types : LogTypes profile) :
    Callback.Run types.State (Payload (profile.Value types.StringResource) types.StringResource)
      Unit types.Unwind types.Terminal :=
  fun before payload =>
    let base : Callback.Run types.State Unit Unit types.Unwind types.Terminal :=
      match payload with
      | .anchor anchor => fun state _ => formatLog types state (anchorRequest anchor)
      | .program program => fun state _ => Callback.bind (AnchorErrorOwned.lift (cloneStatus
        profile types))
          (fun status actual => formatLog types actual (programRequest program status))
          state program.error
    Callback.bind base (fun _ afterBase => comparedLog types afterBase payload.compared) before ()

def logAt {profile : ProgramProfile} (types : LogTypes profile) : (storage : Storage) →
    Callback.Run types.State
      (AnchorErrorOperations.Error storage (profile.Value types.StringResource)
        types.StringResource types.BoxResource) Unit types.Unwind types.Terminal
  | .inline => payloadLog types
  | .boxed => fun before error outcome => ∃ payload,
      types.currentBox before error.resource = some payload ∧ payloadLog types before payload
        outcome

def logRun {profile : ProgramProfile} (types : LogTypes profile) :
    Callback.Run types.State types.Error Unit types.Unwind types.Terminal :=
  logAt types types.storage

/-- Error::log has no result data or error mutation. Its complete model retains
the concrete primitive sequence, intermediate states and terminal outcomes. -/
def logFamily (profile : ProgramProfile) : Family where
  Index := LogTypes profile
  State := fun types => types.State
  Args := fun types => types.Error
  Value := fun _ => Unit
  Unwind := fun types => types.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => { requires := fun _ _ => True, post := logRun types }

theorem log_reference (profile : ProgramProfile) :
    FamilyReference (logFamily profile) logRun := fun _ _ _ _ _ run => run

/-- A trace resource is distinct from its contents; formatting allocates a
fresh natural-number owner, and log/drop events observe that exact owner. -/
inductive LogEvent where
  | format (request : FormatRequest Nat ProgramError.Value) (resource : Nat)
  | logged (resource : Nat)
  | literal (text : String)
  | pubkey (value : Solanalib.Runtime.Pubkey)
  | dropped (resource : Nat)
  deriving DecidableEq, Repr

abbrev logSample : LogTypes .modern where
  State := List LogEvent
  StringResource := Nat
  BoxResource := Nat
  Unwind := Empty
  Terminal := Empty
  storage := .inline
  currentBox := fun _ _ => none
  cloneString := ()
  format := fun before request outcome =>
    outcome = .returned before.length (before ++ [.format request before.length])
  logString := fun before resource outcome => outcome = .returned () (before ++ [.logged resource])
  logLiteral := fun before value outcome => outcome = .returned () (before ++ [.literal value])
  logPubkey := fun before value outcome => outcome = .returned () (before ++ [.pubkey value])
  dropString := fun before resource outcome => outcome = .returned () (before ++ [.dropped
    resource])
  double := AnchorErrorOwned.noDouble

abbrev logSamplePayload : Payload ProgramError.Value Nat :=
  .program ⟨.invalidAccountData, none, none⟩

def logSampleRequest : FormatRequest Nat ProgramError.Value :=
  programRequest ⟨.invalidAccountData, none, none⟩
    (ProgramError.V3_0_1.toStatus .invalidAccountData)

def logSampleEvents : List LogEvent :=
  [.format logSampleRequest 0, .logged 0, .dropped 0]

theorem log_hasExecution : FamilyHasExecution (logFamily .modern) logRun logSample := by
  refine ⟨[], logSamplePayload, .returned () logSampleEvents, trivial, ?_⟩
  refine ⟨.returned () logSampleEvents, ?_, rfl⟩
  refine ⟨.returned (ProgramError.V3_0_1.toStatus .invalidAccountData) [],
    ⟨_, rfl, rfl⟩, ?_⟩
  exact ⟨.returned 0 [.format logSampleRequest 0], ⟨_, rfl, rfl⟩,
    .returned () [.format logSampleRequest 0, .logged 0], rfl,
    .returned () logSampleEvents, ⟨_, rfl, rfl⟩, rfl⟩

theorem log_satisfiable : FamilySatisfiable (logFamily .modern) logSample :=
  log_hasExecution.satisfiable

end Solanalib.Specs.Core.AnchorErrorOperations
