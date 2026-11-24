/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwned
public import Solanalib.Specs.Core.ProgramErrorOwned
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOperations

/-- Anchor 0.27 stores error payloads inline. Anchor 0.29 and the later
reviewed releases own a Box around the same kind of payload. -/
inductive Storage where
  | inline
  | boxed
  deriving DecidableEq, Repr

/-- Shared diagnostic fields are exactly the existing resource vocabulary. -/
abbrev Origin := AnchorErrorOwned.Origin
abbrev Compared := AnchorErrorOwned.Compared
abbrev AnchorPayload := AnchorErrorOwned.AnchorPayload
abbrev Code := AnchorErrorOwned.Code

/-- The ProgramError of the selected dependency is retained without status-code
projection. Older dependencies instantiate `Program` with
`ProgramErrorOwned.Value StringResource`; newer ones use the string-free enum. -/
structure ProgramPayload (Program StringResource : Type) where
  error : Program
  origin : Option (Origin StringResource)
  compared : Option (Compared StringResource)
  deriving DecidableEq, Repr

/-- Both error variants retain their current owned diagnostics. -/
inductive Payload (Program StringResource : Type) where
  | anchor (value : AnchorPayload StringResource)
  | program (value : ProgramPayload Program StringResource)
  deriving DecidableEq, Repr

/-- The release-selected representation. An inline error is its owned payload;
a boxed error is the stable handle of the allocation containing that payload. -/
def Error (storage : Storage) (Program StringResource BoxResource : Type) : Type :=
  match storage with
  | .inline => Payload Program StringResource
  | .boxed => AnchorErrorOwned.Error BoxResource

/-- Primitive owned String/Box dependencies. `programStrings` is the exact
owned-field projection for the selected ProgramError representation, not a
destructor oracle. No operation here invokes an SDK body or CPI. -/
structure Ops (State Program StringResource BoxResource Terminal : Type) where
  currentString : State → StringResource → Option String
  currentBox : State → BoxResource → Option (Payload Program StringResource)
  programStrings : Program → List StringResource
  copyLiteral : Callback.Run State String StringResource Empty Terminal
  formatLiteral : Callback.Run State String StringResource Empty Terminal
  newBox : Callback.Run State (Payload Program StringResource) BoxResource Empty Terminal
  writeBox : State → BoxResource → Payload Program StringResource → Option State
  dropString : Callback.Run State StringResource Unit Empty Terminal
  freeBox : Callback.Run State BoxResource Unit Empty Terminal

variable {State Program StringResource BoxResource Terminal : Type}

/-- Current payload lookup does not invent a box for an inline release. -/
def currentPayload (storage : Storage)
    (ops : Ops State Program StringResource BoxResource Terminal)
    (state : State) : Error storage Program StringResource BoxResource →
      Option (Payload Program StringResource) :=
  match storage with
  | .inline => some
  | .boxed => fun error => ops.currentBox state error.resource

/-- Wrap already evaluated owned fields. The inline case performs no
allocation; the boxed case calls exactly the selected Box::new dependency. -/
def fromPayload (storage : Storage)
    (ops : Ops State Program StringResource BoxResource Terminal) :
    Callback.Run State (Payload Program StringResource)
      (Error storage Program StringResource BoxResource) Empty Terminal :=
  match storage with
  | .inline => fun before payload outcome => outcome = .returned payload before
  | .boxed => Callback.map AnchorErrorOwned.Error.mk ops.newBox

/-- From<AnchorError> moves name/message and all existing diagnostics. -/
def fromAnchor (storage : Storage)
    (ops : Ops State Program StringResource BoxResource Terminal) :
    Callback.Run State (AnchorPayload StringResource)
      (Error storage Program StringResource BoxResource) Empty Terminal :=
  fun before payload => fromPayload storage ops before (.anchor payload)

/-- From<ProgramError> moves the complete dependency value, initializes both
diagnostics to None, and allocates a Box only in boxed releases. -/
def fromProgram (storage : Storage)
    (ops : Ops State Program StringResource BoxResource Terminal) :
    Callback.Run State Program (Error storage Program StringResource BoxResource) Empty Terminal :=
  fun before program => fromPayload storage ops before (.program ⟨program, none, none⟩)

/-- Fixed ErrorCode conversion evaluates name, then Display message, then
the release-selected error wrapper. Normal String and Box allocation effects
are explicit even though custom diagnostic-allocation failure is outside the
shared applicability boundary. -/
def fromCode (storage : Storage)
    (ops : Ops State Program StringResource BoxResource Terminal) :
    Callback.Run State Code (Error storage Program StringResource BoxResource) Empty Terminal :=
  fun before code => Callback.bind ops.copyLiteral
    (fun name afterName => Callback.bind ops.formatLiteral
      (fun message afterMessage => fromAnchor storage ops afterMessage
        ⟨name, code.number, message, none, none⟩) afterName code.message)
    before code.name

/-- Source field order, including the older the owned String of ProgramError. -/
def Payload.strings (programStrings : Program → List StringResource) :
    Payload Program StringResource → List StringResource
  | .anchor value => [value.name, value.message] ++
      AnchorErrorOwned.originStrings value.origin ++ AnchorErrorOwned.comparedStrings value.compared
  | .program value => programStrings value.error ++
      AnchorErrorOwned.originStrings value.origin ++ AnchorErrorOwned.comparedStrings value.compared

/-- Source-order String destruction uses each actual intermediate state. -/
def dropStrings (ops : Ops State Program StringResource BoxResource Terminal)
    (strings : List StringResource) : Callback.Run State Unit Unit Empty Terminal :=
  fun before _ outcome => Owned.cleanup AnchorErrorOwned.noDouble
    (strings.map fun resource state result => ops.dropString state resource result)
    (.returned () before) outcome

/-- Release the owned fields of an error and then its Box, if there is one. An
absent box is not replaced by an arbitrary payload or a successful no-op. -/
def drop (storage : Storage)
    (ops : Ops State Program StringResource BoxResource Terminal) :
    Callback.Run State (Error storage Program StringResource BoxResource) Unit Empty Terminal :=
  match storage with
  | .inline => fun before payload => dropStrings ops (payload.strings ops.programStrings) before ()
  | .boxed => fun before error outcome =>
    ∃ payload, ops.currentBox before error.resource = some payload ∧
      Callback.bind (dropStrings ops (payload.strings ops.programStrings))
        (fun _ after => ops.freeBox after error.resource) before () outcome

/-- In an inline release, converting a program error has exactly the same
state and owned dependency payload, with no Box call hidden in the rule. -/
theorem fromProgram_inline (ops : Ops State Program StringResource BoxResource Terminal)
    (before : State) (program : Program)
    (outcome : Outcome State (Error .inline Program StringResource BoxResource) Empty Terminal) :
    fromProgram .inline ops before program outcome ↔
      outcome = .returned (.program ⟨program, none, none⟩) before := Iff.rfl

/-- In a boxed release, the actual dependency execution supplies the returned
box identity and its current state; no replacement allocation is manufactured. -/
theorem fromProgram_boxed (ops : Ops State Program StringResource BoxResource Terminal)
    (before : State) (program : Program)
    (outcome : Outcome State (Error .boxed Program StringResource BoxResource) Empty Terminal) :
    fromProgram .boxed ops before program outcome ↔
      Callback.map AnchorErrorOwned.Error.mk ops.newBox before
        (.program ⟨program, none, none⟩) outcome := Iff.rfl

/-- Preserve the complete old boxed payload when selecting the newer shared
representation. Only the type constructor changes; no value is projected out. -/
def Payload.ofOwned : AnchorErrorOwned.Payload StringResource → Payload ProgramError.Value
  StringResource
  | .anchor value => .anchor value
  | .program value => .program ⟨value.error, value.origin, value.compared⟩

/-- The inverse translation is available only for the string-free dependency
type of the existing boxed provider. Legacy String-bearing errors cannot use it. -/
def Payload.toOwned : Payload ProgramError.Value StringResource → AnchorErrorOwned.Payload
  StringResource
  | .anchor value => .anchor value
  | .program value => .program ⟨value.error, value.origin, value.compared⟩

@[simp] theorem Payload.toOwned_ofOwned (payload : AnchorErrorOwned.Payload StringResource) :
    (Payload.ofOwned payload).toOwned = payload := by
  cases payload <;> rfl

@[simp] theorem Payload.ofOwned_toOwned (payload : Payload ProgramError.Value StringResource) :
    Payload.ofOwned payload.toOwned = payload := by
  cases payload <;> rfl

/-- Reuse the existing primitive String/Box provider for modern ProgramError.
The same state, identities and callback exits are retained, including each
actual allocation and store. This is not a conversion for legacy program errors. -/
def Ops.fromOwned (ops : AnchorErrorOwned.Ops State StringResource BoxResource Terminal) :
    Ops State ProgramError.Value StringResource BoxResource Terminal where
  currentString := ops.currentString
  currentBox := fun state box => (ops.currentBox state box).map Payload.ofOwned
  programStrings := fun _ => []
  copyLiteral := ops.copyLiteral
  formatLiteral := ops.formatLiteral
  newBox := fun state payload => ops.newBox state payload.toOwned
  writeBox := fun state box payload => ops.writeBox state box payload.toOwned
  dropString := ops.dropString
  freeBox := ops.freeBox

/-- The current comparison field, before any replacement destructor runs. -/
def Payload.compared : Payload Program StringResource → Option (Compared StringResource)
  | .anchor value => value.compared
  | .program value => value.compared

/-- The current origin, before any replacement destructor runs. -/
def Payload.origin : Payload Program StringResource → Option (Origin StringResource)
  | .anchor value => value.origin
  | .program value => value.origin

/-- Change exactly the comparison descriptor, retaining all other fields. -/
def Payload.withCompared (compared : Option (Compared StringResource)) :
    Payload Program StringResource → Payload Program StringResource
  | .anchor value => .anchor { value with compared }
  | .program value => .program { value with compared }

/-- Change exactly the origin descriptor, retaining all other fields. -/
def Payload.withOrigin (origin : Option (Origin StringResource)) :
    Payload Program StringResource → Payload Program StringResource
  | .anchor value => .anchor { value with origin }
  | .program value => .program { value with origin }

/-- Store into the current owned payload. Inline fields remain local values;
boxed fields are read from and written to the same actual allocation. -/
def updatePayload (storage : Storage)
    (ops : Ops State Program StringResource BoxResource Terminal)
    (update : Payload Program StringResource → Payload Program StringResource) :
    Callback.Run State (Error storage Program StringResource BoxResource)
      (Error storage Program StringResource BoxResource) Empty Terminal :=
  match storage with
  | .inline => fun before payload outcome => outcome = .returned (update payload) before
  | .boxed => fun before error outcome =>
    ∃ payload after, ops.currentBox before error.resource = some payload ∧
      ops.writeBox before error.resource (update payload) = some after ∧
      outcome = .returned error after

/-- Assignment first drops the owned strings of the replaced comparison, then
updates the current payload. It neither drops nor recreates the error box. -/
def withCompared (storage : Storage)
    (ops : Ops State Program StringResource BoxResource Terminal)
    (compared : Option (Compared StringResource)) :
    Callback.Run State (Error storage Program StringResource BoxResource)
      (Error storage Program StringResource BoxResource) Empty Terminal :=
  fun before error outcome => ∃ payload, currentPayload storage ops before error = some payload ∧
    Callback.bind (dropStrings ops (AnchorErrorOwned.comparedStrings payload.compared))
      (fun _ after => updatePayload storage ops (Payload.withCompared compared) after error)
      before () outcome

/-- Account origins own a String; replacing one drops exactly that old String
before storing the new origin, in the actual state after its destructor. -/
def withOrigin (storage : Storage)
    (ops : Ops State Program StringResource BoxResource Terminal)
    (origin : Option (Origin StringResource)) :
    Callback.Run State (Error storage Program StringResource BoxResource)
      (Error storage Program StringResource BoxResource) Empty Terminal :=
  fun before error outcome => ∃ payload, currentPayload storage ops before error = some payload ∧
    Callback.bind (dropStrings ops (AnchorErrorOwned.originStrings payload.origin))
      (fun _ after => updatePayload storage ops (Payload.withOrigin origin) after error)
      before () outcome

/-- Pubkey comparison replacement allocates no Strings and retains the actual
error ownership, after releasing any replaced string comparison. -/
def withPubkeys (storage : Storage)
    (ops : Ops State Program StringResource BoxResource Terminal)
    (left right : Solanalib.Runtime.Pubkey) :
    Callback.Run State (Error storage Program StringResource BoxResource)
      (Error storage Program StringResource BoxResource) Empty Terminal :=
  withCompared storage ops (some (.pubkeys left right))

/-- Source filenames are borrowed static data. Only the replaced owned name,
if present, has cleanup; the rest of the payload and storage identity remain. -/
def withSource (storage : Storage)
    (ops : Ops State Program StringResource BoxResource Terminal)
    (source : AnchorError.Source) :
    Callback.Run State (Error storage Program StringResource BoxResource)
      (Error storage Program StringResource BoxResource) Empty Terminal :=
  withOrigin storage ops (some (.source source))

end Solanalib.Specs.Core.AnchorErrorOperations
