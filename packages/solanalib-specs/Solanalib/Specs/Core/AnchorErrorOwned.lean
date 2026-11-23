/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorError
public import Solanalib.Specs.Core.ProgramError
public import Solanalib.Specs.Core.OwnedCleanup
public import Solanalib.Specs.Core.OwnedFocus

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOwned

/-- A source location borrows its static filename. An account-name origin owns
a String resource instead. Resource identities are not physical pointers. -/
inductive Origin (StringResource : Type) where
  /-- The borrowed static filename and line of the source. -/
  | source (location : AnchorError.Source)
  /-- A currently owned diagnostic String. -/
  | accountName (name : StringResource)
  deriving DecidableEq, Repr

/-- Compared strings remain identified resources until replaced or dropped. -/
inductive Compared (StringResource : Type) where
  /-- Two owned strings, in tuple declaration order. -/
  | values (left right : StringResource)
  /-- Pubkey comparisons contain no owned String allocation. -/
  | pubkeys (left right : Solanalib.Runtime.Pubkey)
  deriving DecidableEq, Repr

/-- The resource-bearing fields of the unboxed error structure of Anchor. -/
structure AnchorPayload (StringResource : Type) where
  /-- Owned error-name String identity. -/
  name : StringResource
  /-- The numeric error code of the source. -/
  number : UInt32
  /-- Owned error-message String identity. -/
  message : StringResource
  /-- Optional source or owned account-name diagnostic. -/
  origin : Option (Origin StringResource)
  /-- Optional comparison, retaining any owned String identities. -/
  compared : Option (Compared StringResource)
  deriving DecidableEq, Repr

/-- ProgramError 3.0.1 has no owned String payload, including BorshIoError. -/
structure ProgramPayload (StringResource : Type) where
  /-- The unchanged SDK error value. -/
  error : ProgramError.Value
  /-- Optional source or owned account-name diagnostic. -/
  origin : Option (Origin StringResource)
  /-- Optional diagnostic comparison. -/
  compared : Option (Compared StringResource)
  deriving DecidableEq, Repr

/-- Current contents of one identified Box allocation. -/
inductive Payload (StringResource : Type) where
  /-- Boxed AnchorError fields. -/
  | anchor (value : AnchorPayload StringResource)
  /-- Boxed ProgramErrorWithOrigin fields. -/
  | program (value : ProgramPayload StringResource)
  deriving DecidableEq, Repr

/-- An owned-error handle retains its Box identity. Current observations and
retirement are state dependent; merely naming a handle is not a permission. -/
structure Error (BoxResource : Type) where
  /-- The same logical Box across in-place diagnostic replacement. -/
  resource : BoxResource
  deriving DecidableEq, Repr

/-- Fixed literal metadata supplied by the selected generated ErrorCode arm.
Arbitrary user Display implementations require a different callback model. -/
structure Code where
  /-- Literal returned by the generated name arm. -/
  name : String
  /-- The already computed, source-defined numeric code. -/
  number : UInt32
  /-- The fixed Display literal for this selected error code. -/
  message : String
  deriving DecidableEq, Repr

/-- The corresponding pure diagnostic value, before allocation is modeled. -/
def Code.value (code : Code) : AnchorError.AnchorValue :=
  ⟨code.name, code.number, code.message, none, none⟩

/-- Primitive String and Box dependencies, not an opaque SDK error factory.
The selected Global String/Box operations and fixed literal Display arms have
no user unwind callback. Terminal exits and the absence of a finite exit stay
explicit; normal allocation or deallocation is never assumed here. -/
structure Ops (State StringResource BoxResource Terminal : Type) where
  /-- Read the actual current String contents, absent after retirement. -/
  currentString : State → StringResource → Option String
  /-- Read the actual resource-bearing payload of a live Box. -/
  currentBox : State → BoxResource → Option (Payload StringResource)
  /-- The literal-to-String dependency of the generated name arm. -/
  copyLiteral : Callback.Run State String StringResource Empty Terminal
  /-- The String formatting dependency of the selected fixed Display literal. -/
  formatLiteral : Callback.Run State String StringResource Empty Terminal
  /-- Box::new receives the already evaluated resource-bearing fields. -/
  newBox : Callback.Run State (Payload StringResource) BoxResource Empty Terminal
  /-- An in-place Box-payload store. Missing model handles have no store. -/
  writeBox : State → BoxResource → Payload StringResource → Option State
  /-- Drop one current String allocation. -/
  dropString : Callback.Run State StringResource Unit Empty Terminal
  /-- Retire the Box allocation after its fields have been dropped. -/
  freeBox : Callback.Run State BoxResource Unit Empty Terminal

variable {State StringResource BoxResource Terminal : Type}

/-- Read optional owned origins using the current String observations. -/
def observeOrigin (strings : StringResource → Option String) :
    Option (Origin StringResource) → Option (Option AnchorError.Origin)
  | none => some none
  | some (.source location) => some (some (.source location))
  | some (.accountName name) => (strings name).map (some ∘ AnchorError.Origin.accountName)

/-- Read both compared strings in the actual supplied resource state. -/
def observeCompared (strings : StringResource → Option String) :
    Option (Compared StringResource) → Option (Option AnchorError.ComparedValues)
  | none => some none
  | some (.pubkeys left right) => some (some (.pubkeys left right))
  | some (.values left right) => do
      let left ← strings left
      let right ← strings right
      pure (some (.values left right))

/-- Interpret all fields of a live Box payload without saving String snapshots. -/
def Payload.observe (strings : StringResource → Option String) :
    Payload StringResource → Option (AnchorError.Value ProgramError.Value)
  | .anchor value => do
      let name ← strings value.name
      let message ← strings value.message
      let origin ← observeOrigin strings value.origin
      let compared ← observeCompared strings value.compared
      pure (.anchor ⟨name, value.number, message, origin, compared⟩)
  | .program value => do
      let origin ← observeOrigin strings value.origin
      let compared ← observeCompared strings value.compared
      pure (.program ⟨value.error, origin, compared⟩)

/-- Current full error contents; dead boxes or strings are rejected. -/
def current (ops : Ops State StringResource BoxResource Terminal)
    (state : State) (error : Error BoxResource) : Option (AnchorError.Value ProgramError.Value) :=
  (ops.currentBox state error.resource).bind (Payload.observe (ops.currentString state))

/-- Only the owned account-name origin needs String cleanup. -/
def originStrings : Option (Origin StringResource) → List StringResource
  | some (.accountName name) => [name]
  | none | some (.source _) => []

/-- Compared string fields drop left before right. -/
def comparedStrings : Option (Compared StringResource) → List StringResource
  | some (.values left right) => [left, right]
  | none | some (.pubkeys _ _) => []

/-- The comparison field of either current error variant. -/
def Payload.compared : Payload StringResource → Option (Compared StringResource)
  | .anchor value => value.compared
  | .program value => value.compared

/-- String fields in Rust declaration order; numeric and borrowed fields add
no owned cleanup action. -/
def Payload.strings : Payload StringResource → List StringResource
  | .anchor value => [value.name, value.message] ++ originStrings value.origin ++
      comparedStrings value.compared
  | .program value => originStrings value.origin ++ comparedStrings value.compared

/-- Structural storage readiness, separate from a Rust ownership permission.
Duplicate String owners inside one payload are not a valid source value. -/
def Payload.Ready (ops : Ops State StringResource BoxResource Terminal)
    (state : State) (payload : Payload StringResource) : Prop :=
  payload.strings.Nodup ∧ ∀ resource ∈ payload.strings,
    ∃ contents, ops.currentString state resource = some contents

/-- A live represented error with initialized, distinct owned fields. -/
def Ready (ops : Ops State StringResource BoxResource Terminal)
    (state : State) (error : Error BoxResource) : Prop :=
  ∃ payload, ops.currentBox state error.resource = some payload ∧ payload.Ready ops state

/-- Replace only the comparison descriptor of either boxed variant. -/
def Payload.withPubkeys (left right : Solanalib.Runtime.Pubkey) : Payload StringResource → Payload
  StringResource
  | .anchor value => .anchor { value with compared := some (.pubkeys left right) }
  | .program value => .program { value with compared := some (.pubkeys left right) }

/-- With Empty unwind there is no second-unwind policy to invoke. -/
def noDouble : Owned.DoubleUnwind State Empty Terminal := fun _ impossible => nomatch impossible

/-- Execute String drops in exact source order, using each actual intermediate
state. This is the common cleanup engine with a non-unwinding dependency type. -/
def dropStrings (ops : Ops State StringResource BoxResource Terminal)
    (resources : List StringResource) : Callback.Run State Unit Unit Empty Terminal :=
  fun before _ outcome => Owned.cleanup noDouble
    (resources.map (fun resource state result => ops.dropString state resource result))
    (.returned () before) outcome

/-- From<AnchorError> boxes the already constructed owned String fields. -/
def fromAnchor (ops : Ops State StringResource BoxResource Terminal) :
    Callback.Run State (AnchorPayload StringResource) (Error BoxResource) Empty Terminal :=
  fun before payload => Callback.map Error.mk ops.newBox before (.anchor payload)

/-- The generated fixed-code conversion constructs name, then message, then
Box. Terminal exits stop at their actual dependency; they do not run cleanup. -/
def buildCode (ops : Ops State StringResource BoxResource Terminal) :
    Callback.Run State Code (Error BoxResource) Empty Terminal :=
  fun before code => Callback.bind ops.copyLiteral
    (fun name afterName => Callback.bind ops.formatLiteral
      (fun message afterMessage => fromAnchor ops afterMessage
        ⟨name, code.number, message, none, none⟩) afterName code.message)
    before code.name

/-- From<ProgramError> wraps the unchanged value and absent diagnostics before
its Box allocation. ProgramError 3.0.1 contributes no owned String field. -/
def fromProgram (ops : Ops State StringResource BoxResource Terminal) :
    Callback.Run State ProgramError.Value (Error BoxResource) Empty Terminal :=
  fun before error => Callback.map Error.mk ops.newBox before (.program ⟨error, none, none⟩)

/-- Replace diagnostics in the existing Box after dropping the old compared
String fields. The final store reads the Box from the actual post-drop state.
Missing handles are invalid model inputs, not invented SDK error values. -/
def withPubkeys (ops : Ops State StringResource BoxResource Terminal) :
    Callback.Run State (Error BoxResource × Solanalib.Runtime.Pubkey × Solanalib.Runtime.Pubkey)
      (Error BoxResource) Empty Terminal :=
  fun before (error, left, right) outcome =>
    ∃ payload, ops.currentBox before error.resource = some payload ∧
      Callback.bind (dropStrings ops (comparedStrings payload.compared))
        (fun _ afterDrops final => ∃ actual,
          ops.currentBox afterDrops error.resource = some actual ∧
          ∃ after, ops.writeBox afterDrops error.resource (actual.withPubkeys left right) = some
            after ∧
            final = .returned error after) before () outcome

/-- Drop an error from its current Box payload: owned fields in declaration
order, then the Box allocation. A retired handle has no finite second drop. -/
def dropError (ops : Ops State StringResource BoxResource Terminal)
    (error : Error BoxResource) : Owned.DropAction State Empty Terminal :=
  fun before outcome => ∃ payload, ops.currentBox before error.resource = some payload ∧
    Callback.bind (dropStrings ops payload.strings)
      (fun _ afterFields => ops.freeBox afterFields error.resource) before () outcome

/-- Embed only the non-unwinding the existing outcomes of the dependency. -/
def liftOutcome {Value Unwind : Type} :
    Outcome State Value Empty Terminal → Outcome State Value Unwind Terminal
  | .returned value after => .returned value after
  | .unwound impossible _ => nomatch impossible
  | .terminated reason => .terminated reason

/-- Widen the exit vocabulary for an enclosing Owner/codec/CPI callback,
without inventing a dependency unwind, post-state or finite execution. -/
def lift {Args Value Unwind : Type}
    (run : Callback.Run State Args Value Empty Terminal) :
    Callback.Run State Args Value Unwind Terminal :=
  fun before args outcome => ∃ actual, run before args actual ∧ liftOutcome actual = outcome

/-- The cleanup action of a retained error in the enclosing callback vocabulary. -/
def dropErrorLift {Unwind : Type} (ops : Ops State StringResource BoxResource Terminal)
    (error : Error BoxResource) : Owned.DropAction State Unwind Terminal :=
  fun before outcome => lift (fun state (_ : Unit) => dropError ops error state) before () outcome

/-- Focus all primitive operations into one component of an outer world.
Every current observation and finite returned state uses this exact focus. -/
def Ops.focus {Outer Inner : Type} (ops : Ops Inner StringResource BoxResource Terminal)
    (part : Owned.Focus Outer Inner) : Ops Outer StringResource BoxResource Terminal where
  currentString := fun state resource => ops.currentString (part.get state) resource
  currentBox := fun state resource => ops.currentBox (part.get state) resource
  copyLiteral := part.lift ops.copyLiteral
  formatLiteral := part.lift ops.formatLiteral
  newBox := part.lift ops.newBox
  writeBox := fun before resource payload =>
    (ops.writeBox (part.get before) resource payload).map (part.set before)
  dropString := part.lift ops.dropString
  freeBox := part.lift ops.freeBox

end Solanalib.Specs.Core.AnchorErrorOwned
