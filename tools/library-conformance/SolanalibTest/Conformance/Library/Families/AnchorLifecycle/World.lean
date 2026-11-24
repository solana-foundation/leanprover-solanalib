/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.World
import SolanalibTest.Conformance.Library.Families.Anchor.Graph
import Solanalib.Specs.Core.AnchorLifecycleProfiles

/-! Concrete conformance interpretation of the lifecycle primitive interfaces.
The heap retains String and Box identity, the shared account store, Rc owner
counts and callback events. It interprets the tested host execution profile;
it is not a library-body or allocator-correctness theorem. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor

/-- Only the legacy Borsh variant owns an additional String. Other dependency
variants share the existing complete mathematical enum without numeric erasure. -/
inductive Program where
  | plain (value : ProgramError.Value)
  | legacyBorsh (resource : Nat)
  deriving DecidableEq, Repr

def Program.strings : Program → List Nat
  | .plain _ => []
  | .legacyBorsh resource => [resource]

inductive Event where
  | owner
  | id
  | checkOwner (ownerRef : Nat)
  | checkId (key : Solanalib.Runtime.Pubkey)
  | decode (checked : Bool) (bytes : Solanalib.Runtime.Bytes)
  | serialize (value : Nat)
  | write (count : Nat)
  | dropPayload (value : Nat)
  | sysvar (record : Nat)
  | innerAccounts (program : Solanalib.Runtime.Pubkey) (instruction : Solanalib.Runtime.Bytes)
    (remaining : Nat)
  | innerExit (value : Nat) (program : Solanalib.Runtime.Pubkey)
  | innerClose (value : Nat) (destination : AccountInfo.Value)
  deriving DecidableEq, Repr

structure Logged where
  event : Event
  counts : List Nat
  leases : List Lease
  deriving DecidableEq, Repr

abbrev ErrorPayload := AnchorErrorOperations.Payload Program Nat

structure Aux where
  owners : List Solanalib.Runtime.Pubkey
  counts : List Nat
  log : List Logged
  strings : List (Option String)
  boxes : List (Option ErrorPayload)
  payload : Nat
  extraLive : Nat
  programString : Option Nat
  buffers : List (Option AccountInfoSdk.Buffer)
  payloadBoxes : List (Option Nat) := []
  memoryCopies : List Solanalib.Runtime.Bytes := []

abbrev W := AnchorAccount.World Aux
abbrev Out (Value : Type) := Outcome W Value
  (AnchorAccount.ConstructorUnwind String) (AnchorAccount.ConstructorTerminal Unit)
abbrev DepOut (Value : Type) := Outcome W Value Empty Unit
abbrev SigOut (Value : Type) := Outcome W Value String Unit

def ownerAt (aux : Aux) (reference : AccountInfo.OwnerRef) : Solanalib.Runtime.Pubkey :=
  aux.owners.getD reference.id .zero

def sdk : Owned.Focus W AccountInfoSdk.State where
  get := fun state => ⟨state.1, state.2.owners, state.2.buffers⟩
  set := fun state next => (next.borrow, { state.2 with owners := next.owners, buffers :=
    next.buffers })
  get_set := by intro _ next; cases next; rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def payloadFocus : Owned.Focus W Nat where
  get := fun state => state.2.payload
  set := fun state value => (state.1, { state.2 with payload := value })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def currentString (state : W) (resource : Nat) : Option String := state.2.strings[resource]?.join
def currentBox (state : W) (resource : Nat) : Option ErrorPayload := state.2.boxes[resource]?.join

def copyString (state : W) (text : String) : DepOut Nat :=
  .returned state.2.strings.length (state.1, { state.2 with strings := state.2.strings ++ [some
    text] })

def newBox (state : W) (payload : ErrorPayload) : DepOut Nat :=
  .returned state.2.boxes.length (state.1, { state.2 with boxes := state.2.boxes ++ [some payload]
    })

def writeBox (state : W) (resource : Nat) (payload : ErrorPayload) : Option W :=
  (currentBox state resource).map fun _ =>
    (state.1, { state.2 with boxes := state.2.boxes.set resource (some payload) })

def dropString (state : W) (resource : Nat) : Option (DepOut Unit) :=
  (currentString state resource).map fun _ =>
    .returned () (state.1, { state.2 with strings := state.2.strings.set resource none })

def freeBox (state : W) (resource : Nat) : Option (DepOut Unit) :=
  (currentBox state resource).map fun _ =>
    .returned () (state.1, { state.2 with boxes := state.2.boxes.set resource none })

def errors : AnchorErrorOperations.Ops W Program Nat Nat Unit where
  currentString := currentString
  currentBox := currentBox
  programStrings := Program.strings
  copyLiteral := Callback.ofFunction copyString
  formatLiteral := Callback.ofFunction copyString
  newBox := Callback.ofFunction newBox
  writeBox := writeBox
  dropString := fun state resource outcome => dropString state resource = some outcome
  freeBox := fun state resource outcome => freeBox state resource = some outcome

def base (storage : AnchorErrorOperations.Storage) : Base where
  Aux := Aux
  Unwind := String
  Terminal := Unit
  StringResource := Nat
  BoxResource := Nat
  Program := Program
  errorStorage := storage
  errors := errors
  programValue := Program.plain

abbrev Error (storage : AnchorErrorOperations.Storage) := (base storage).Error

def rcStep (increment : Bool) (state : W) (argument : AccountInfoRc.Field × Borrow.Handle) :
    Option (DepOut Unit) :=
  match state.2.counts[argument.2.cell]? with
  | none => none
  | some count =>
    if increment then some (.returned ()
      (state.1, { state.2 with counts := state.2.counts.set argument.2.cell (count + 1) }))
    else match count with
      | 0 => none
      | count + 1 => some (.returned ()
        (state.1, { state.2 with counts := state.2.counts.set argument.2.cell count }))

def rc : AccountInfoRc.Ops W Unit where
  cloneRc := fun state argument outcome => rcStep true state argument = some outcome
  dropRc := fun state argument outcome => rcStep false state argument = some outcome

def push (state : W) (target : AccountInfo.Value) (event : Event) : W :=
  let counts := if state.1.cells.isEmpty then []
    else [state.2.counts.getD target.lamports.cell 0, state.2.counts.getD target.data.cell 0]
  let leases := (List.range state.1.cells.length).map (leaseOf state.1)
  (state.1, { state.2 with log := state.2.log ++ [⟨event, counts, leases⟩] })

def callCount (state : W) (select : Event → Bool) : Nat :=
  state.2.log.countP (fun logged => select logged.event)

def freshLive (state : W) : Nat :=
  state.2.strings.countP (fun value => value.isSome && !(value.getD "").isEmpty) +
    state.2.boxes.countP Option.isSome + state.2.extraLive

def programStringDropped (state : W) : Option Bool :=
  state.2.programString.map fun resource => (currentString state resource).isNone

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
