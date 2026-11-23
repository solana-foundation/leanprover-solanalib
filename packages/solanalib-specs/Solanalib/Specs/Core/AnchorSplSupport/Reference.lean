/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.Continuations

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport.Reference

/-- Events belong to the finite mathematical witness. They expose allocation,
Rc multiplicity, cleanup and the opaque request without executing a callee. -/
inductive Event where
  | allocate (kind : String) (resource : Nat)
  | update (kind : String) (resource : Nat)
  | retire (kind : String) (resource : Nat)
  | cloneRc (field : AccountInfoRc.Field) (cell : Borrow.Handle)
  | dropRc (field : AccountInfoRc.Field) (cell : Borrow.Handle)
  | pda (request : Address.Syscall.PdaRequest)
  | invoke (request : CpiRequest.Request AccountInfo.Value)

/-- The scripted whole invocation can return either Result branch, unwind,
or terminate. It has no implementation body. -/
inductive Reply where
  | ok
  | error (value : ProgramErrorOwned.Value Nat)
  | unwind (reason : String)
  | terminal (reason : String)

/-- Separate finite ledgers retain real logical identities and tombstones.
Effects on accounts and the complete request history share this same state. -/
structure State where
  metas : Owned.VectorState Instruction.Meta := []
  bytes : Owned.VectorState UInt8 := []
  infos : Owned.VectorState AccountInfo.Value := []
  keys : Owned.VectorState Solanalib.Runtime.Pubkey := []
  strings : List (Option String) := []
  creators : List (Option (List Metadata.Creator)) := []
  boxes : List (Option (AnchorErrorOperations.Payload (ProgramErrorOwned.Value Nat) Nat)) := []
  events : List Event := []
  reply : Reply := .ok
  effect : Nat := 0

/-- A focused finite vector ledger, with source primitive effects recorded.
Missing tokens terminate this reference; they never become empty vectors. -/
def vector {Element : Type} (kind : String) (get : State → Owned.VectorState Element)
    (put : State → Owned.VectorState Element → State) :
    Owned.VectorOps State Element Nat String String where
  current := fun state => (get state).current
  empty := fun state =>
    let allocated := (get state).allocate []
    (allocated.1, { put state allocated.2 with events := state.events ++ [.allocate kind
      allocated.1] })
  withCapacity := returnsOf fun state _ =>
    let allocated := (get state).allocate []
    (allocated.1, { put state allocated.2 with events := state.events ++ [.allocate kind
      allocated.1] })
  fromList := returnsOf fun state values =>
    let allocated := (get state).allocate values
    (allocated.1, { put state allocated.2 with events := state.events ++ [.allocate kind
      allocated.1] })
  push := Callback.ofFunction fun state (resource, value) =>
    match (get state).current resource with
    | none => .terminated "missing push target"
    | some values => .returned () { put state ((get state).set resource (some (values ++ [value])))
        with events := state.events ++ [.update kind resource] }
  extend := Callback.ofFunction fun state (resource, values) =>
    match (get state).current resource with
    | none => .terminated "missing extend target"
    | some old => .returned () { put state ((get state).set resource (some (old ++ values)))
        with events := state.events ++ [.update kind resource] }
  drop := Callback.ofFunction fun state resource =>
    match (get state).current resource with
    | none => .terminated "missing drop target"
    | some _ => .returned () { put state ((get state).set resource none)
        with events := state.events ++ [.retire kind resource] }

def metas := vector "metas" State.metas (fun state values => { state with metas := values })
def bytes := vector "bytes" State.bytes (fun state values => { state with bytes := values })
def keys := vector "keys" State.keys (fun state values => { state with keys := values })
def plainInfos := vector "infos" State.infos (fun state values => { state with infos := values })

def rc : AccountInfoRc.Ops State String where
  cloneRc := returnsOf fun state (field, cell) =>
    ((), { state with events := state.events ++ [.cloneRc field cell] })
  dropRc := returnsOf fun state (field, cell) =>
    ((), { state with events := state.events ++ [.dropRc field cell] })

/-- The destructor provider records the two Rc fields of each owned occurrence.
It is a mathematical primitive interpretation, without a Vec body proof. -/
def infoDropEvents (values : List AccountInfo.Value) : List Event :=
  values.flatMap fun value => [.dropRc .lamports value.lamports, .dropRc .data value.data]

def infoCloneEvents (values : List AccountInfo.Value) : List Event :=
  values.flatMap fun value => [.cloneRc .lamports value.lamports, .cloneRc .data value.data]

def infos : Owned.VectorOps State AccountInfo.Value Nat String String :=
  { plainInfos with drop := Callback.ofFunction fun state resource =>
      match state.infos.current resource with
      | none => .terminated "missing info vector"
      | some values => .returned () { state with
          infos := state.infos.set resource none
          events := state.events ++ infoDropEvents values ++ [.retire "infos" resource] } }

def errors : AnchorErrorOperations.Ops State (ProgramErrorOwned.Value Nat) Nat Nat String where
  currentString := fun state resource => state.strings[resource]?.join
  currentBox := fun state resource => state.boxes[resource]?.join
  programStrings := ProgramErrorOwned.strings
  copyLiteral := returnsOf fun state value =>
    (state.strings.length, { state with
      strings := state.strings ++ [some value]
      events := state.events ++ [.allocate "string" state.strings.length] })
  formatLiteral := returnsOf fun state value =>
    (state.strings.length, { state with
      strings := state.strings ++ [some value]
      events := state.events ++ [.allocate "string" state.strings.length] })
  newBox := returnsOf fun state value =>
    (state.boxes.length, { state with
      boxes := state.boxes ++ [some value]
      events := state.events ++ [.allocate "box" state.boxes.length] })
  writeBox := fun state resource value =>
    if state.boxes[resource]?.join |>.isSome then
      some { state with
        boxes := state.boxes.set resource (some value)
        events := state.events ++ [.update "box" resource] }
    else none
  dropString := Callback.ofFunction fun state resource =>
    match state.strings[resource]?.join with
    | none => .terminated "missing string"
    | some _ => .returned () { state with
        strings := state.strings.set resource none
        events := state.events ++ [.retire "string" resource] }
  freeBox := Callback.ofFunction fun state resource =>
    match state.boxes[resource]?.join with
    | none => .terminated "missing box"
    | some _ => .returned () { state with
        boxes := state.boxes.set resource none
        events := state.events ++ [.retire "box" resource] }

def literal : Owned.Array.Provider State AccountInfo.Value Nat String String where
  work := returnsOf fun state (count, values) =>
    (if values.length < count then .evaluate else .finish, state)
  finish := infos.fromList
  cleanupOrder := fun _ values => List.finRange values.length
  drop := AccountInfoRc.lift (AccountInfoRc.dropCall rc)
  retire := returnsOf fun state _ => ((), state)
  double := fun _ _ _ _ => False

def serialize : Callback.Run State Serialization (Except SerializationError Nat) String String :=
  fun state input final => match input.encode with
  | .error error => final = .returned (.error error) state
  | .ok values => Callback.map Except.ok bytes.fromList state values final

def appendBytes : Callback.Run State (Nat × Nat) Unit String String :=
  Callback.ofFunction fun state (destination, source) =>
    match state.bytes.current destination, state.bytes.current source with
    | some left, some right =>
        if destination = source then .terminated "aliased append owners"
        else .returned () { state with
          bytes := (state.bytes.set destination (some (left ++ right))).set source (some []),
          events := state.events ++ [.update "bytes" destination, .update "bytes" source] }
    | _, _ => .terminated "missing append owner"

def extendInfos : Callback.Run State (Nat × Nat) Unit String String :=
  Callback.ofFunction fun state (destination, source) =>
    match state.infos.current destination, state.infos.current source with
    | some left, some right =>
        if destination = source then .terminated "aliased extend owners"
        else .returned () { state with
          infos := (state.infos.set destination (some (left ++ right))).set source none,
          events := state.events ++ [.update "infos" destination, .retire "infos" source] }
    | _, _ => .terminated "missing extend owner"

def cloneExtendInfos : Callback.Run State (Nat × List AccountInfo.Value) Unit String String :=
  Callback.ofFunction fun state (destination, values) =>
    match state.infos.current destination with
    | none => .terminated "missing clone-extend target"
    | some old => .returned () { state with
        infos := state.infos.set destination (some (old ++ values))
        events := state.events ++ infoCloneEvents values ++ [.update "infos" destination] }

abbrev resources : Resources where
  State := State
  MetaResource := Nat
  ByteResource := Nat
  InfoResource := Nat
  KeyResource := Nat
  StringResource := Nat
  CreatorResource := Nat
  BoxResource := Nat
  ProgramError := ProgramErrorOwned.Value Nat
  Unwind := String
  Terminal := String
  metas := metas
  bytes := bytes
  infos := infos
  infoLiteral := literal
  keys := keys
  creatorCurrent := fun state resource => state.creators[resource]?.join
  creatorDrop := Callback.ofFunction fun state resource =>
    match state.creators[resource]?.join with
    | none => .terminated "missing creators"
    | some _ => .returned () { state with
        creators := state.creators.set resource none
        events := state.events ++ [.retire "creators" resource] }
  rc := rc
  errors := errors
  appendBytes := appendBytes
  extendInfos := extendInfos
  cloneExtendInfos := cloneExtendInfos
  serialize := serialize
  unwrapSerialization := Callback.ofFunction fun state _ => .unwound "serialization" state
  pda := returnsOf fun state request =>
    (⟨0, some (.ofNat 77), 254⟩, { state with events := state.events ++ [.pda request] })
  zeroPda := returnsOf fun state request =>
    (⟨0, .ofNat 77, 254⟩, { state with events := state.events ++ [.pda request] })
  pdaPanic := Callback.ofFunction fun state _ => .unwound "pda" state
  doubleUnwind := fun _ _ _ _ => False

def invoke : CpiRequest.Invocation State AccountInfo.Value (ProgramErrorOwned.Value Nat) String
  String :=
  Callback.ofFunction fun state request =>
    let after := { state with events := state.events ++ [.invoke request], effect := state.effect +
      1 }
    match state.reply with
    | .ok => .returned (.ok ()) after
    | .error value => .returned (.error value) after
    | .unwind reason => .unwound reason after
    | .terminal reason => .terminated reason

abbrev types : Types := ⟨resources, invoke⟩

end Solanalib.Specs.Core.AnchorSplSupport.Reference
