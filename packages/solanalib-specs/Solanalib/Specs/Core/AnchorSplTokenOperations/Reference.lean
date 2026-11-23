/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.ExecutionRun

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations.Reference

open Execution

instance (release : Release) : DecidableEq (release.ProgramError Nat) := by
  cases release <;> simp only [Release.ProgramError] <;> infer_instance

instance (release : Release) : Repr (release.ProgramError Nat) := by
  cases release <;> simp only [Release.ProgramError] <;> infer_instance

/-- Distinct owned vectors remain distinct even when their element lengths
coincide. Events record dependency calls, not an allocator implementation. -/
inductive VectorKind where
  | bytes | metas | extensions | remaining
  deriving DecidableEq, Repr

inductive Event where
  | reserve (kind : VectorKind) (capacity : Nat)
  | literal (kind : VectorKind) (length : Nat)
  | push (kind : VectorKind) (resource : Nat)
  | extend (kind : VectorKind) (resource length : Nat)
  | release (kind : VectorKind) (resource : Nat)
  | cloneRc (field : AccountInfoRc.Field) (handle : Borrow.Handle)
  | dropRc (field : AccountInfoRc.Field) (handle : Borrow.Handle)
  | newBox (resource : Nat)
  | invoke
  | getReturnData
  deriving DecidableEq, Repr

structure RecordedCall where
  instruction : Solanalib.Runtime.CpiInstruction
  accounts : List AccountInfo.Value
  signers : List (List Solanalib.Runtime.Bytes)
  seedReference : Option Nat
  counts : List ((AccountInfoRc.Field × Borrow.Handle) × Nat)
  deriving DecidableEq, Repr

structure GetterObservation where
  counts : List ((AccountInfoRc.Field × Borrow.Handle) × Nat)
  bytes : Owned.VectorState UInt8
  metas : Owned.VectorState Solanalib.Runtime.CpiMeta
  deriving DecidableEq, Repr

/-- A concrete shared resource ledger used only as a closed dependency
interpretation. Rc counts, owned payloads and effects have explicit state. -/
structure State (release : Release) where
  bytes : Owned.VectorState UInt8 := []
  metas : Owned.VectorState Solanalib.Runtime.CpiMeta := []
  extensions : Owned.VectorState ExtensionType := []
  remaining : Owned.VectorState AccountInfo.Value := []
  strings : List (Option String) := []
  boxes : List (Option (AnchorErrorOperations.Payload (release.ProgramError Nat) Nat)) := []
  seeds : List (Option (List (List Solanalib.Runtime.Bytes))) := []
  counts : List ((AccountInfoRc.Field × Borrow.Handle) × Nat) := []
  lamports : List (Borrow.Handle × Nat) := []
  dataCells : List (Borrow.Handle × Solanalib.Runtime.Bytes) := []
  events : List Event := []
  calls : List RecordedCall := []
  getters : List GetterObservation := []
  effect : Nat := 0
  deriving DecidableEq, Repr

inductive Reply (Program : Type) where
  | success
  | error (value : Program)
  | unwind (reason : Nat)
  | terminal (reason : Nat)
  deriving DecidableEq, Repr

inductive ReturnData where
  | absent
  | present (program : Solanalib.Runtime.Pubkey) (bytes : Solanalib.Runtime.Bytes)
  | unwind (reason : Nat)
  | terminal (reason : Nat)
  deriving DecidableEq, Repr

structure Script (release : Release) where
  reply : Reply (release.ProgramError Nat) := .success
  returned : ReturnData := .absent
  effect : Nat := 1
  boxTerminal : Option Nat := none
  enumSize : Nat := 128
  writeFirst : Bool := false
  deriving DecidableEq, Repr

variable {release : Release}

def bytesFocus : Owned.Focus (State release) (Owned.VectorState UInt8) where
  get := State.bytes
  set := fun state bytes => { state with bytes }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def metasFocus : Owned.Focus (State release) (Owned.VectorState Solanalib.Runtime.CpiMeta) where
  get := State.metas
  set := fun state metas => { state with metas }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def extensionsFocus : Owned.Focus (State release) (Owned.VectorState ExtensionType) where
  get := State.extensions
  set := fun state extensions => { state with extensions }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def remainingFocus : Owned.Focus (State release) (Owned.VectorState AccountInfo.Value) where
  get := State.remaining
  set := fun state remaining => { state with remaining }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def emit {Value Unwind : Type} (event : Event) :
    Outcome (State release) Value Unwind Nat → Outcome (State release) Value Unwind Nat
  | .returned value state => .returned value { state with events := state.events ++ [event] }
  | .unwound reason state => .unwound reason { state with events := state.events ++ [event] }
  | .terminated reason => .terminated reason

/-- Canonical reference-vector computations with an additional call log. -/
def vectorFn {Element Unwind : Type} (kind : VectorKind)
    (focus : Owned.Focus (State release) (Owned.VectorState Element)) :
    VecFn (State release) Element Nat Unwind Nat :=
  let base : VecFn (State release) Element Nat Unwind Nat := refVec.focus focus
  { withCapacity := fun state capacity => (base.withCapacity state capacity).map (emit (.reserve
    kind capacity))
    fromList := fun state values => (base.fromList state values).map (emit (.literal kind
      values.length))
    push := fun state args => (base.push state args).map (emit (.push kind args.1))
    extend := fun state args => (base.extend state args).map (emit (.extend kind args.1
      args.2.length))
    drop := fun state resource => (base.drop state resource).map (emit (.release kind resource)) }

def relation {S Args Value U T : Type} (function : S → Args → Option (Outcome S Value U T)) :
    Callback.Run S Args Value U T := fun state args final => function state args = some final

def vectorOps {Element Unwind : Type} (kind : VectorKind)
    (focus : Owned.Focus (State release) (Owned.VectorState Element)) :
    Owned.VectorOps (State release) Element Nat Unwind Nat :=
  { (Owned.vectorReference (Unwind := Unwind) (Terminal := Nat)).focus focus with
    withCapacity := relation (vectorFn kind focus).withCapacity
    fromList := relation (vectorFn kind focus).fromList
    push := relation (vectorFn kind focus).push
    extend := relation (vectorFn kind focus).extend
    drop := relation (vectorFn kind focus).drop }

theorem vector_graph {Element Unwind : Type} (kind : VectorKind)
    (focus : Owned.Focus (State release) (Owned.VectorState Element)) :
    VecGraph (U := Unwind) (vectorOps kind focus) (vectorFn kind focus) where
  withCapacity := fun _ _ _ => Iff.rfl
  fromList := fun _ _ _ => Iff.rfl
  push := fun _ _ _ => Iff.rfl
  extend := fun _ _ _ => Iff.rfl
  drop := fun _ _ _ => Iff.rfl

def cloneRcFn (state : State release) (field : AccountInfoRc.Field × Borrow.Handle) :
    Option (Outcome (State release) Unit Empty Nat) := do
  let count ← state.counts.lookup field
  if count = 2^64 - 1 then return .terminated 900
  else return .returned () { state with
    counts := state.counts.map fun (key, value) => (key, if key = field then count + 1 else value)
    events := state.events ++ [.cloneRc field.1 field.2] }

def dropRcFn (state : State release) (field : AccountInfoRc.Field × Borrow.Handle) :
    Option (Outcome (State release) Unit Empty Nat) := do
  let count ← state.counts.lookup field
  if count = 0 then none
  else return .returned () { state with
    counts := state.counts.map fun (key, value) => (key, if key = field then count - 1 else value)
    events := state.events ++ [.dropRc field.1 field.2] }

def rc : AccountInfoRc.Ops (State release) Nat where
  cloneRc := relation cloneRcFn
  dropRc := relation dropRcFn

/-- Remaining-vector destruction invokes both actual Rc field drops for
each element before the vector ledger slot is retired. -/
def dropInfosFn : List AccountInfo.Value → State release → Option (Outcome (State release) Unit
  Empty Nat)
  | [], state => some (.returned () state)
  | info :: rest, state =>
      (dropRcFn state (.lamports, info.lamports)).bind (PGraph.bindK fun _ middle =>
        (dropRcFn middle (.data, info.data)).bind (PGraph.bindK fun _ after => dropInfosFn rest
          after))

def dropRemainingFn (state : State release) (resource : Nat) :
    Option (Outcome (State release) Unit Empty Nat) := do
  let infos ← state.remaining.current resource
  (dropInfosFn infos state).bind (PGraph.bindK fun _ after =>
    (vectorFn .remaining remainingFocus).drop after resource)

def programStrings (release : Release) : release.ProgramError Nat → List Nat :=
  match release with
  | .v027 | .v029 | .v0321 => ProgramErrorOwned.strings
  | .v102 | .v112 => fun _ => []

def newBoxFn (script : Script release) (state : State release)
    (payload : AnchorErrorOperations.Payload (release.ProgramError Nat) Nat) :
    Option (Outcome (State release) Nat Empty Nat) :=
  match script.boxTerminal with
  | some reason => some (.terminated reason)
  | none => some (.returned state.boxes.length { state with
      boxes := state.boxes ++ [some payload], events := state.events ++ [.newBox
        state.boxes.length] })

def errors (script : Script release) :
    AnchorErrorOperations.Ops (State release) (release.ProgramError Nat) Nat Nat Nat where
  currentString := fun state resource => state.strings[resource]?.join
  currentBox := fun state resource => state.boxes[resource]?.join
  programStrings := programStrings release
  copyLiteral := relation fun state text => some (.returned state.strings.length
    { state with strings := state.strings ++ [some text] })
  formatLiteral := relation fun state text => some (.returned state.strings.length
    { state with strings := state.strings ++ [some text] })
  newBox := relation (newBoxFn script)
  writeBox := fun state resource payload => (state.boxes[resource]?.join).map fun _ =>
    { state with boxes := state.boxes.set resource (some payload) }
  dropString := relation fun state resource => (state.strings[resource]?.join).map fun _ =>
    .returned () { state with strings := state.strings.set resource none }
  freeBox := relation fun state resource => (state.boxes[resource]?.join).map fun _ =>
    .returned () { state with boxes := state.boxes.set resource none }

def invokeFn (script : Script release) (seeds : Option Nat) (state : State release)
    (call : CpiRequest.Request AccountInfo.Value) :
    Option (Outcome (State release) (Except (release.ProgramError Nat) Unit) Nat Nat) :=
  let written := if script.writeFirst then
      match call.accounts with
      | [] => state
      | first :: _ => { state with
          lamports := state.lamports.map fun (handle, value) =>
            (handle, if handle = first.lamports then value + 101 else value)
          dataCells := state.dataCells.map fun (handle, bytes) =>
            (handle, if handle = first.data then
              match bytes with
              | [] => []
              | byte :: rest => (byte + 7) :: rest
              else bytes) }
    else state
  let after := { written with
    events := state.events ++ [.invoke]
    calls := state.calls ++ [⟨call.instruction, call.accounts, call.signers, seeds, state.counts⟩]
    effect := state.effect + script.effect }
  match script.reply with
  | .success => some (.returned (.ok ()) after)
  | .error error => some (.returned (.error error) after)
  | .unwind reason => some (.unwound reason after)
  | .terminal reason => some (.terminated reason)

def getReturnDataFn (script : Script release) (state : State release) (_ : Unit) :
    Option (Outcome (State release) (Option (Solanalib.Runtime.Pubkey × Nat)) Nat Nat) :=
  let after := { state with
    events := state.events ++ [.getReturnData]
    getters := state.getters ++ [⟨state.counts, state.bytes, state.metas⟩]
    effect := state.effect + script.effect }
  match script.returned with
  | .absent => some (.returned none after)
  | .present key bytes =>
      let allocated := after.bytes.allocate bytes
      some (.returned (some (key, allocated.1)) { after with bytes := allocated.2 })
  | .unwind reason => some (.unwound reason after)
  | .terminal reason => some (.terminated reason)

def types (binding : Binding) (script : Script binding.release) : Types binding where
  builder := {
    instruction := {
      State := State binding.release
      ByteResource := Nat
      MetaResource := Nat
      Unwind := Nat
      Terminal := Nat
      wordBits := 64
      enumSize := script.enumSize
      bytes := vectorOps .bytes bytesFocus
      metas := vectorOps .metas metasFocus
      doubleUnwind := fun _ first second terminal => some (first + second) = some terminal }
    ExtensionResource := Nat
    extensions := {
      current := fun state resource => state.extensions.current resource
      copySlice := relation (vectorFn .extensions extensionsFocus).fromList
      drop := relation (vectorFn .extensions extensionsFocus).drop } }
  RemainingResource := Nat
  SeedRef := Nat
  StringResource := Nat
  BoxResource := Nat
  rc
  dropRemaining := relation dropRemainingFn
  currentSeeds := fun state resource => state.seeds[resource]?.join
  errors := errors script
  invoke := fun seeds => relation (invokeFn script seeds)
  getReturnData := relation (getReturnDataFn script)

def functions (binding : Binding) (script : Script binding.release) : Functions (types binding
  script) where
  instruction := {
    bytes := vectorFn .bytes bytesFocus
    metas := vectorFn .metas metasFocus
    double := fun _ (first second : Nat) => some (first + second) }
  copyExtensions := (vectorFn .extensions extensionsFocus).fromList
  dropExtensions := (vectorFn .extensions extensionsFocus).drop
  cloneRc := cloneRcFn
  dropRc := dropRcFn
  dropRemaining := dropRemainingFn
  newBox := newBoxFn script
  invoke := invokeFn script
  getReturnData := getReturnDataFn script

theorem graphs (binding : Binding) (script : Script binding.release) : Graph (functions binding
  script) where
  instruction := {
    bytes := vector_graph .bytes bytesFocus
    metas := vector_graph .metas metasFocus
    double := fun _ _ _ _ => Iff.rfl }
  copyExtensions := fun _ _ _ => Iff.rfl
  dropExtensions := fun _ _ _ => Iff.rfl
  cloneRc := fun _ _ _ => Iff.rfl
  dropRc := fun _ _ _ => Iff.rfl
  dropRemaining := fun _ _ _ => Iff.rfl
  newBox := fun _ _ _ => Iff.rfl
  invoke := fun _ _ _ _ => Iff.rfl
  getReturnData := fun _ _ _ => Iff.rfl

/-- Closed computation is connected to the registered raw relation for every
script and every state, including absence of a required local resource. -/
theorem run_iff (binding : Binding) (script : Script binding.release)
    (state : State binding.release) (args : Input (types binding script))
    (outcome : Exit (types binding script)) :
    run (types binding script) state args outcome ↔
      runFn (functions binding script) state args = some outcome :=
  run_graph _ (graphs binding script) state args outcome

end Solanalib.Specs.Core.AnchorSplTokenOperations.Reference
