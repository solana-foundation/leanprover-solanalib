/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Contexts
import SolanalibTest.Conformance.Library.BorshCommon
import Solanalib.Specs.AnchorLang.Idl
import Solanalib.Specs.AnchorLang.bpf_writer
import Solanalib.Specs.AnchorLang.codec_operations

set_option autoImplicit false

open Lean (Json toJson)

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations.Decoders

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorCodec AnchorErrorOperations
open SolanalibTest.Conformance.Library.Families.Anchor

structure State where
  vectors : Owned.VectorState UInt8 := []
  ioErrors : List Borsh.IoError := []
  strings : List (Option String) := []
  boxes : List (Option (Payload ProgramError.Value Nat)) := []
  decodeErrors : List (Option LoaderFailure) := []
  cursor : Solanalib.Runtime.Bytes := []
  callbacks : List String := []

def fresh (state : State) : Nat :=
  (state.vectors.filterMap id |>.filter (fun bytes => !bytes.isEmpty)).length +
    3 * state.ioErrors.length + (state.strings.filterMap id |>.filter (· != "")).length +
    (state.boxes.filterMap id).length + (state.decodeErrors.filterMap id).length

def stringCreated (state : State) (text : String) : Outcome State Nat Empty Empty :=
  .returned state.strings.length { state with strings := state.strings ++ [some text] }

def boxCreated (state : State) (payload : Payload ProgramError.Value Nat) : Outcome State Nat Empty
  Empty :=
  .returned state.boxes.length { state with boxes := state.boxes ++ [some payload] }

def stringDropped (state : State) (owner : Nat) : Option (Outcome State Unit Empty Empty) :=
  ((state.strings[owner]?).join).map fun _ => .returned () {
    state with strings := state.strings.set owner none }

def boxDropped (state : State) (owner : Nat) : Option (Outcome State Unit Empty Empty) :=
  ((state.boxes[owner]?).join).map fun _ => .returned () {
    state with boxes := state.boxes.set owner none }

def ops : Ops State ProgramError.Value Nat Nat Empty where
  currentString := fun state owner => (state.strings[owner]?).join
  currentBox := fun state owner => (state.boxes[owner]?).join
  programStrings := fun _ => []
  copyLiteral := Callback.ofFunction stringCreated
  formatLiteral := Callback.ofFunction stringCreated
  newBox := Callback.ofFunction boxCreated
  writeBox := fun state owner payload => ((state.boxes[owner]?).join).map fun _ =>
    { state with boxes := state.boxes.set owner (some payload) }
  dropString := fun state owner out => stringDropped state owner = some out
  freeBox := fun state owner out => boxDropped state owner = some out

def opsFn : OpsFn State ProgramError.Value Nat Nat Empty where
  copy := fun state text => some (stringCreated state text)
  format := fun state text => some (stringCreated state text)
  newBox := fun state payload => some (boxCreated state payload)
  dropString := stringDropped
  freeBox := boxDropped

theorem opsGraph : OpsGraph ops opsFn where
  copy := PGraph.ofFunction stringCreated
  format := PGraph.ofFunction stringCreated
  newBox := PGraph.ofFunction boxCreated
  dropString := fun _ _ => PGraph.ofOption _
  freeBox := fun _ _ => PGraph.ofOption _

def diagnosticCreated (state : State) (failure : LoaderFailure) : Outcome State Nat Empty Empty :=
  .returned state.decodeErrors.length { state with decodeErrors := state.decodeErrors ++ [some
    failure] }

def diagnosticDropped (state : State) (owner : Nat) : Option (Outcome State Unit Empty Empty) :=
  ((state.decodeErrors[owner]?).join).map fun _ => .returned () {
    state with decodeErrors := state.decodeErrors.set owner none }

abbrev loaderTypes : LoaderTypes := ⟨State, Nat, Nat, Nat, Empty, ops,
  Callback.ofFunction diagnosticCreated, fun state owner out => diagnosticDropped state owner =
    some out⟩

def loaderFn (state : State) (input : Solanalib.Runtime.Bytes) :
    Option (Outcome State (Except loaderTypes.Error LoaderState × Solanalib.Runtime.Bytes) Empty
      Empty) :=
  match decodeLoader input with
  | .ok value => some (.returned (.ok value, input) state)
  | .error error => (some (diagnosticCreated state error)).bind (PGraph.bindK fun original
    allocated =>
      (Fn.fromProgram .boxed opsFn allocated .invalidAccountData).bind (PGraph.bindK fun error
        mapped =>
        (diagnosticDropped mapped original).map (Outcome.map (fun _ => (.error error, input)))))

theorem loaderGraph (state : State) (input : Solanalib.Runtime.Bytes) :
    PGraph
      (bpf_upgradeable_state.UpgradeableLoaderState.try_deserialize_unchecked_run loaderTypes state
        input)
      (loaderFn state input) := by
  unfold
    bpf_upgradeable_state.UpgradeableLoaderState.try_deserialize_unchecked_run
    loaderRun loaderFn
  cases decodeLoader input with
  | ok value => exact PGraph.eq_left _
  | error failure =>
    exact PGraph.bind (PGraph.ofFunction diagnosticCreated state failure) fun original allocated =>
      PGraph.bind (Fn.fromProgram_graph opsGraph .boxed allocated .invalidAccountData) fun error
        mapped =>
        PGraph.map _ (PGraph.ofOption (diagnosticDropped mapped original))

def boxedErrorJson (state : State) (error : AnchorErrorOwned.Error Nat) : Json :=
  match (state.boxes[error.resource]?).join with
  | none => Json.null
  | some (.anchor value) => payloadJson (fun owner => optionJson Json.str
    ((state.strings[owner]?).join)) (.anchor value)
  | some (.program value) => payloadJson (fun owner => optionJson Json.str
    ((state.strings[owner]?).join))
      (.program ⟨.inr value.error, value.origin, value.compared⟩)

def loaderValueJson : LoaderState → Json
  | .uninitialized => variantJson "Uninitialized" []
  | .buffer key => variantJson "Buffer" [optionJson pubkeyJson key]
  | .program key => variantJson "Program" [pubkeyJson key]
  | .programData slot key => variantJson "ProgramData" [toJson slot.toNat, optionJson pubkeyJson
    key]

def loaderProject : Outcome State (Except loaderTypes.Error LoaderState × Solanalib.Runtime.Bytes)
  Empty Empty → String
  | .returned (value, rest) state =>
    (returnedJson (exceptJson (boxedErrorJson state) loaderValueJson value)
      (Json.mkObj [("remaining", bytesJson rest), ("fresh_live", toJson (fresh state))])).compress
  | .unwound impossible _ | .terminated impossible => nomatch impossible

def loaderChecker (function : String) : Checker := ofModel function []
    "Solanalib.Specs.AnchorLang.bpf_upgradeable_state.UpgradeableLoaderState.try_deserializ\
      e_unchecked_run" fun case => do
  let input ← asBytes (← field case.state "remaining")
  let state : State := {}
  let observed ← parseOutcome pure pure (noReason (α := Empty)) (noReason (α := Empty)) case.outcome
  return decideProjected
    (bpf_upgradeable_state.UpgradeableLoaderState.try_deserialize_unchecked_run loaderTypes state
      input)
    _ (loaderGraph state input) loaderProject (observed.map fun
      | .returned value state => (returnedJson value state).compress
      | .unwound impossible _ | .terminated impossible => nomatch impossible) (optionJson Json.str)

/-- The user-supplied unchecked fixture consumes one byte before either its
ordinary return or its actual panic. This is one callback dependency, not an
invented discriminator check in the provided default method. -/
def unchecked (state : State) (_ : Unit) : Outcome State (Except loaderTypes.Error UInt8) String
  Empty :=
  let mode := state.cursor.headD 0
  let after := {
    state with
    cursor := state.cursor.drop 1
    callbacks := state.callbacks ++ ["unchecked"] }
  if mode = 2 then .unwound "unchecked" after
  else if mode = 1 then
    let payload : Payload ProgramError.Value Nat := .program ⟨.invalidAccountData, none, none⟩
    .returned (.error ⟨after.boxes.length⟩) { after with boxes := after.boxes ++ [some payload] }
  else .returned (.ok 17) after

abbrev defaultTypes : DeserializeTypes := ⟨State, Unit, UInt8, loaderTypes.Error, String, Empty,
  Callback.ofFunction unchecked⟩

def defaultProject : Outcome State (Except loaderTypes.Error UInt8) String Empty → String
  | .returned value state =>
    (returnedJson (exceptJson (boxedErrorJson state) (fun byte => toJson byte.toNat) value)
      (Json.mkObj [("remaining", bytesJson state.cursor), ("callbacks", toJson state.callbacks),
        ("fresh_live", toJson (fresh state))])).compress
  | .unwound reason state => (Json.mkObj [("exit", "unwound"), ("reason", toJson reason),
      ("state", Json.mkObj [("remaining", bytesJson state.cursor), ("callbacks", toJson
        state.callbacks),
        ("fresh_live", toJson (fresh state))])]).compress
  | .terminated impossible => nomatch impossible

def defaultChecker (function : String) : Checker := ofModel function []
    "Solanalib.Specs.AnchorLang.AccountDeserialize.try_deserialize_run" fun case => do
  let state : State := {
    cursor := ← asBytes (← field case.state "remaining")
    callbacks := ← asList Json.getStr? (← field case.state "callbacks") }
  let observed ← parseOutcome pure pure some (noReason (α := Empty)) case.outcome
  return decideProjected (AccountDeserialize.try_deserialize_run
    defaultTypes state ())
    _ (PGraph.ofFunction unchecked state ()) defaultProject (observed.map fun
      | .returned value state => (returnedJson value state).compress
      | .unwound reason state => (Json.mkObj [("exit", "unwound"), ("reason", toJson reason),
        ("state", state)]).compress
      | .terminated impossible => nomatch impossible) (optionJson Json.str)

end SolanalibTest.Conformance.Library.Families.AnchorOperations.Decoders

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations.Decoders

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorCodec AnchorErrorOperations
open SolanalibTest.Conformance.Library.Families.Anchor

def vecFocus : Owned.Focus State (Owned.VectorState UInt8) where
  get := State.vectors
  set := fun state vectors => { state with vectors }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def allocateVec (state : State) (bytes : Solanalib.Runtime.Bytes) : Outcome State Nat Empty Empty :=
  .returned state.vectors.length { state with vectors := state.vectors ++ [some bytes] }

def vectors : Owned.VectorOps State UInt8 Nat Empty Empty :=
  { Owned.vectorReference.focus vecFocus with fromList := Callback.ofFunction allocateVec }

def ioCreated (state : State) (error : Borsh.IoError) : Outcome State Nat Empty Empty :=
  .returned state.ioErrors.length { state with ioErrors := state.ioErrors ++ [error] }

abbrev idlTypes : IdlTypes := ⟨State, Nat, Nat, Empty, vectors, Callback.ofFunction ioCreated⟩

def idlFn (state : State) (input : Solanalib.Runtime.Bytes) : Outcome State (Except Nat (IdlValue
  Nat) × Solanalib.Runtime.Bytes) Empty Empty :=
  match decodeIdl input with
  | (.error error, rest) => (ioCreated state error).map (fun owner => (.error owner, rest))
  | (.ok value, rest) => match value with
    | .write [] => let result := vectors.empty state
        .returned (.ok (.write result.1), rest) result.2
    | .write (byte :: bytes) => (allocateVec state (byte :: bytes)).map (fun owner => (.ok (.write
      owner), rest))
    | .create size => .returned (.ok (.create size), rest) state
    | .createBuffer => .returned (.ok .createBuffer, rest) state
    | .setBuffer => .returned (.ok .setBuffer, rest) state
    | .setAuthority key => .returned (.ok (.setAuthority key), rest) state
    | .close => .returned (.ok .close, rest) state
    | .resize size => .returned (.ok (.resize size), rest) state

theorem idlGraph (state : State) (input : Solanalib.Runtime.Bytes) :
    PGraph (idl.IdlInstruction.deserialize_run idlTypes state input)
      (some (idlFn state input)) := by
  unfold idl.IdlInstruction.deserialize_run idlRun idlFn
  generalize decodeIdl input = decoded
  rcases decoded with ⟨result, rest⟩
  cases result with
  | error error => exact PGraph.map _ (PGraph.ofFunction ioCreated state error)
  | ok value => cases value with
    | write bytes => cases bytes with
      | nil => exact PGraph.eq_left _
      | cons byte bytes => exact PGraph.map _ (PGraph.ofFunction allocateVec state (byte :: bytes))
    | create size => exact PGraph.eq_left _
    | createBuffer => exact PGraph.eq_left _
    | setBuffer => exact PGraph.eq_left _
    | setAuthority key => exact PGraph.eq_left _
    | close => exact PGraph.eq_left _
    | resize size => exact PGraph.eq_left _

def idlValueJson (state : State) : IdlValue Nat → Json
  | .create size => variantJson "Create" [toJson size.toNat]
  | .createBuffer => variantJson "CreateBuffer" []
  | .write owner => variantJson "Write" [bytesJson ((Owned.VectorState.current state.vectors
    owner).getD [])]
  | .setBuffer => variantJson "SetBuffer" []
  | .setAuthority key => variantJson "SetAuthority" [pubkeyJson key]
  | .close => variantJson "Close" []
  | .resize size => variantJson "Resize" [toJson size.toNat]

def idlProject : Outcome State (Except Nat (IdlValue Nat) × Solanalib.Runtime.Bytes) Empty Empty →
  String
  | .returned (value, rest) state =>
    (returnedJson (exceptJson (fun owner => (state.ioErrors[owner]?).map
      SolanalibTest.Conformance.Library.Borsh.ioErrorJson
      |>.getD Json.null) (idlValueJson state) value)
      (Json.mkObj [("remaining", bytesJson rest), ("fresh_live", toJson (fresh state))])).compress
  | .unwound impossible _ | .terminated impossible => nomatch impossible

def idlChecker (function : String) : Checker := ofModel function []
    "Solanalib.Specs.AnchorLang.idl.IdlInstruction.deserialize_run" fun case => do
  let input ← asBytes (← field case.state "remaining")
  let state : State := {}
  let observed ← parseOutcome pure pure (noReason (α := Empty)) (noReason (α := Empty)) case.outcome
  return decideProjected (idl.IdlInstruction.deserialize_run idlTypes
    state input)
    _ (idlGraph state input) idlProject (observed.map fun
      | .returned value state => (returnedJson value state).compress
      | .unwound impossible _ | .terminated impossible => nomatch impossible) (optionJson Json.str)

end SolanalibTest.Conformance.Library.Families.AnchorOperations.Decoders
