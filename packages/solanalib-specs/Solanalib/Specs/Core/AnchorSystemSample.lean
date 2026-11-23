/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSystemRun
public import Solanalib.Specs.Core.InstructionBuilderSample
public import Solanalib.Specs.Core.OwnedVector
public import Solanalib.Specs.Core.OwnedFocus

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSystem.Sample

/-- A finite consistency interpretation. The constructor owns two slot
ledgers; the context owns a third. Rc events preserve every moved occurrence.
Boxes retain complete errors, and invocation effects live in the same state.
This is not a Rust allocator or a runtime/callee implementation. -/
structure State (Program : Type) where
  /-- The current meta and byte vectors allocated by instruction construction. -/
  construction : InstructionBuilder.Sample.State := {}
  /-- Current remaining-account vectors, with consumed slots marked absent. -/
  remaining : Owned.VectorState AccountInfo.Value := []
  /-- Ordered Rc releases, retaining repeated aliases as separate occurrences. -/
  rcEvents : List AccountInfoRc.Event := []
  /-- Current complete error payloads indexed by box identity. -/
  boxes : List (Option (AnchorErrorOperations.Payload Program Nat)) := []
  /-- Current owned String contents indexed by resource identity. -/
  strings : List (Option String) := []
  /-- The exact requests received by the opaque provider of this sample. -/
  calls : List (CpiRequest.Request AccountInfo.Value) := []
  /-- Ordered state effects of the scripted providers. -/
  effects : List Nat := []

/-- Select only the instruction resource ledger, preserving all ambient fields. -/
def constructionFocus (Program : Type) : Owned.Focus (State Program)
  InstructionBuilder.Sample.State where
  get := State.construction
  set := fun state part => { state with construction := part }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Select the actual remaining-account vector ledger. -/
def remainingFocus (Program : Type) : Owned.Focus (State Program) (Owned.VectorState
  AccountInfo.Value) where
  get := State.remaining
  set := fun state part => { state with remaining := part }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- All resource identities and finite exit reasons in this sample are naturals. -/
abbrev types (Program : Type) : Types := ⟨State Program, Nat, Nat, Nat, Nat, Nat, Nat⟩

/-- A codec/allocator sample using exact System bytes and the existing
instruction-builder ledger, focused into the whole wrapper state. -/
def builder (Program : Type) : InstructionBuilder.Providers (types Program).builder where
  metaVec := InstructionBuilder.Sample.metaVec.focus (constructionFocus Program)
  byteVec := InstructionBuilder.Sample.byteVec.focus (constructionFocus Program)
  serialize := (constructionFocus Program).lift
    (InstructionBuilder.Sample.providers Data Data.bytes).serialize
  unwrapFailure := (constructionFocus Program).lift
    (InstructionBuilder.Sample.providers Data Data.bytes).unwrapFailure
  doubleUnwind := fun _ first later terminal => terminal = first + later + 1000

/-- One actual Rc drop event. An event denotes one owner, not one distinct key. -/
def dropRc {Program : Type} (state : State Program)
    (field : AccountInfoRc.Field) (handle : Borrow.Handle) : State Program :=
  { state with rcEvents := state.rcEvents ++ [.drop field handle] }

/-- Both independently reference-counted fields are released in source order. -/
def dropInfoState {Program : Type} (state : State Program) (info : AccountInfo.Value) : State
  Program :=
  dropRc (dropRc state .lamports info.lamports) .data info.data

/-- Drop all AccountInfo occurrences, retaining their order and aliases. -/
def dropInfos {Program : Type} (state : State Program) (infos : List AccountInfo.Value) : State
  Program :=
  infos.foldl dropInfoState state

/-- The provider of the vector owns both its current elements and allocation. The
sample observes those elements at drop time, not at context construction. -/
def dropRemaining {Program : Type} (state : State Program) (resource : Nat) : State Program :=
  let after := dropInfos state ((state.remaining.current resource).getD [])
  { after with remaining := after.remaining.set resource none }

/-- Concrete consistency providers; invalid/stale resources are not a source
admission claim. Positive controls start from live, distinct owned slots. -/
def resources (Program : Type) : Resources where
  types := types Program
  builder := builder Program
  remaining := { (Owned.vectorReference (Element := AccountInfo.Value) (Unwind := Nat)
    (Terminal := Nat)).focus (remainingFocus Program) with
    drop := Callback.ofFunction fun state resource => .returned () (dropRemaining state resource) }
  rc := {
    cloneRc := Callback.ofFunction fun state (field, handle) =>
      .returned () { state with rcEvents := state.rcEvents ++ [.clone field handle] }
    dropRc := Callback.ofFunction fun state (field, handle) => .returned () (dropRc state field
      handle) }

/-- Actual program-owned String fields for each source profile. -/
def programStrings (profile : Profile) : profile.Program Nat → List Nat :=
  match profile with
  | .inlineLegacy | .boxedLegacy => ProgramErrorOwned.strings
  | .boxedModern => fun _ => []

/-- A finite error resource interpretation. The converter of the wrapper uses only
newBox; the other fields support observations and eventual caller cleanup. -/
def errors (profile : Profile) : AnchorErrorOperations.Ops
    (State (profile.Program Nat)) (profile.Program Nat) Nat Nat Nat where
  currentString := fun state resource => state.strings[resource]?.join
  currentBox := fun state resource => state.boxes[resource]?.join
  programStrings := programStrings profile
  copyLiteral := Callback.ofFunction fun state value =>
    .returned state.strings.length { state with strings := state.strings ++ [some value] }
  formatLiteral := Callback.ofFunction fun state value =>
    .returned state.strings.length { state with strings := state.strings ++ [some value] }
  newBox := Callback.ofFunction fun state value =>
    .returned state.boxes.length { state with boxes := state.boxes ++ [some value] }
  writeBox := fun state resource value =>
    if resource < state.boxes.length then some { state with boxes := state.boxes.set resource (some
      value) }
    else none
  dropString := Callback.ofFunction fun state resource =>
    .returned () { state with strings := state.strings.set resource none }
  freeBox := Callback.ofFunction fun state resource =>
    .returned () { state with boxes := state.boxes.set resource none }

/-- A source-selected consistency index whose provider records its exact
request and returns success. Other tests replace this one explicit provider. -/
def index (profile : Profile) : Index profile where
  resources := resources (profile.Program Nat)
  StringResource := Nat
  BoxResource := Nat
  errors := errors profile
  invoke := Callback.ofFunction fun state current =>
    .returned (.ok ()) { state with calls := state.calls ++ [current], effects := state.effects ++
      [70] }

/-- Distinct keys and stable Rc cell identities used by the closed witnesses. -/
def info (number : Nat) : AccountInfo.Value :=
  { AccountInfo.sampleInfo with
    key := .ofNat number
    lamports := ⟨2 * number⟩
    data := ⟨2 * number + 1⟩
    ownerRef := ⟨number⟩ }

/-- One retained remaining vector, with a repeated alias to exercise ownership
multiplicity separately from key identity. -/
def before (profile : Profile) : State (profile.Program Nat) where
  remaining := [some [info 3, info 1, info 3]]

/-- Sample arguments use a deliberately unrelated context program and nested
seeds containing empty and repeated slices. Neither is silently normalized. -/
def args (profile : Profile) (operation : Operation) :
    Args (index profile).resources profile.context operation where
  accounts := match operation with
    | .allocate | .assign => info 1
    | .createAccount | .transfer => (info 1, info 2)
  remaining := (0 : Nat)
  program := match profile with
    | .inlineLegacy | .boxedLegacy => info 9
    | .boxedModern => _root_.Solanalib.Runtime.Pubkey.ofNat 9
  signerSeeds := [[[1, 2], [], [1, 2]], [[255]]]
  parameters := match operation with
    | .allocate => (8193 : UInt64)
    | .assign => _root_.Solanalib.Runtime.Pubkey.ofNat 23
    | .createAccount => ((37 : UInt64), (4097 : UInt64), _root_.Solanalib.Runtime.Pubkey.ofNat 23)
    | .transfer => (37 : UInt64)

/-- The actual state following the meta allocation of this sample. -/
def afterMeta {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat)) (input : Args (index profile).resources profile.context
      operation) :
    State (profile.Program Nat) :=
  { state with construction := InstructionBuilder.Sample.allocateMetas state.construction (metas
    input) }

/-- The actual state following System enum serialization. -/
def afterBuild {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat)) (input : Args (index profile).resources profile.context
      operation) :
    State (profile.Program Nat) :=
  let middle := afterMeta state input
  { middle with
    construction := InstructionBuilder.Sample.afterSerialize Data.bytes .bincode
      middle.construction (data input) }

/-- The two exact fresh vector identities returned by sample construction. -/
def builtValue {profile : Profile} (state : State (profile.Program Nat)) :
    InstructionBuilder.Value (index profile).resources.types.builder :=
  ⟨Instruction.systemProgramId, state.construction.metas.length, state.construction.bytes.length⟩

/-- The successful meta allocation and serialization are actual dependency
executions, including their resource identities and intermediate state. -/
theorem build_returns {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat)) (input : Args (index profile).resources profile.context
      operation) :
    build state input (.returned (builtValue state) (afterBuild state input)) := by
  apply InstructionBuilder.allocateRun_of_returned (index profile).resources.types.builder .bincode
    state (afterMeta state input) (allocation input)
    state.construction.metas.length _
  · exact ⟨.returned state.construction.metas.length
      (InstructionBuilder.Sample.allocateMetas state.construction (metas input)), rfl, rfl⟩
  · apply InstructionBuilder.run_of_serialized
    exact ⟨.returned (.ok state.construction.bytes.length)
      (InstructionBuilder.Sample.afterSerialize Data.bytes .bincode
        (afterMeta state input).construction (data input)), rfl, rfl⟩

/-- No alternate constructor result is introduced by the concrete function
providers of this sample. This is a model fact, not a Rust determinism claim. -/
theorem build_exact {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat)) (input : Args (index profile).resources profile.context
      operation)
    (outcome : Outcome (State (profile.Program Nat))
      (InstructionBuilder.Value (index profile).resources.types.builder) Nat Nat) :
    build state input outcome ↔ outcome = .returned (builtValue state) (afterBuild state input) :=
      by
  constructor
  · rintro ⟨first, ⟨inner, firstCall, firstLift⟩, continuation⟩
    change Outcome.returned state.construction.metas.length
      (InstructionBuilder.Sample.allocateMetas state.construction (metas input)) = inner
        at firstCall
    subst inner
    cases firstLift
    obtain ⟨pending, ⟨serialized, ⟨inner, serializeCall, serializeLift⟩, returned⟩, guarded⟩ :=
      continuation
    change Outcome.returned (.ok state.construction.bytes.length)
      (InstructionBuilder.Sample.afterSerialize Data.bytes .bincode
        (afterMeta state input).construction (data input)) = inner at serializeCall
    subst inner
    cases serializeLift
    cases returned
    exact guarded
  · rintro rfl
    exact build_returns state input

/-- Every reached successful constructor in the finite sample is readable.
This closes the family precondition rather than assuming a successful build. -/
theorem build_ready {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat)) (input : Args (index profile).resources profile.context
      operation) :
    BuildReady state input := by
  intro value after completed
  have exactResult := (build_exact state input (.returned value after)).mp completed
  cases exactResult
  constructor
  · refine ⟨metas input, ?_⟩
    simp [index, resources, builder, Owned.VectorOps.focus, constructionFocus,
      afterBuild, afterMeta, builtValue, InstructionBuilder.Sample.metaVec,
      InstructionBuilder.Sample.metasAt, InstructionBuilder.Sample.allocateMetas,
      InstructionBuilder.Sample.afterSerialize]
  · refine ⟨(data input).bytes, ?_⟩
    simp [index, resources, builder, Owned.VectorOps.focus, constructionFocus,
      afterBuild, afterMeta, builtValue, InstructionBuilder.Sample.byteVec,
      InstructionBuilder.Sample.bytesAt, InstructionBuilder.Sample.allocateMetas,
      InstructionBuilder.Sample.afterSerialize]

/-- The provider of the sample receives exactly the intended encoded request. -/
theorem request_exact {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat)) (input : Args (index profile).resources profile.context
      operation) :
    request (afterBuild state input) input (builtValue state) =
      some ⟨instruction input, movedAccounts input, input.signerSeeds⟩ := by
  apply request_of_encoded _ _ _ rfl
  · simp [index, resources, builder, Owned.VectorOps.focus, constructionFocus,
      afterBuild, afterMeta, builtValue, InstructionBuilder.Sample.metaVec,
      InstructionBuilder.Sample.metasAt, InstructionBuilder.Sample.allocateMetas,
      InstructionBuilder.Sample.afterSerialize]
  · simp [index, resources, builder, Owned.VectorOps.focus, constructionFocus,
      afterBuild, afterMeta, builtValue, InstructionBuilder.Sample.byteVec,
      InstructionBuilder.Sample.bytesAt, InstructionBuilder.Sample.allocateMetas,
      InstructionBuilder.Sample.afterSerialize]

end Solanalib.Specs.Core.AnchorSystem.Sample
