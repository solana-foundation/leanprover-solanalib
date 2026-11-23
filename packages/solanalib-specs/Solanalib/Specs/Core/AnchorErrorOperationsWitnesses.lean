/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOperationsContracts
public import Solanalib.Specs.Core.AnchorCodecDecoders

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOperations

/-- Restrict an indexed model to an exact source representation. The condition
selects the family index; it is not an unconsumed source-call precondition. -/
def select (family : Family) (condition : family.Index → Prop) : Family where
  Index := { index : family.Index // condition index }
  State := fun index => family.State index.val
  Args := fun index => family.Args index.val
  Value := fun index => family.Value index.val
  Unwind := fun index => family.Unwind index.val
  Terminal := fun index => family.Terminal index.val
  contract := fun index => family.contract index.val

def selectRun (family : Family) (condition : family.Index → Prop)
    (run : FamilyRun family) : FamilyRun (select family condition) := fun index => run index.val

theorem select_reference (family : Family) (condition : family.Index → Prop)
    (run : FamilyRun family) (reference : FamilyReference family run) :
    FamilyReference (select family condition) (selectRun family condition run) :=
  fun index => reference index.val

theorem select_execution (family : Family) (condition : family.Index → Prop)
    (run : FamilyRun family) (sample : family.Index) (selected : condition sample)
    (execution : FamilyHasExecution family run sample) :
    FamilyHasExecution (select family condition) (selectRun family condition run)
      ⟨sample, selected⟩ := execution

/-- Either exact storage representation can use the same owned primitive
reference. The modern dependency type here is only the witness instantiation. -/
abbrev sampleAt (storage : Storage) : Types := { sampleTypes with storage }

theorem fromAnchor_executionAt (storage : Storage) :
    FamilyHasExecution fromAnchorFamily fromAnchorRun (sampleAt storage) := by
  cases storage with
  | inline => exact fromAnchor_hasExecution
  | boxed =>
    refine ⟨AnchorErrorOwned.sampleAnchorState, AnchorErrorOwned.sampleAnchor,
      .returned ⟨⟨0⟩⟩
        (AnchorErrorOwned.Reference.boxResult AnchorErrorOwned.sampleAnchorState
          (.anchor AnchorErrorOwned.sampleAnchor)).2, trivial, ?_⟩
    exact ⟨.returned ⟨0⟩
      (AnchorErrorOwned.Reference.boxResult AnchorErrorOwned.sampleAnchorState
        (.anchor AnchorErrorOwned.sampleAnchor)).2, rfl, rfl⟩

theorem fromProgram_executionAt (storage : Storage) :
    FamilyHasExecution fromProgramFamily fromProgramRun (sampleAt storage) := by
  cases storage with
  | inline => exact fromProgram_hasExecution
  | boxed =>
    refine ⟨AnchorErrorOwned.Reference.initial 1, .invalidAccountData,
      .returned ⟨⟨0⟩⟩
        (AnchorErrorOwned.Reference.boxResult (AnchorErrorOwned.Reference.initial 1)
          (.program ⟨.invalidAccountData, none, none⟩)).2, trivial, ?_⟩
    exact ⟨.returned ⟨0⟩
      (AnchorErrorOwned.Reference.boxResult (AnchorErrorOwned.Reference.initial 1)
        (.program ⟨.invalidAccountData, none, none⟩)).2, rfl, rfl⟩

theorem code_executionAt (storage : Storage) (codes : Array Code) (code : Fin codes.size) :
    FamilyHasExecution (codeFamily codes) (codeRun codes) (sampleAt storage) := by
  cases storage with
  | inline => exact code_hasExecution codes code
  | boxed =>
    let before := AnchorErrorOwned.Reference.initial 3
    let name := AnchorErrorOwned.Reference.stringResult false before codes[code].name
    let message := AnchorErrorOwned.Reference.stringResult true name.2 codes[code].message
    let boxed := AnchorErrorOwned.Reference.boxResult message.2
      (.anchor ⟨name.1, codes[code].number, message.1, none, none⟩)
    refine ⟨before, code, .returned ⟨boxed.1⟩ boxed.2, trivial, ?_⟩
    exact ⟨.returned name.1 name.2, rfl, .returned message.1 message.2, rfl,
      .returned boxed.1 boxed.2, rfl, rfl⟩

/-- A live receiver for the selected storage, with the same initialized name
and message resources in either representation. -/
def receiverAt : (storage : Storage) → (sampleAt storage).Error
  | .inline => samplePayload
  | .boxed => AnchorErrorOwned.sampleError

theorem pubkeys_executionAt (storage : Storage) :
    FamilyHasExecution pubkeysFamily pubkeysRun (sampleAt storage) := by
  cases storage with
  | inline => exact pubkeys_hasExecution
  | boxed =>
    let left := Solanalib.Runtime.Pubkey.ofNat 3
    let right := Solanalib.Runtime.Pubkey.ofNat 4
    let before := AnchorErrorOwned.sampleBoxState
    let updated := (AnchorErrorOwned.Payload.anchor AnchorErrorOwned.sampleAnchor).withPubkeys left
      right
    let after : AnchorErrorOwned.Reference.State := { before with
      boxes := before.boxes.set 0 (some updated)
      events := before.events ++ [.write ⟨0⟩] }
    refine ⟨before, (AnchorErrorOwned.sampleError, left, right),
      .returned AnchorErrorOwned.sampleError after, trivial, ?_⟩
    exact ⟨samplePayload, rfl, .returned () before, rfl,
      samplePayload, after, rfl, rfl, rfl⟩

theorem source_executionAt (storage : Storage) :
    FamilyHasExecution sourceFamily sourceRun (sampleAt storage) := by
  cases storage with
  | inline => exact source_hasExecution
  | boxed =>
    let before := AnchorErrorOwned.sampleBoxState
    let origin : Option (Origin AnchorErrorOwned.Reference.StringId) :=
      some (.source ⟨"source.rs", 7⟩)
    let updated : AnchorErrorOwned.Payload AnchorErrorOwned.Reference.StringId :=
      .anchor { AnchorErrorOwned.sampleAnchor with origin }
    let after : AnchorErrorOwned.Reference.State := { before with
      boxes := before.boxes.set 0 (some updated)
      events := before.events ++ [.write ⟨0⟩] }
    refine ⟨before, (AnchorErrorOwned.sampleError, ⟨"source.rs", 7⟩),
      .returned AnchorErrorOwned.sampleError after, trivial, ?_⟩
    exact ⟨samplePayload, rfl, .returned () before, rfl,
      samplePayload, after, rfl, rfl, rfl⟩

/-- Callback samples retain the finite String/Box heap but select Nat terminal
reasons, allowing an explicit user callback abort independent of allocation. -/
abbrev callbackAt (storage : Storage) : Types :=
  { sampleAt storage with
    Terminal := Nat
    ops := Ops.fromOwned AnchorErrorOwned.Reference.natOps }

def callbackReceiverAt : (storage : Storage) → (callbackAt storage).Error
  | .inline => samplePayload
  | .boxed => AnchorErrorOwned.sampleError

abbrev valuesSampleAt (storage : Storage) : ValuesTypes where
  toTypes := callbackAt storage
  Left := Unit
  Right := Unit
  Unwind := Nat
  callbacks := {
    left := fun _ _ outcome => outcome = .terminated 7
    right := fun _ _ outcome => outcome = .terminated 8
    dropLeft := fun before _ outcome => outcome = .returned () before
    dropRight := fun before _ outcome => outcome = .returned () before
    double := fun _ _ _ terminal => terminal = 9 }

theorem values_executionAt (storage : Storage) :
    FamilyHasExecution valuesFamily valuesRun (valuesSampleAt storage) := by
  refine ⟨AnchorErrorOwned.sampleBoxState, ⟨callbackReceiverAt storage, (), ()⟩,
    .terminated (7 : Nat), trivial, .terminated (7 : Nat), ?_, ?_⟩
  · exact valuesBody_first_terminal _ _ _ _ rfl
  · exact finishMoved_terminal _ _ _ _ _

abbrev nameSampleAt (storage : Storage) : NameTypes where
  toTypes := callbackAt storage
  Name := Unit
  Unwind := Nat
  toString := fun _ _ outcome => outcome = .terminated 7
  dropName := fun before _ outcome => outcome = .returned () before
  double := fun _ _ _ terminal => terminal = 9

theorem name_executionAt (storage : Storage) :
    FamilyHasExecution nameFamily nameRun (nameSampleAt storage) := by
  refine ⟨AnchorErrorOwned.sampleBoxState, (callbackReceiverAt storage, ()),
    .terminated (7 : Nat), trivial, .terminated (7 : Nat), ?_, ?_⟩
  · exact ⟨.terminated 7, rfl, rfl⟩
  · exact finishMoved_terminal _ _ _ _ _

/-- An actual dependency unwind skips the following wrapper allocation of Anchor
and retains the returned state of the consuming IO conversion. -/
theorem io_unwind (types : IoTypes) (before after : types.State)
    (input : types.IoError) (reason : types.Unwind)
    (converted : types.fromIo before input (.unwound reason after)) :
    ioRun types before input (.unwound reason after) := ⟨.unwound reason after, converted, rfl⟩

abbrev ioSample : IoTypes where
  toTypes := callbackAt .boxed
  IoError := Unit
  Unwind := Nat
  fromIo := fun before _ outcome => outcome = .unwound 4
    { before with events := before.events ++ [.dropString ⟨0⟩ "custom IO payload"] }

theorem io_hasExecution : FamilyHasExecution ioFamily ioRun ioSample :=
  ⟨AnchorErrorOwned.sampleBoxState, (), .unwound (4 : Nat)
    { AnchorErrorOwned.sampleBoxState with
      events := AnchorErrorOwned.sampleBoxState.events ++ [.dropString ⟨0⟩ "custom IO \
        payload"] },
    trivial, io_unwind _ _ _ _ _ rfl⟩

theorem io_satisfiable : FamilySatisfiable ioFamily ioSample := io_hasExecution.satisfiable

end Solanalib.Specs.Core.AnchorErrorOperations

namespace Solanalib.Specs.Core.AnchorCodec

abbrev loaderSample : LoaderTypes where
  State := AnchorErrorOwned.Reference.State
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  DecodeError := AnchorErrorOwned.Reference.StringId
  Terminal := AnchorErrorOwned.Reference.Failure
  errors := AnchorErrorOperations.Ops.fromOwned AnchorErrorOwned.Reference.ops
  makeDecodeError := fun before _ => AnchorErrorOwned.Reference.ops.copyLiteral before
    "bincode decode error"
  dropDecodeError := AnchorErrorOwned.Reference.ops.dropString

/-- Successful fixed-width decoding leaves even trailing input untouched. -/
theorem loader_hasExecution : FamilyHasExecution loaderFamily loaderRun loaderSample :=
  ⟨AnchorErrorOwned.Reference.initial 0, [0, 0, 0, 0, 255],
    .returned (.ok .uninitialized, [0, 0, 0, 0, 255]) (AnchorErrorOwned.Reference.initial 0),
    trivial, loader_success _ _ _ _ rfl⟩

theorem loader_satisfiable : FamilySatisfiable loaderFamily loaderSample :=
  loader_hasExecution.satisfiable

end Solanalib.Specs.Core.AnchorCodec
