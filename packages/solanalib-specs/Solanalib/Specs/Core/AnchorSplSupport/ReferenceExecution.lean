/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.ReferenceFacts
public import Solanalib.Specs.Core.AnchorSplSupport.ExecutionRun

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport.Reference

open Execution

/-- A computable value accompanied by an exact finite relation certificate.
Proof erasure leaves the computation; no choice or assumed graph is used. -/
abbrev Computed {O : Type} (relation : O → Prop) := { value : Option O // PGraph relation value }

def serializeComputed (before : State) (input : Serialization) :
    Computed (serializeBytes resources before input) := by
  cases encoded : input.encode with
  | error failure =>
    refine ⟨some (.unwound "serialization" before), ?_⟩
    intro outcome
    simp [serializeBytes, resources, serialize, encoded, Callback.bind, Callback.map,
      Callback.ofFunction, Outcome.map, eq_comm]
  | ok values =>
    refine ⟨some (.returned before.bytes.length
      { before with bytes := before.bytes ++ [some values]
                    events := before.events ++ [.allocate "bytes" before.bytes.length] }), ?_⟩
    intro outcome
    simp [serializeBytes, resources, serialize, encoded, bytes, vector, Callback.bind, Callback.map,
      returns_exact, Owned.VectorState.allocate, Outcome.map, eq_comm]

def findComputed (profile : Profile) (before : State) (inputs : Address.Syscall.PdaInputs) :
    Computed (resources.find profile before inputs) := by
  cases profile with
  | legacyInline | legacyBoxed =>
    refine ⟨some (.returned (.ofNat 77, 254)
      { before with events := before.events ++ [.pda (Address.Operations.zeroFindRequest inputs)]
        }), ?_⟩
    intro outcome
    simp [Resources.find, resources, Address.Operations.zeroFindRun,
      Address.Operations.zeroFindDecode,
      Address.Syscall.finishFind, Callback.bind, Callback.map, returns_exact, Outcome.map, eq_comm]
  | modern =>
    refine ⟨some (.returned (.ofNat 77, 254)
      { before with events := before.events ++ [.pda (Address.Syscall.pdaRequest inputs)] }), ?_⟩
    intro outcome
    simp [Resources.find, resources, Address.Syscall.findRun, Address.Syscall.tryRun,
      Address.Syscall.decodePda,
      Address.Syscall.finishFind, Callback.bind, returns_exact, eq_comm]

def convertComputed (profile : Profile) (before : State) (program : ProgramErrorOwned.Value Nat) :
    Computed (AccountInfoRc.lift
      (AnchorErrorOperations.fromProgram profile.storage errors) before program :
      Outcome State (Error resources profile) String String → Prop) := by
  cases profile with
  | legacyInline =>
    refine ⟨some (.returned (.program ⟨program, none, none⟩) before), ?_⟩
    exact PGraph.exists_eq AccountInfoRc.liftOutcome (PGraph.eq_left _)
  | legacyBoxed | modern =>
    refine ⟨some (.returned ⟨before.boxes.length⟩
      { before with boxes := before.boxes ++ [some (.program ⟨program, none, none⟩)]
                    events := before.events ++ [.allocate "box" before.boxes.length] }), ?_⟩
    exact PGraph.exists_eq AccountInfoRc.liftOutcome (PGraph.map AnchorErrorOwned.Error.mk
      (returns_graph
        (fun (state : State) (payload : AnchorErrorOperations.Payload (ProgramErrorOwned.Value Nat)
          Nat) =>
          (state.boxes.length, { state with
            boxes := state.boxes ++ [some payload]
            events := state.events ++ [.allocate "box" state.boxes.length] }))
        before (.program ⟨program, none, none⟩)))

def primitiveComputed {A V : Type} (primitive : Primitive types A V) (before : State) (args : A) :
    Computed (primitive.run before args) := by
  cases primitive <;>
    dsimp only [Computed, Primitive.run, types, resources, metas, bytes, keys, infos, plainInfos,
      vector, appendBytes, extendInfos, cloneExtendInfos, invoke, errors]
  case metaCapacity => exact ⟨_, returns_graph _ _ _⟩
  case metaList => exact ⟨_, returns_graph _ _ _⟩
  case metaPush => exact ⟨_, PGraph.ofFunction _ _ _⟩
  case metaExtend => exact ⟨_, PGraph.ofFunction _ _ _⟩
  case metaDrop => exact ⟨_, PGraph.ofFunction _ _ _⟩
  case byteList => exact ⟨_, returns_graph _ _ _⟩
  case byteDrop => exact ⟨_, PGraph.ofFunction _ _ _⟩
  case infoPush => exact ⟨_, PGraph.ofFunction _ _ _⟩
  case infoDrop => exact ⟨_, PGraph.ofFunction _ _ _⟩
  case keyList => exact ⟨_, returns_graph _ _ _⟩
  case keyDrop => exact ⟨_, PGraph.ofFunction _ _ _⟩
  case serialize => exact serializeComputed before args
  case find profile => exact findComputed profile before args
  case singleton =>
    exact ⟨_, PGraph.congr (PGraph.eq_left _) (fun outcome => singleton_exact before args outcome)⟩
  case cloneInfo =>
    exact ⟨_, PGraph.congr (PGraph.eq_left _) (fun outcome => clone_exact before args outcome)⟩
  case dropInfo =>
    exact ⟨_, PGraph.congr (PGraph.eq_left _) (fun outcome => drop_exact before args outcome)⟩
  case appendBytes => exact ⟨_, PGraph.ofFunction _ _ _⟩
  case extendInfos => exact ⟨_, PGraph.ofFunction _ _ _⟩
  case cloneExtendInfos => exact ⟨_, PGraph.ofFunction _ _ _⟩
  case stringDrop =>
    exact ⟨_, PGraph.exists_eq AccountInfoRc.liftOutcome (PGraph.ofFunction _ _ _)⟩
  case creatorDrop =>
    exact ⟨_, PGraph.exists_eq AccountInfoRc.liftOutcome (PGraph.ofFunction _ _ _)⟩
  case convert profile => exact convertComputed profile before args
  case invoke => exact ⟨_, PGraph.ofFunction _ _ _⟩

theorem withdraw_literal_exact (before : State) (accounts : WithdrawAccounts)
    (outcome : Outcome State Nat (Owned.Array.Failure × String) String) :
    withdrawLiteral resources accounts before outcome ↔
      outcome = .returned before.infos.length (infoAllocated before accounts.moved) := by
  let evaluate : Run resources Nat AccountInfo.Value := fun state index produced =>
    match accounts.moved[index]? with
    | some value => produced = .returned value state
    | none => False
  change Owned.Array.Trace resources.literalProvider 5 evaluate [] before outcome ↔ _
  exact (literal_step 5 evaluate [] before before accounts.stake (by simp) (fun _ => Iff.rfl)
    outcome).trans <|
    (literal_step 5 evaluate [accounts.stake] before before accounts.destination (by simp) (fun _
      => Iff.rfl) outcome).trans <|
    (literal_step 5 evaluate [accounts.stake, accounts.destination] before before accounts.clock
      (by simp) (fun _ => Iff.rfl) outcome).trans <|
    (literal_step 5 evaluate [accounts.stake, accounts.destination, accounts.clock] before before
      accounts.stakeHistory
      (by simp) (fun _ => Iff.rfl) outcome).trans <|
    (literal_step 5 evaluate [accounts.stake, accounts.destination, accounts.clock,
      accounts.stakeHistory]
      before before accounts.withdrawer (by simp) (fun _ => Iff.rfl) outcome).trans
    (literal_done 5 evaluate accounts.moved before rfl outcome)

def functions : Functions types where
  primitive := fun primitive before args => (primitiveComputed primitive before args).val
  literal := fun before accounts => some (.returned before.infos.length (infoAllocated before
    accounts.moved))
  double := fun _ _ _ => none

theorem graphs : Graph functions where
  primitive := fun primitive before args => (primitiveComputed primitive before args).property
  literal := fun before accounts =>
    PGraph.congr (PGraph.eq_left _) (fun outcome => withdraw_literal_exact before accounts outcome)
  double := fun _ _ _ => PGraph.false

end Solanalib.Specs.Core.AnchorSplSupport.Reference
