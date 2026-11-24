/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TransferHookResolutionFacts
public import Solanalib.Specs.Core.TransferHookResolutionSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.TransferHookResolution.Sample

open Token (Error Bytes)
open Token.AllocatedControl

def validationKey : Solanalib.Runtime.Pubkey := .ofBytes [2]
def programInfo : AccountInfo.Value := { AccountInfo.sampleInfo with key := .ofBytes [1] }
def reply : Address.Operations.ZeroFindReply := ⟨0, validationKey, 251⟩
def sampleTypes : Types := types reply

/-- Four moved aliases, a borrowed additional owner and one outside owner of
each represented Rc. The preexisting byte vector of the caller is retained. -/
def initialState : State :=
  (AccountInfo.sampleState, {
    bytes := [some [42, 43]]
    metas := [some []]
    infos := [some []]
    rcOwners := [6, 6] })

def args : Args sampleTypes where
  instruction := ⟨.zero, (0 : Nat), (0 : Nat)⟩
  infos := (0 : Nat)
  programId := programInfo.key
  source := AccountInfo.sampleInfo
  mint := AccountInfo.sampleInfo
  destination := AccountInfo.sampleInfo
  authority := AccountInfo.sampleInfo
  amount := 23
  additional := [programInfo]

/-- A whole AccountInfo clone updates lamports Rc before data Rc. -/
def cloneAfter (state : State) (info : AccountInfo.Value) : State :=
  rcAfter true (rcAfter true state .lamports info.lamports) .data info.data

/-- A whole AccountInfo drop updates lamports Rc before data Rc. -/
def dropAfter (state : State) (info : AccountInfo.Value) : State :=
  rcAfter false (rcAfter false state .lamports info.lamports) .data info.data

/-- Both ordered clone calls lie inside the domain of the finite sample provider. -/
def cloneReady (state : State) (info : AccountInfo.Value) : Prop :=
  rcReady true state info.lamports ∧
    rcReady true (rcAfter true state .lamports info.lamports) info.data

/-- Both ordered field drops have a represented live owner to consume. -/
def dropReady (state : State) (info : AccountInfo.Value) : Prop :=
  rcReady false state info.lamports ∧
    rcReady false (rcAfter false state .lamports info.lamports) info.data

theorem clone_call_returns (state : State) (info : AccountInfo.Value) (ready : cloneReady state
  info) :
    AccountInfoRc.cloneCall rcOps state info (.returned info (cloneAfter state info)) :=
  ⟨.returned () (rcAfter true state .lamports info.lamports), ⟨ready.1, rfl⟩,
    .returned () (cloneAfter state info), ⟨ready.2, rfl⟩, rfl⟩

/-- Lift the actual Rc clone into the outcome vocabulary of the array evaluator. -/
theorem clone_lift_returns (state : State) (info : AccountInfo.Value) (ready : cloneReady state
  info) :
    AccountInfoRc.lift (AccountInfoRc.cloneCall rcOps) state info
      (.returned info (cloneAfter state info) : Outcome State AccountInfo.Value Nat Nat) :=
  ⟨.returned info (cloneAfter state info), clone_call_returns state info ready, rfl⟩

theorem clone_info_returns (state : State) (info : AccountInfo.Value) (ready : cloneReady state
  info) :
    cloneInfo sampleTypes info state (.returned (.ok info) (cloneAfter state info)) :=
  ⟨.returned info (cloneAfter state info),
    ⟨.returned info (cloneAfter state info), clone_call_returns state info ready, rfl⟩, rfl⟩

theorem drop_call_returns (state : State) (info : AccountInfo.Value) (ready : dropReady state info)
  :
    AccountInfoRc.dropCall rcOps state info (.returned () (dropAfter state info)) :=
  ⟨.returned () (rcAfter false state .lamports info.lamports), ⟨ready.1, rfl⟩,
    ⟨ready.2, rfl⟩⟩

theorem drop_info_returns (state : State) (info : AccountInfo.Value) (ready : dropReady state info)
  :
    dropInfo sampleTypes info state (.returned () (dropAfter state info)) :=
  ⟨.returned () (dropAfter state info), drop_call_returns state info ready, rfl⟩

/-- Thread the actual Rc counter and trace updates through ordered entry drops. -/
def dropped : List AccountInfo.Value → State → State
  | [], state => state
  | info :: rest, state => dropped rest (dropAfter state info)

/-- Every entry drop has sufficient ownership in its actual preceding state. -/
def dropsReady : List AccountInfo.Value → State → Prop
  | [], _ => True
  | info :: rest, state => dropReady state info ∧ dropsReady rest (dropAfter state info)

/-- Vector-element and owned-argument cleanup share the same actual Rc calls. -/
theorem drop_infos_returns (infos : List AccountInfo.Value) (state : State)
    (ready : dropsReady infos state) :
    dropInfos infos state () (.returned () (dropped infos state)) := by
  induction infos generalizing state with
  | nil => rfl
  | cons info rest induction =>
    exact ⟨.returned () (dropAfter state info), drop_info_returns state info ready.1,
      induction (dropAfter state info) ready.2⟩

theorem drop_trace (infos : List AccountInfo.Value) (state : State)
    (ready : dropsReady infos state) :
    Owned.DropReturns (infos.map (dropInfo sampleTypes)) state (dropped infos state) := by
  induction infos generalizing state with
  | nil => exact .nil state
  | cons info rest induction =>
    exact .cons _ _ state (dropAfter state info) (dropped rest (dropAfter state info))
      (drop_info_returns state info ready.1) (induction (dropAfter state info) ready.2)


/-- The actual validation PDA callback changes the event state first. -/
def entryState : State :=
  pdaAfter initialState (Address.Operations.zeroFindRequest (hookPdaInputs args args.programId))

def metadataState : State := metasFocus.set entryState [some [readonlyMeta programInfo.key]]
def clonedState : State := cloneAfter metadataState programInfo
def infosState : State := infosFocus.set clonedState [some [programInfo]]
def finalState : State := dropped (List.replicate 4 AccountInfo.sampleInfo) infosState

theorem find_returns : sampleTypes.findPda initialState (hookPdaInputs args args.programId)
    (.returned (validationKey, 251) entryState) :=
  ⟨.returned (some (validationKey, 251)) entryState,
    ⟨.returned reply entryState, rfl, rfl⟩, rfl⟩

theorem entry_returns : hookEntry sampleTypes args args.programId initialState
    (.returned (.ok (validationKey, programInfo, none)) entryState) :=
  ⟨.returned (.ok (validationKey, 251)) entryState,
    ⟨.returned (validationKey, 251) entryState, find_returns, rfl⟩, rfl⟩

theorem metadata_push : sampleTypes.metas.push entryState ((0 : Nat), readonlyMeta programInfo.key)
    (.returned () metadataState) :=
  ⟨.returned () [some [readonlyMeta programInfo.key]], ⟨[], rfl, rfl⟩, rfl⟩

theorem clone_ready : cloneReady metadataState programInfo := by
  unfold cloneReady rcReady
  decide +kernel

theorem info_push : sampleTypes.infos.push clonedState ((0 : Nat), programInfo)
    (.returned () infosState) :=
  ⟨.returned () [some [programInfo]], ⟨[], rfl, rfl⟩, rfl⟩

theorem append_returns : appendReadonly sampleTypes ⟨args.instruction, args.infos⟩
    args.programId programInfo entryState (.returned (.ok ()) infosState) :=
  ⟨.returned (.ok ()) metadataState,
    ⟨.returned () metadataState, metadata_push, rfl⟩,
    .returned (.ok programInfo) clonedState, clone_info_returns metadataState programInfo
      clone_ready,
    .returned () infosState, info_push, rfl⟩

theorem arguments_ready : dropsReady (List.replicate 4 AccountInfo.sampleInfo) infosState := by
  simp only [List.replicate, dropsReady, dropReady, rcReady]
  decide +kernel

/-- The positive closed execution performs PDA, metadata append, two-field
Rc clone, info append, then all eight argument-field drops. -/
theorem run_returns : run sampleTypes initialState args (.returned (.ok ()) finalState) := by
  refine ⟨.returned (.ok (validationKey, programInfo, none)) entryState,
    ⟨.returned (.ok (validationKey, programInfo, none)) entryState, entry_returns, rfl⟩, ?_⟩
  refine ⟨.returned (.ok ()) infosState, append_returns, ?_⟩
  exact (drop_trace (List.replicate 4 AccountInfo.sampleInfo) infosState
    arguments_ready).cleanup_returned
    sampleTypes.doubleUnwind (Except.ok () : Except Error Unit)

/-- The helper preserves the preexisting instruction bytes of the caller and all
account cells. Its appended metadata is readonly, the AccountInfo retains its
alias identity, and exactly four owned arguments have been retired. -/
theorem final_observations :
    finalState.1 = initialState.1 ∧
    finalState.2.bytes = [some [42, 43]] ∧
    finalState.2.metas = [some [readonlyMeta programInfo.key]] ∧
    finalState.2.infos = [some [programInfo]] ∧
    finalState.2.rcOwners = [3, 3] ∧
    finalState.2.rcEvents =
      [.clone .lamports ⟨0⟩, .clone .data ⟨1⟩] ++
        (List.replicate 4 [.drop .lamports ⟨0⟩, .drop .data ⟨1⟩]).flatten ∧
    finalState.2.pdaCalls = [((hookPdaInputs args args.programId).seeds, args.programId)] := by
  decide +kernel

theorem has_execution : FamilyHasExecution family reference sampleTypes :=
  ⟨initialState, args, .returned (.ok ()) finalState, trivial, run_returns⟩

theorem satisfiable : FamilySatisfiable family sampleTypes := has_execution.satisfiable

end Solanalib.Specs.Core.TransferHookResolution.Sample
