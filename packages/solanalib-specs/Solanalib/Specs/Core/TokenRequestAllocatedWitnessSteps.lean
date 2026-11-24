/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessProviders
public import Solanalib.Specs.Core.TokenRequestAllocatedOnchain
public import Solanalib.Specs.Core.TokenInstructionAllocatedWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.Witness

/-- The single live byte slot of the sample with all surrounding state retained. -/
def putBytes (state : State) (bytes : Bytes) : State := bytesFocus.set state [some bytes]
/-- The single live metadata slot of the sample with all surrounding state retained. -/
def putMetas (state : State) (items : List Solanalib.Runtime.CpiMeta) : State :=
  metasFocus.set state [some items]

theorem bytes_capacity (state : State) (capacity : Nat) :
    sampleTypes.bytes.withCapacity state capacity
      (.returned state.2.bytes.length
        (bytesFocus.set state (state.2.bytes ++ [some []]))) :=
  ⟨.returned state.2.bytes.length (state.2.bytes ++ [some []]), rfl, rfl⟩

theorem bytes_push (state : State) (prior : Bytes) (byte : UInt8) :
    sampleTypes.bytes.push (putBytes state prior) ((0 : Nat), byte)
      (.returned () (putBytes state (prior ++ [byte]))) :=
  ⟨.returned () [some (prior ++ [byte])], ⟨prior, rfl, rfl⟩, rfl⟩

theorem bytes_extend (state : State) (prior extra : Bytes) :
    sampleTypes.bytes.extend (putBytes state prior) ((0 : Nat), extra)
      (.returned () (putBytes state (prior ++ extra))) :=
  ⟨.returned () [some (prior ++ extra)], ⟨prior, rfl, rfl⟩, rfl⟩

theorem metas_capacity (state : State) (capacity : Nat) :
    sampleTypes.metas.withCapacity state capacity
      (.returned state.2.metas.length
        (metasFocus.set state (state.2.metas ++ [some []]))) :=
  ⟨.returned state.2.metas.length (state.2.metas ++ [some []]), rfl, rfl⟩

theorem metas_from_list (state : State) (items : List Solanalib.Runtime.CpiMeta) :
    sampleTypes.metas.fromList state items
      (.returned state.2.metas.length
        (metasFocus.set state (state.2.metas ++ [some items]))) :=
  ⟨.returned state.2.metas.length (state.2.metas ++ [some items]), rfl, rfl⟩

theorem metas_push (state : State) (prior : List Solanalib.Runtime.CpiMeta) (item :
  Solanalib.Runtime.CpiMeta) :
    sampleTypes.metas.push (putMetas state prior) ((0 : Nat), item)
      (.returned () (putMetas state (prior ++ [item]))) :=
  ⟨.returned () [some (prior ++ [item])], ⟨prior, rfl, rfl⟩, rfl⟩

/-- The same standalone constructor engine composes every byte operation in
the larger account, vector and Rc world, preserving the surrounding state. -/
theorem write_data_returns (steps : List InstructionAllocated.DataStep) (prior : Bytes)
    (state : State) :
    InstructionAllocated.writeData sampleTypes.constructor (0 : Nat) steps
      (putBytes state prior) ()
      (.returned () (putBytes state (prior ++ steps.flatMap InstructionAllocated.DataStep.bytes)))
        := by
  induction steps generalizing prior with
  | nil => simp [InstructionAllocated.writeData]
  | cons step steps induction =>
    cases step with
    | push byte =>
      refine ⟨.returned () (putBytes state (prior ++ [byte])), bytes_push _ _ _, ?_⟩
      simpa [InstructionAllocated.DataStep.bytes, List.append_assoc] using
        induction (prior ++ [byte])
    | extend extra =>
      refine ⟨.returned () (putBytes state (prior ++ extra)), bytes_extend _ _ _, ?_⟩
      simpa [InstructionAllocated.DataStep.bytes, List.append_assoc] using
        induction (prior ++ extra)

theorem push_metas_returns (items prior : List Solanalib.Runtime.CpiMeta) (state : State) :
    InstructionAllocated.pushMetas sampleTypes.constructor (0 : Nat) items
      (putMetas state prior) () (.returned () (putMetas state (prior ++ items))) := by
  induction items generalizing prior with
  | nil => simp [InstructionAllocated.pushMetas]
  | cons item items induction =>
    refine ⟨.returned () (putMetas state (prior ++ [item])), metas_push _ _ _, ?_⟩
    simpa [List.append_assoc] using induction (prior ++ [item])

theorem build_metas_returns (plan : InstructionAllocated.MetaPlan) (state : State)
    (empty : state.2.metas = []) :
    InstructionAllocated.buildMetas sampleTypes.constructor plan state ()
      (.returned (0 : Nat) (putMetas state plan.items)) := by
  cases plan with
  | fromList items =>
    simpa only [InstructionAllocated.buildMetas, Types.constructor,
      InstructionAllocated.MetaPlan.items, putMetas, empty, List.length_nil, List.nil_append] using
      metas_from_list state items
  | withCapacity capacity items =>
    have allocated : sampleTypes.metas.withCapacity state capacity
        (.returned (0 : Nat) (putMetas state [])) := by
      simpa only [putMetas, empty, List.length_nil, List.nil_append] using metas_capacity state
        capacity
    refine InstructionAllocated.Witness.build_metas_reserved allocated
      (push_metas_returns items [] state) ?_
    rfl
  | fromListThenPush initial rest =>
    have allocated : sampleTypes.metas.fromList state initial
        (.returned (0 : Nat) (putMetas state initial)) := by
      simpa only [putMetas, empty, List.length_nil, List.nil_append] using
        metas_from_list state initial
    exact InstructionAllocated.Witness.build_metas_literal_tail allocated
      (push_metas_returns rest initial state) rfl

/-- The constructed instruction owns slot zero in each distinct typed ledger. -/
def ownedInstruction (plan : InstructionAllocated.Plan) :
    Instruction.OwnedValue Nat Nat := ⟨plan.programId, 0, 0⟩

/-- The state reached by executing this plan from empty byte and meta ledgers. -/
def constructed (state : State) (plan : InstructionAllocated.Plan) : State :=
  putMetas (putBytes state plan.data) plan.metas.items

/-- Successful instruction construction is derived on the full caller state;
no whole-constructor callback is supplied to the on-chain model. -/
theorem constructor_returns (state : State) (plan : InstructionAllocated.Plan)
    (emptyBytes : state.2.bytes = []) (emptyMetas : state.2.metas = [])
    (admitted : Instruction.checkProgram plan.programs plan.programId = .ok ()) :
    InstructionAllocated.run sampleTypes.constructor state plan
      (.returned (.ok (ownedInstruction plan)) (constructed state plan)) := by
  cases order : plan.order with
  | dataThenMetas =>
    have allocated : sampleTypes.bytes.withCapacity state sampleTypes.tokenEnumSize
        (.returned (0 : Nat) (putBytes state [])) := by
      simpa only [putBytes, emptyBytes, List.length_nil, List.nil_append] using
        bytes_capacity state sampleTypes.tokenEnumSize
    refine InstructionAllocated.Witness.run_from_prepared_data
      (metadata := .returned (0 : Nat) (constructed state plan)) admitted order allocated
      (write_data_returns plan.dataSteps [] state) ?_ ?_
    · exact build_metas_returns plan.metas (putBytes state plan.data) emptyMetas
    · rfl
  | metasThenData =>
    have allocated : sampleTypes.bytes.withCapacity (putMetas state plan.metas.items)
        sampleTypes.tokenEnumSize
        (.returned (0 : Nat) (putBytes (putMetas state plan.metas.items) [])) := by
      simpa only [putBytes, putMetas, metasFocus, emptyBytes, List.length_nil, List.nil_append]
        using
        bytes_capacity (putMetas state plan.metas.items) sampleTypes.tokenEnumSize
    refine InstructionAllocated.Witness.run_from_prepared_metas
      (data := .returned (0 : Nat) (constructed state plan)) admitted order
      (build_metas_returns plan.metas state emptyMetas) ?_ ?_
    · exact InstructionAllocated.Witness.build_data_allocated allocated
        (write_data_returns plan.dataSteps [] (putMetas state plan.metas.items)) rfl
    · rfl

/-- A whole AccountInfo clone updates lamports Rc before data Rc. -/
def cloneAfter (state : State) (info : AccountInfo.Value) : State :=
  rcAfter true (rcAfter true state .lamports info.lamports) .data info.data

/-- A whole AccountInfo drop updates lamports Rc before data Rc. -/
def dropAfter (state : State) (info : AccountInfo.Value) : State :=
  rcAfter false (rcAfter false state .lamports info.lamports) .data info.data

/-- Both ordered clone calls lie inside the domain of the finite sample provider. -/
def cloneReady (state : State) (info : AccountInfo.Value) : Prop :=
  rcReady true state .lamports info.lamports ∧
    rcReady true (rcAfter true state .lamports info.lamports) .data info.data

/-- Both ordered field drops have a represented live owner to consume. -/
def dropReady (state : State) (info : AccountInfo.Value) : Prop :=
  rcReady false state .lamports info.lamports ∧
    rcReady false (rcAfter false state .lamports info.lamports) .data info.data

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

/-- Concatenate two actual destructor traces without changing their order or
the intermediate state at which the second trace starts. -/
theorem drop_trace_append
    {first rest : List (Owned.DropAction State Nat Nat)} {before middle after : State}
    (head : Owned.DropReturns first before middle)
    (tail : Owned.DropReturns rest middle after) :
    Owned.DropReturns (first ++ rest) before after := by
  induction head with
  | nil => exact tail
  | cons action actions before during middle called _ induction =>
    exact .cons action (actions ++ rest) before during after called (induction tail)

/-- The selected checked-transfer instruction before on-chain account handling. -/
def plan : InstructionAllocated.Plan := transferPlan Onchain.witnessArgs
/-- Both instruction vectors are live before any AccountInfo clone. -/
def instructionState : State := constructed initialState plan
/-- State after cloning the source AccountInfo. -/
def clone1 : State := cloneAfter instructionState Onchain.witnessInfo
/-- State after cloning the mint AccountInfo. -/
def clone2 : State := cloneAfter clone1 Onchain.witnessInfo
/-- State after cloning the destination AccountInfo. -/
def clone3 : State := cloneAfter clone2 Onchain.witnessInfo
/-- State after cloning the authority AccountInfo. -/
def clone4 : State := cloneAfter clone3 Onchain.witnessInfo
/-- The sample intentionally retains four aliases as four owned vector entries. -/
def accounts : List AccountInfo.Value := List.replicate 4 Onchain.witnessInfo
/-- The literal vector owns those four already-cloned entries in slot zero. -/
def infosState : State := infosFocus.set clone4 [some accounts]

/-- Preparation retains both instruction vector handles and the info-vector handle. -/
def prepared : Prepared sampleTypes := ⟨ownedInstruction plan, (0 : Nat)⟩

/-- The sample schedule evaluates all four indexed clones in their actual
states before the supplied completion trace. Other family members can perform
construction work, unwind or terminate between those indexed evaluations. -/
theorem literal_four_steps
    (provider : Owned.Array.Provider State AccountInfo.Value Nat Nat Nat)
    (work : provider.work = infoLiteral.work)
    (outcome : Outcome State Nat (Owned.Array.Failure × Nat) Nat)
    (finished : Owned.Array.Trace provider 4 (initialInfoAt sampleTypes Onchain.witnessArgs)
      accounts clone4 outcome) :
    provider.runDetailed 4 (initialInfoAt sampleTypes Onchain.witnessArgs)
      instructionState outcome := by
  refine .next [] instructionState instructionState clone1 Onchain.witnessInfo outcome
    (by decide) ?_ ?_ ?_
  · rw [work]
    rfl
  · exact clone_lift_returns _ _ (by unfold cloneReady rcReady; decide +kernel)
  refine .next _ clone1 clone1 clone2 Onchain.witnessInfo outcome (by decide) ?_ ?_ ?_
  · rw [work]
    rfl
  · exact clone_lift_returns _ _ (by unfold cloneReady rcReady; decide +kernel)
  refine .next _ clone2 clone2 clone3 Onchain.witnessInfo outcome (by decide) ?_ ?_ ?_
  · rw [work]
    rfl
  · exact clone_lift_returns _ _ (by unfold cloneReady rcReady; decide +kernel)
  refine .next _ clone3 clone3 clone4 Onchain.witnessInfo outcome (by decide) ?_ ?_ ?_
  · rw [work]
    rfl
  · exact clone_lift_returns _ _ (by unfold cloneReady rcReady; decide +kernel)
  exact finished

/-- This explicit sample schedule evaluates four clones and transfers all
four owned results at completion; it assumes no fixed source allocation order. -/
theorem initial_infos_returns :
    initialInfos sampleTypes Onchain.witnessArgs instructionState
      (.returned (.ok (0 : Nat)) infosState) := by
  refine ⟨.returned (0 : Nat) infosState, ?_, rfl⟩
  refine ⟨.returned (0 : Nat) infosState, ?_, rfl⟩
  apply literal_four_steps sampleTypes.literalProvider rfl
  exact .finishReturn accounts clone4 clone4 infosState (0 : Nat) rfl ⟨rfl, rfl⟩
    ⟨.returned (0 : Nat) [some accounts], rfl, rfl⟩

/-- The current owner is not a token program, so multisig detection skips its
data-length borrow and preserves the complete constructed state. -/
theorem no_multisig_returns :
    addMultisig sampleTypes Onchain.witnessArgs prepared infosState
      (.returned (.ok ()) infosState) :=
  ⟨.returned (.ok false) infosState, rfl, rfl⟩

/-- This is an actual allocation, pack, clone, info construction and multisig
control-flow execution, retaining all owners for the mint stage. -/
theorem base_returns :
    base sampleTypes Onchain.witnessArgs initialState
      (.returned (.ok prepared) infosState) := by
  refine ⟨.returned (.ok (ownedInstruction plan)) instructionState,
    constructor_returns initialState plan rfl rfl (by rfl), ?_⟩
  refine ⟨.returned (.ok prepared) infosState, ?_, rfl⟩
  refine ⟨.returned (.ok (0 : Nat)) infosState, initial_infos_returns, ?_⟩
  exact ⟨.returned (.ok prepared) infosState,
    ⟨.returned (.ok ()) infosState, no_multisig_returns, rfl⟩, rfl⟩

end Solanalib.Specs.Core.Token.OnchainAllocated.Witness
