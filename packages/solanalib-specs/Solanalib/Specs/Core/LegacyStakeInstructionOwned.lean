/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.LegacyStakeInstruction
public import Solanalib.Specs.Core.InstructionBuilder
public import Solanalib.Specs.Core.OwnedArray
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.LegacyStakeInstruction

/-- All concrete source resource and failure representations remain indexed.
The serializer receives the exact fixed bincode bytes of these concrete
variants. Binding it to the fixed codec and allocation of bincode is explicit. -/
structure Index where
  State : Type
  MetaResource : Type
  ByteResource : Type
  VectorResource : Type
  Error : Type
  Unwind : Type
  Terminal : Type
  providers : InstructionBuilder.Providers
    ⟨State, Solanalib.Runtime.Bytes, MetaResource, ByteResource, Error, Unwind, Terminal⟩
  array : Owned.Array.Provider State (Instruction.OwnedValue MetaResource ByteResource)
    VectorResource Unwind Terminal

def Index.builderTypes (index : Index) : InstructionBuilder.Types :=
  ⟨index.State, Solanalib.Runtime.Bytes, index.MetaResource, index.ByteResource,
    index.Error, index.Unwind, index.Terminal⟩

abbrev OwnedInstruction (index : Index) :=
  Instruction.OwnedValue index.MetaResource index.ByteResource

/-- Optional account pushes occur after literal-vector construction. The allocation and unwinding
state of a push are supplied by the actual dependency. -/
def pushMetas (index : Index) (resource : index.MetaResource) : List Instruction.Meta →
    Callback.Run index.State Unit Unit index.Unwind index.Terminal
  | [] => fun before _ outcome => outcome = .returned () before
  | value :: rest => fun before _ =>
    Callback.bind index.providers.metaVec.push (fun _ after =>
      pushMetas index resource rest after ()) before (resource, value)

def prepareMetas (index : Index) (plan : Plan) :
    Callback.Run index.State Unit index.MetaResource index.Unwind index.Terminal :=
  fun before _ => Callback.bind index.providers.metaVec.fromList
    (fun resource after =>
      Callback.map (fun _ => resource)
        (Owned.protect index.providers.doubleUnwind
          [index.providers.metaVec.dropAction resource]
          (pushMetas index resource plan.extra)) after ())
    before plan.initial

/-- Once metadata preparation returns, the standard builder owns that same
handle and drops it on a serialization/unwrap unwind. The push scope has
already ended, so no metadata handle is dropped twice. -/
def build (index : Index) (plan : Plan) :
    Callback.Run index.State Unit (OwnedInstruction index) index.Unwind index.Terminal :=
  Callback.bind (prepareMetas index plan) fun resource after =>
    InstructionBuilder.run index.builderTypes .bincode after
      ⟨plan.programId, plan.data, resource, index.providers⟩

def singleFamily (Args : Type) (plan : Args → Plan) : Family where
  Index := Index
  State := Index.State
  Args := fun _ => Args
  Value := OwnedInstruction
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before args => build index (plan args) before () }

def singleReference (Args : Type) (plan : Args → Plan) : FamilyRun (singleFamily Args plan) :=
  fun index before args => build index (plan args) before ()

theorem single_reference (Args : Type) (plan : Args → Plan) :
    FamilyReference (singleFamily Args plan) (singleReference Args plan) :=
  fun _ _ _ _ _ execution => execution

/-- The source vec macro supplies array allocation/scheduling and cleanup. Its
expressions construct the three instructions in left-to-right order. -/
def splitRun (index : Index) (before : index.State) (args : SplitArgs) :
    Outcome index.State index.VectorResource index.Unwind index.Terminal → Prop :=
  index.array.run 3 (fun state position outcome =>
    ∃ plan, (splitPlans args)[position]? = some plan ∧ build index plan state () outcome) before

/-- Merge allocates the accounts Vec before entering the one-element outer
Vec expression. If outer construction unwinds before evaluating that element,
the still-unconsumed accounts Vec is dropped after temporary storage cleanup.
An element unwind has already consumed/cleaned it inside InstructionBuilder. -/
def mergeWithMetas (index : Index) (args : MergeArgs) (resource : index.MetaResource)
    (before : index.State)
    (outcome : Outcome index.State index.VectorResource index.Unwind index.Terminal) : Prop :=
  ∃ detailed, index.array.runDetailed 1
    (fun state _ => InstructionBuilder.run index.builderTypes .bincode state
      ⟨(mergePlan args).programId, (mergePlan args).data, resource, index.providers⟩)
      before detailed ∧
    match detailed with
    | .returned value after => outcome = .returned value after
    | .terminated reason => outcome = .terminated reason
    | .unwound (failure, reason) after =>
      if failure.completed = 0 ∧ failure.site = .work then
        Owned.cleanup index.providers.doubleUnwind
          [index.providers.metaVec.dropAction resource] (.unwound reason after) outcome
      else outcome = .unwound reason after

def mergeRun (index : Index) (before : index.State) (args : MergeArgs) :
    Outcome index.State index.VectorResource index.Unwind index.Terminal → Prop :=
  Callback.bind index.providers.metaVec.fromList (fun resource after =>
    mergeWithMetas index args resource after) before (mergePlan args).initial

def splitFamily : Family where
  Index := Index
  State := Index.State
  Args := fun _ => SplitArgs
  Value := Index.VectorResource
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => { requires := fun _ _ => True, post := splitRun index }

def mergeFamily : Family where
  Index := Index
  State := Index.State
  Args := fun _ => MergeArgs
  Value := Index.VectorResource
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => { requires := fun _ _ => True, post := mergeRun index }

def splitReference : FamilyRun splitFamily := splitRun
def mergeReference : FamilyRun mergeFamily := mergeRun

theorem split_reference : FamilyReference splitFamily splitReference :=
  fun _ _ _ _ _ execution => execution

theorem merge_reference : FamilyReference mergeFamily mergeReference :=
  fun _ _ _ _ _ execution => execution

/-- Useful source-call observation from the actual retained resources. -/
def observe (index : Index) (state : index.State) (value : OwnedInstruction index) :
    Option Instruction.Value :=
  InstructionBuilder.observe index.builderTypes index.providers state value

/-- Local primitive codec and vector facts expose all bytes, flags and account
order of the prepared instruction. No CPI effect is inferred from construction. -/
theorem observe_plan (index : Index) (state : index.State) (value : OwnedInstruction index)
    (plan : Plan) (program : value.programId = plan.programId)
    (metas : index.providers.metaVec.current state value.metas = some (plan.initial ++ plan.extra))
    (bytes : index.providers.byteVec.current state value.data = some plan.data) :
    observe index state value = some plan.value := by
  unfold observe
  rw [InstructionBuilder.observe_of_current index.builderTypes index.providers state value
    (plan.initial ++ plan.extra) plan.data metas bytes]
  simp [Plan.value, program]

end Solanalib.Specs.Core.LegacyStakeInstruction
