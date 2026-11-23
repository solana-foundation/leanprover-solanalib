/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.LegacyStakeInstructionOwned
public import Solanalib.Specs.Core.InstructionBuilderSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.LegacyStakeInstruction.Sample

namespace Ledger
abbrev State := InstructionBuilder.Sample.State
abbrev providers := InstructionBuilder.Sample.providers Solanalib.Runtime.Bytes id
abbrev Instruction := _root_.Solanalib.Specs.Core.Instruction.OwnedValue Nat Nat

/-- A closed successful outer-vector interpretation. Its resource is the
owned ordered sequence; inner vector resources retain fresh ledger identities.
The generic construction engine also admits real allocation failures. -/
def array : Owned.Array.Provider State Instruction (List Instruction) Nat Nat where
  work := Callback.ofFunction fun before (count, values) =>
    .returned (if values.length < count then .evaluate else .finish) before
  finish := Callback.ofFunction fun before values => .returned values before
  cleanupOrder := fun _ values => List.finRange values.length
  drop := fun before value => Owned.cleanup providers.doubleUnwind
    [providers.metaVec.dropAction value.metas, providers.byteVec.dropAction value.data]
    (.returned () before)
  retire := Callback.ofFunction fun before _ => .returned () before
  double := providers.doubleUnwind

end Ledger

def index : Index where
  State := Ledger.State
  MetaResource := Nat
  ByteResource := Nat
  VectorResource := List Ledger.Instruction
  Error := Nat
  Unwind := Nat
  Terminal := Nat
  providers := Ledger.providers
  array := Ledger.array

def before : Ledger.State := {}

def allocated (state : Ledger.State) (plan : Plan) : Ledger.State :=
  InstructionBuilder.Sample.allocateMetas state plan.initial

def after (state : Ledger.State) (plan : Plan) : Ledger.State :=
  InstructionBuilder.Sample.afterSerialize id .bincode (allocated state plan) plan.data

def value (state : Ledger.State) (plan : Plan) : OwnedInstruction index :=
  ⟨plan.programId, state.metas.length, state.bytes.length⟩

theorem prepare_no_extra (state : Ledger.State) (plan : Plan) (empty : plan.extra = []) :
    prepareMetas index plan state () (.returned state.metas.length (allocated state plan)) := by
  refine ⟨.returned state.metas.length (allocated state plan), rfl, ?_⟩
  refine ⟨.returned () (allocated state plan), ?_, rfl⟩
  refine ⟨.returned () (allocated state plan), ?_, rfl⟩
  simp only [empty, pushMetas]

theorem build_no_extra (state : Ledger.State) (plan : Plan) (empty : plan.extra = []) :
    build index plan state () (.returned (value state plan) (after state plan)) := by
  refine ⟨.returned state.metas.length (allocated state plan), prepare_no_extra state plan empty,
    ?_⟩
  exact InstructionBuilder.run_of_serialized _ _ _ _ _ _ rfl

theorem single_execution (Args : Type) (plan : Args → Plan) (args : Args)
    (empty : (plan args).extra = []) :
    FamilyHasExecution (singleFamily Args plan) (singleReference Args plan) index :=
  ⟨before, args, .returned (value before (plan args)) (after before (plan args)), trivial,
    build_no_extra before (plan args) empty⟩

/-- Closed finite execution of all three independently allocated instructions. -/
theorem split_execution (args : SplitArgs) :
    FamilyHasExecution splitFamily splitReference index := by
  let p0 : Plan := ⟨.zero, StakeState.u32Bytes 8 ++ StakeState.u64Bytes 200,
    [Instruction.accountMeta args.destination true true], []⟩
  let p1 : Plan := ⟨.zero, StakeState.u32Bytes 1 ++ Solanalib.Runtime.Ids.stakeProgram.bytes,
    [Instruction.accountMeta args.destination true true], []⟩
  let p2 := splitPlan args
  let s1 := after before p0
  let s2 := after s1 p1
  let s3 := after s2 p2
  let i0 := value before p0
  let i1 := value s1 p1
  let i2 := value s2 p2
  refine ⟨before, args, .returned [i0, i1, i2] s3, trivial, ?_⟩
  refine ⟨.returned [i0, i1, i2] s3, ?_, rfl⟩
  apply Owned.Array.Trace.next [] before before s1 i0 _ (by simp) rfl
  · exact ⟨p0, rfl, build_no_extra before p0 rfl⟩
  · apply Owned.Array.Trace.next [i0] s1 s1 s2 i1 _ (by simp) rfl
    · exact ⟨p1, rfl, build_no_extra s1 p1 rfl⟩
    · apply Owned.Array.Trace.next [i0, i1] s2 s2 s3 i2 _ (by simp) rfl
      · exact ⟨p2, rfl, build_no_extra s2 p2 rfl⟩
      · exact Owned.Array.Trace.finishReturn [i0, i1, i2] s3 s3 s3 [i0, i1, i2]
          rfl rfl rfl

/-- the outer construction of Merge starts after the metadata vector exists. -/
theorem merge_execution (args : MergeArgs) :
    FamilyHasExecution mergeFamily mergeReference index := by
  let plan := mergePlan args
  let ready := allocated before plan
  let complete := after before plan
  let instruction := value before plan
  refine ⟨before, args, .returned [instruction] complete, trivial, ?_⟩
  refine ⟨.returned (0 : Nat) ready, rfl, ?_⟩
  refine ⟨.returned [instruction] complete, ?_, rfl⟩
  apply Owned.Array.Trace.next [] ready ready complete instruction _ (by simp) rfl
  · exact InstructionBuilder.run_of_serialized _ _ _ _ _ _ rfl
  · exact Owned.Array.Trace.finishReturn [instruction] complete complete complete [instruction]
      rfl rfl rfl

end Solanalib.Specs.Core.LegacyStakeInstruction.Sample
