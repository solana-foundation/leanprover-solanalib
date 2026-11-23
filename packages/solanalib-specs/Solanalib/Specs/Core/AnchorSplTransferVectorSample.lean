/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTransferResources
public import Solanalib.Specs.Core.TokenInstructionAllocatedWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTransfer.VectorSample

open Token.InstructionAllocated

/-- Reuse the shared two-vector reference ledger while retaining independent
SDK state. No vector implementation or allocator-success assertion is added. -/
def types (Aux : Type) : Types where
  State := Witness.State × Aux
  ByteResource := Nat
  MetaResource := Nat
  Unwind := Nat
  Terminal := Nat
  wordBits := Witness.sampleTypes.wordBits
  enumSize := Witness.sampleTypes.enumSize
  bytes := Witness.sampleTypes.bytes.focus Owned.Focus.fst
  metas := Witness.sampleTypes.metas.focus Owned.Focus.fst
  doubleUnwind := fun _ first second terminal => terminal = first + second

variable {Aux : Type}

theorem bytes_capacity (bytes : Owned.VectorState UInt8)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (aux : Aux) (capacity : Nat) :
    (types Aux).bytes.withCapacity ((bytes, metas), aux) capacity
      (.returned bytes.length ((bytes ++ [some []], metas), aux)) :=
  ⟨.returned bytes.length (bytes ++ [some []], metas), Witness.bytes_capacity _ _ _, rfl⟩

theorem bytes_push (bytes : Solanalib.Runtime.Bytes) (metas : Owned.VectorState
  Solanalib.Runtime.CpiMeta)
    (aux : Aux) (value : UInt8) :
    (types Aux).bytes.push (([some bytes], metas), aux) ((0 : Nat), value)
      (.returned () (([some (bytes ++ [value])], metas), aux)) :=
  ⟨.returned () ([some (bytes ++ [value])], metas), Witness.bytes_push _ _ _, rfl⟩

theorem bytes_extend (bytes extra : Solanalib.Runtime.Bytes) (metas : Owned.VectorState
  Solanalib.Runtime.CpiMeta)
    (aux : Aux) :
    (types Aux).bytes.extend (([some bytes], metas), aux) ((0 : Nat), extra)
      (.returned () (([some (bytes ++ extra)], metas), aux)) :=
  ⟨.returned () ([some (bytes ++ extra)], metas), Witness.bytes_extend _ _ _, rfl⟩

theorem metas_capacity (bytes : Owned.VectorState UInt8)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (aux : Aux) (capacity : Nat) :
    (types Aux).metas.withCapacity ((bytes, metas), aux) capacity
      (.returned metas.length ((bytes, metas ++ [some []]), aux)) :=
  ⟨.returned metas.length (bytes, metas ++ [some []]), Witness.metas_capacity _ _ _, rfl⟩

theorem metas_from_list (bytes : Owned.VectorState UInt8)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (aux : Aux) (items : List
      Solanalib.Runtime.CpiMeta) :
    (types Aux).metas.fromList ((bytes, metas), aux) items
      (.returned metas.length ((bytes, metas ++ [some items]), aux)) :=
  ⟨.returned metas.length (bytes, metas ++ [some items]), Witness.metas_from_list _ _ _, rfl⟩

theorem metas_push (bytes : Owned.VectorState UInt8) (items : List Solanalib.Runtime.CpiMeta)
    (aux : Aux) (item : Solanalib.Runtime.CpiMeta) :
    (types Aux).metas.push ((bytes, [some items]), aux) ((0 : Nat), item)
      (.returned () ((bytes, [some (items ++ [item])]), aux)) :=
  ⟨.returned () (bytes, [some (items ++ [item])]), Witness.metas_push _ _ _, rfl⟩

/-- Each source byte operation runs through the same vector providers, with
the auxiliary world unchanged by this particular reference interpretation. -/
theorem write_data_returns (steps : List DataStep) (prior : Solanalib.Runtime.Bytes)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (aux : Aux) :
    writeData (types Aux) (0 : Nat) steps (([some prior], metas), aux) ()
      (.returned () (([some (prior ++ steps.flatMap DataStep.bytes)], metas), aux)) := by
  induction steps generalizing prior with
  | nil => simp [writeData]
  | cons step steps induction =>
    cases step with
    | push byte =>
      refine ⟨.returned () (([some (prior ++ [byte])], metas), aux), bytes_push _ _ _ _, ?_⟩
      simpa [DataStep.bytes, List.append_assoc] using induction (prior ++ [byte])
    | extend extra =>
      refine ⟨.returned () (([some (prior ++ extra)], metas), aux), bytes_extend _ _ _ _, ?_⟩
      simpa [DataStep.bytes, List.append_assoc] using induction (prior ++ extra)

theorem push_metas_returns (items prior : List Solanalib.Runtime.CpiMeta)
    (bytes : Owned.VectorState UInt8) (aux : Aux) :
    pushMetas (types Aux) (0 : Nat) items ((bytes, [some prior]), aux) ()
      (.returned () ((bytes, [some (prior ++ items)]), aux)) := by
  induction items generalizing prior with
  | nil => simp [pushMetas]
  | cons item items induction =>
    refine ⟨.returned () ((bytes, [some (prior ++ [item])]), aux), metas_push _ _ _ _, ?_⟩
    simpa [List.append_assoc] using induction (prior ++ [item])

theorem build_metas_returns (plan : MetaPlan) (bytes : Owned.VectorState UInt8) (aux : Aux) :
    buildMetas (types Aux) plan ((bytes, []), aux) ()
      (.returned (0 : Nat) ((bytes, [some plan.items]), aux)) := by
  cases plan with
  | fromList items => exact metas_from_list _ [] aux items
  | withCapacity capacity items =>
    refine Witness.build_metas_reserved (metas_capacity bytes [] aux capacity)
      (push_metas_returns items [] bytes aux) ?_
    rfl
  | fromListThenPush initial rest =>
    refine Witness.build_metas_literal_tail (metas_from_list bytes [] aux initial)
      (push_metas_returns rest initial bytes aux) ?_
    rfl

/-- The reference byte builder preserves any metadata owner constructed
earlier and retains the auxiliary state throughout its individual writes. -/
theorem build_data_returns (steps : List DataStep)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (aux : Aux) :
    buildData (types Aux) steps (([], metas), aux) ()
      (.returned (0 : Nat) (([some (steps.flatMap DataStep.bytes)], metas), aux)) := by
  exact Witness.build_data_allocated (bytes_capacity [] metas aux (types Aux).enumSize)
    (write_data_returns steps [] metas aux) rfl

def value (Aux : Type) (plan : Plan) : Value (types Aux) :=
  ⟨plan.programId, (0 : Nat), (0 : Nat)⟩

/-- Any admitted plan has a concrete complete builder execution with real
ledger resources and retained auxiliary state. This proves existence only for
the selected reference interpretation, not allocator success in source Rust. -/
theorem run_returns (plan : Plan) (aux : Aux)
    (admitted : Token.Instruction.checkProgram plan.programs plan.programId = .ok ()) :
    Token.InstructionAllocated.run (types Aux) (([], []), aux) plan
      (.returned (.ok (value Aux plan)) (([some plan.data], [some plan.metas.items]), aux)) := by
  cases order : plan.order with
  | dataThenMetas =>
    exact Witness.run_from_prepared_data admitted order
      (bytes_capacity [] [] aux (types Aux).enumSize)
      (write_data_returns plan.dataSteps [] [] aux)
      (build_metas_returns plan.metas [some plan.data] aux) rfl
  | metasThenData =>
    exact Witness.run_from_prepared_metas admitted order
      (build_metas_returns plan.metas [] aux)
      (build_data_returns plan.dataSteps [some plan.metas.items] aux) rfl

private theorem returns_exact {State Args Value Unwind Terminal : Type}
    (run : State → Args → Value × State) (before : State) (args : Args)
    (outcome : Outcome State Value Unwind Terminal) :
    returnsOf run before args outcome ↔
      outcome = .returned (run before args).1 (run before args).2 := by
  cases outcome with
  | returned value after => simp [returnsOf, Prod.ext_iff, eq_comm]
  | unwound _ _ => simp [returnsOf]
  | terminated _ => simp [returnsOf]

private theorem lift_exact {Outer Inner Args Value Unwind Terminal : Type}
    (focus : Owned.Focus Outer Inner) (run : Callback.Run Inner Args Value Unwind Terminal)
    (before : Outer) (args : Args) (value : Value) (after : Inner)
    (exact : ∀ outcome, run (focus.get before) args outcome ↔ outcome = .returned value after)
    (outcome : Outcome Outer Value Unwind Terminal) :
    focus.lift run before args outcome ↔
      outcome = .returned value (focus.set before after) := by
  simp only [Owned.Focus.lift, exact]
  simp [Owned.Focus.liftOutcome, eq_comm]

private theorem bytes_capacity_exact (bytes : Owned.VectorState UInt8)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (aux : Aux) (capacity : Nat)
    (outcome : Outcome (types Aux).State (types Aux).ByteResource
      (types Aux).Unwind (types Aux).Terminal) :
    (types Aux).bytes.withCapacity ((bytes, metas), aux) capacity outcome ↔
      outcome = .returned bytes.length ((bytes ++ [some []], metas), aux) := by
  apply lift_exact Owned.Focus.fst _ _ _ _ _
  intro inner
  apply lift_exact Owned.Focus.fst _ _ _ _ _
  intro inner
  exact returns_exact _ _ _ inner

private theorem bytes_push_exact (bytes : Solanalib.Runtime.Bytes)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (aux : Aux) (value : UInt8)
    (outcome : Outcome (types Aux).State Unit (types Aux).Unwind (types Aux).Terminal) :
    (types Aux).bytes.push (([some bytes], metas), aux) ((0 : Nat), value) outcome ↔
      outcome = .returned () (([some (bytes ++ [value])], metas), aux) := by
  apply lift_exact Owned.Focus.fst _ _ _ _ _
  intro inner
  apply lift_exact Owned.Focus.fst _ _ _ _ _
  intro inner
  change (∃ actual, some bytes = some actual ∧
    inner = .returned () [some (actual ++ [value])]) ↔ _
  simp

private theorem bytes_extend_exact (bytes extra : Solanalib.Runtime.Bytes)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (aux : Aux)
    (outcome : Outcome (types Aux).State Unit (types Aux).Unwind (types Aux).Terminal) :
    (types Aux).bytes.extend (([some bytes], metas), aux) ((0 : Nat), extra) outcome ↔
      outcome = .returned () (([some (bytes ++ extra)], metas), aux) := by
  apply lift_exact Owned.Focus.fst _ _ _ _ _
  intro inner
  apply lift_exact Owned.Focus.fst _ _ _ _ _
  intro inner
  change (∃ actual, some bytes = some actual ∧
    inner = .returned () [some (actual ++ extra)]) ↔ _
  simp

private theorem metas_capacity_exact (bytes : Owned.VectorState UInt8)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (aux : Aux) (capacity : Nat)
    (outcome : Outcome (types Aux).State (types Aux).MetaResource
      (types Aux).Unwind (types Aux).Terminal) :
    (types Aux).metas.withCapacity ((bytes, metas), aux) capacity outcome ↔
      outcome = .returned metas.length ((bytes, metas ++ [some []]), aux) := by
  apply lift_exact Owned.Focus.fst _ _ _ _ _
  intro inner
  apply lift_exact Owned.Focus.snd _ _ _ _ _
  intro inner
  exact returns_exact _ _ _ inner

private theorem metas_push_exact (bytes : Owned.VectorState UInt8)
    (items : List Solanalib.Runtime.CpiMeta) (aux : Aux) (item : Solanalib.Runtime.CpiMeta)
    (outcome : Outcome (types Aux).State Unit (types Aux).Unwind (types Aux).Terminal) :
    (types Aux).metas.push ((bytes, [some items]), aux) ((0 : Nat), item) outcome ↔
      outcome = .returned () ((bytes, [some (items ++ [item])]), aux) := by
  apply lift_exact Owned.Focus.fst _ _ _ _ _
  intro inner
  apply lift_exact Owned.Focus.snd _ _ _ _ _
  intro inner
  change (∃ actual, some items = some actual ∧
    inner = .returned () [some (actual ++ [item])]) ↔ _
  simp

/-- Every successful reference execution of the actual two writes of the transfer
and three metadata pushes leaves both returned vectors readable. This derives
admission from the concrete dependency trace, not from one chosen execution. -/
theorem transfer_readable (aux : Aux) (encoded : Solanalib.Runtime.Bytes)
    (source destination authority : Solanalib.Runtime.CpiMeta)
    (instruction : Value (types Aux)) (after : (types Aux).State)
    (built : Token.InstructionAllocated.run (types Aux) (([], []), aux)
      { programs := .legacy, programId := Token.legacyProgramId,
        dataSteps := [.push 3, .extend encoded],
        metas := .withCapacity 3 [source, destination, authority] }
      (.returned (.ok instruction) after)) :
    (types Aux).metas.Live after instruction.metas ∧
      (types Aux).bytes.Live after instruction.data := by
  have result : instruction = ⟨Token.legacyProgramId, (0 : Nat), (0 : Nat)⟩ ∧
      after = (([some ([3] ++ encoded)], [some [source, destination, authority]]), aux) := by
    simpa [Token.InstructionAllocated.run, Token.Instruction.checkProgram,
      Token.Instruction.ProgramSet.accepts, Callback.bind, Callback.map,
      Owned.protect, Owned.onUnwind, writeData, buildMetas, pushMetas,
      bytes_capacity_exact, bytes_push_exact, bytes_extend_exact,
      metas_capacity_exact, metas_push_exact, Outcome.map] using built
  obtain ⟨rfl, rfl⟩ := result
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

theorem vector_drop_no_unwind {Element Unwind Terminal : Type}
    (before after : Owned.VectorState Element) (resource : Nat) (reason : Unwind) :
    ¬ (Owned.vectorReference : Owned.VectorOps (Owned.VectorState Element) Element Nat Unwind
      Terminal).drop
      before resource (.unwound reason after) := by
  rintro ⟨values, _, impossible⟩
  cases impossible

/-- The non-unwind primitive capability survives lawful state focusing. -/
theorem focused_drop_no_unwind {Outer Inner Element Resource Unwind Terminal : Type}
    (ops : Owned.VectorOps Inner Element Resource Unwind Terminal)
    (focus : Owned.Focus Outer Inner)
    (noUnwind : ∀ before resource reason after, ¬ ops.drop before resource (.unwound reason after))
    (before after : Outer) (resource : Resource) (reason : Unwind) :
    ¬ (ops.focus focus).drop before resource (.unwound reason after) := by
  intro run
  obtain ⟨inner, called, _⟩ :=
    (Owned.Focus.lift_unwound_iff focus ops.drop before resource reason after).mp run
  exact noUnwind _ _ _ _ called

theorem bytes_no_unwind (before after : (types Aux).State) (resource reason : Nat) :
    ¬ (types Aux).bytes.drop before resource (.unwound reason after) := by
  apply focused_drop_no_unwind _ _ _ before after resource reason
  intro before resource reason after
  exact focused_drop_no_unwind _ _
    (fun before resource reason after => vector_drop_no_unwind before after resource reason)
    before after resource reason

theorem metas_no_unwind (before after : (types Aux).State) (resource reason : Nat) :
    ¬ (types Aux).metas.drop before resource (.unwound reason after) := by
  apply focused_drop_no_unwind _ _ _ before after resource reason
  intro before resource reason after
  exact focused_drop_no_unwind _ _
    (fun before resource reason after => vector_drop_no_unwind before after resource reason)
    before after resource reason

end Solanalib.Specs.Core.AnchorSplTransfer.VectorSample
