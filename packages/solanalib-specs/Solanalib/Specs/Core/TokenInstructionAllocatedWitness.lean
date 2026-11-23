/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionAllocated
public import Solanalib.Specs.Core.OwnedVector
public import Solanalib.Specs.Core.OwnedFocus
public import Solanalib.Specs.Core.OwnedFocusFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.InstructionAllocated.Witness

/-- Assemble an actual constructor execution after its byte-vector allocation
and writes. The metadata outcome and subsequent cleanup retain their actual
states, so this rule also exposes allocation, unwind and terminal controls. -/
theorem run_from_prepared_data {types : Types} {before : types.State} {plan : Plan}
    {data : types.ByteResource} {allocated written : types.State}
    {metadata : Outcome types.State types.MetaResource types.Unwind types.Terminal}
    {final : Outcome types.State (Except Error (Value types)) types.Unwind types.Terminal}
    (admitted : Instruction.checkProgram plan.programs plan.programId = .ok ())
    (order : plan.order = .dataThenMetas)
    (allocation : types.bytes.withCapacity before types.enumSize (.returned data allocated))
    (writes : writeData types data plan.dataSteps allocated () (.returned () written))
    (metas : buildMetas types plan.metas written () metadata)
    (cleanup : Owned.onUnwind types.doubleUnwind
      [fun state => types.bytes.drop state data]
      (Outcome.map (fun resource => Except.ok
        ({ programId := plan.programId, metas := resource, data } : Value types)) metadata) final) :
    run types before plan final := by
  unfold run
  rw [admitted, order]
  refine ⟨.returned data allocated, allocation, ?_⟩
  refine ⟨_, ?_, cleanup⟩
  exact ⟨.returned () written, writes, metadata, metas, rfl⟩

/-- A first allocation unwind precedes byte writes and metadata allocation;
there is no vector owner for the constructor to clean up yet. -/
theorem run_capacity_unwound {types : Types} {before after : types.State} {plan : Plan}
    {reason : types.Unwind}
    (admitted : Instruction.checkProgram plan.programs plan.programId = .ok ())
    (order : plan.order = .dataThenMetas)
    (allocation : types.bytes.withCapacity before types.enumSize (.unwound reason after)) :
    run types before plan (.unwound reason after) := by
  unfold run
  rw [admitted, order]
  exact ⟨.unwound reason after, allocation, rfl⟩

/-- In a metadata-first constructor the completed metadata owner remains
protected across byte allocation, packing and the local cleanup of the packing. -/
theorem run_from_prepared_metas {types : Types} {before : types.State} {plan : Plan}
    {metas : types.MetaResource} {prepared : types.State}
    {data : Outcome types.State types.ByteResource types.Unwind types.Terminal}
    {final : Outcome types.State (Except Error (Value types)) types.Unwind types.Terminal}
    (admitted : Instruction.checkProgram plan.programs plan.programId = .ok ())
    (order : plan.order = .metasThenData)
    (metadata : buildMetas types plan.metas before () (.returned metas prepared))
    (packing : buildData types plan.dataSteps prepared () data)
    (cleanup : Owned.onUnwind types.doubleUnwind
      [fun state => types.metas.drop state metas]
      (Outcome.map (fun resource => Except.ok
        ({ programId := plan.programId, metas, data := resource } : Value types)) data) final) :
    run types before plan final := by
  unfold run
  rw [admitted, order]
  exact ⟨.returned metas prepared, metadata, _, ⟨data, packing, rfl⟩, cleanup⟩

/-- Metadata construction can unwind before a metadata-first constructor
ever allocates or writes a byte vector. -/
theorem run_metas_unwound {types : Types} {before after : types.State} {plan : Plan}
    {reason : types.Unwind}
    (admitted : Instruction.checkProgram plan.programs plan.programId = .ok ())
    (order : plan.order = .metasThenData)
    (metadata : buildMetas types plan.metas before () (.unwound reason after)) :
    run types before plan (.unwound reason after) := by
  unfold run
  rw [admitted, order]
  exact ⟨.unwound reason after, metadata, rfl⟩

/-- Packing protects its actual byte owner, including partial contents left
by a failed push or extension, before returning or unwinding to its caller. -/
theorem build_data_allocated {types : Types} {before allocated : types.State}
    {steps : List DataStep} {resource : types.ByteResource}
    {written : Outcome types.State Unit types.Unwind types.Terminal}
    {final : Outcome types.State types.ByteResource types.Unwind types.Terminal}
    (allocation : types.bytes.withCapacity before types.enumSize (.returned resource allocated))
    (writes : writeData types resource steps allocated () written)
    (cleanup : Owned.onUnwind types.doubleUnwind
      [fun state => types.bytes.drop state resource]
      (Outcome.map (fun _ => resource) written) final) :
    buildData types steps before () final :=
  ⟨.returned resource allocated, allocation, _, ⟨written, writes, rfl⟩, cleanup⟩

/-- A reserved metadata vector is protected while its individual pushes run.
The supplied cleanup receives the state of the actual final push outcome. -/
theorem build_metas_reserved {types : Types} {before allocated : types.State}
    {capacity : Nat} {items : List Solanalib.Runtime.CpiMeta} {resource : types.MetaResource}
    {pushed : Outcome types.State Unit types.Unwind types.Terminal}
    {final : Outcome types.State types.MetaResource types.Unwind types.Terminal}
    (allocation : types.metas.withCapacity before capacity (.returned resource allocated))
    (pushes : pushMetas types resource items allocated () pushed)
    (cleanup : Owned.onUnwind types.doubleUnwind
      [fun state => types.metas.drop state resource]
      (Outcome.map (fun _ => resource) pushed) final) :
    buildMetas types (.withCapacity capacity items) before () final := by
  exact ⟨.returned resource allocated, allocation,
    _, ⟨pushed, pushes, rfl⟩, cleanup⟩

/-- A literal prefix is constructed once, then the actual retained metadata
owner is protected while the remaining signer pushes run. -/
theorem build_metas_literal_tail {types : Types} {before allocated : types.State}
    {initial rest : List Solanalib.Runtime.CpiMeta} {resource : types.MetaResource}
    {pushed : Outcome types.State Unit types.Unwind types.Terminal}
    {final : Outcome types.State types.MetaResource types.Unwind types.Terminal}
    (allocation : types.metas.fromList before initial (.returned resource allocated))
    (pushes : pushMetas types resource rest allocated () pushed)
    (cleanup : Owned.onUnwind types.doubleUnwind
      [fun state => types.metas.drop state resource]
      (Outcome.map (fun _ => resource) pushed) final) :
    buildMetas types (.fromListThenPush initial rest) before () final :=
  ⟨.returned resource allocated, allocation, _, ⟨pushed, pushes, rfl⟩, cleanup⟩

/-- Two independent typed ledgers, retaining a tombstone after retirement. -/
abbrev State := Owned.VectorState UInt8 × Owned.VectorState Solanalib.Runtime.CpiMeta

/-- A concrete mathematical dependency interpretation. The enum reservation
128 is an explicit sample parameter, not a measured Rust layout. Its vector
operations return normally; other family members may fail or terminate. -/
def sampleTypes : Types where
  State := State
  ByteResource := Nat
  MetaResource := Nat
  Unwind := Nat
  Terminal := Nat
  wordBits := 64
  enumSize := 128
  bytes := Owned.vectorReference.focus Owned.Focus.fst
  metas := Owned.vectorReference.focus Owned.Focus.snd
  doubleUnwind := fun _ original later terminal => terminal = original + later

/-- Both typed ledgers start without allocated or retired slots. -/
def initialState : State := ([], [])

/-- The closed byte provider satisfies every stated primitive ownership law. -/
theorem sample_bytes_laws : sampleTypes.bytes.Laws :=
  Owned.VectorOps.focus_laws Owned.vectorReference_laws Owned.Focus.fst

/-- The separate metadata provider satisfies the same primitive laws. -/
theorem sample_metas_laws : sampleTypes.metas.Laws :=
  Owned.VectorOps.focus_laws Owned.vectorReference_laws Owned.Focus.snd

/-- Byte allocation preserves the entire metadata ledger. -/
theorem bytes_capacity (bytes : Owned.VectorState UInt8)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (capacity : Nat) :
    sampleTypes.bytes.withCapacity (bytes, metas) capacity
      (.returned bytes.length (bytes ++ [some []], metas)) :=
  ⟨.returned bytes.length (bytes ++ [some []]), rfl, rfl⟩

/-- The concrete byte push updates its retained live slot. -/
theorem bytes_push (bytes : Solanalib.Runtime.Bytes) (metas : Owned.VectorState
  Solanalib.Runtime.CpiMeta)
    (value : UInt8) :
    sampleTypes.bytes.push ([some bytes], metas) ((0 : Nat), value)
      (.returned () ([some (bytes ++ [value])], metas)) :=
  ⟨.returned () [some (bytes ++ [value])], ⟨bytes, rfl, rfl⟩, rfl⟩

/-- Bulk extension is a distinct provider call with the supplied entire slice. -/
theorem bytes_extend (bytes extra : Solanalib.Runtime.Bytes) (metas : Owned.VectorState
  Solanalib.Runtime.CpiMeta) :
    sampleTypes.bytes.extend ([some bytes], metas) ((0 : Nat), extra)
      (.returned () ([some (bytes ++ extra)], metas)) :=
  ⟨.returned () [some (bytes ++ extra)], ⟨bytes, rfl, rfl⟩, rfl⟩

/-- Byte cleanup retires its current token while retaining all metadata state. -/
theorem bytes_drop (bytes : Solanalib.Runtime.Bytes) (metas : Owned.VectorState
  Solanalib.Runtime.CpiMeta) :
    sampleTypes.bytes.drop ([some bytes], metas) (0 : Nat)
      (.returned () ([none], metas)) :=
  ⟨.returned () [none], ⟨bytes, rfl, rfl⟩, rfl⟩

/-- Metadata allocation leaves every byte allocation untouched. -/
theorem metas_capacity (bytes : Owned.VectorState UInt8)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (capacity : Nat) :
    sampleTypes.metas.withCapacity (bytes, metas) capacity
      (.returned metas.length (bytes, metas ++ [some []])) :=
  ⟨.returned metas.length (metas ++ [some []]), rfl, rfl⟩

/-- Literal metadata construction transfers the exact complete ordered array. -/
theorem metas_from_list (bytes : Owned.VectorState UInt8)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) (items : List Solanalib.Runtime.CpiMeta) :
    sampleTypes.metas.fromList (bytes, metas) items
      (.returned metas.length (bytes, metas ++ [some items])) :=
  ⟨.returned metas.length (metas ++ [some items]), rfl, rfl⟩

/-- Metadata push retains duplicates and changes only the current owned vector. -/
theorem metas_push (bytes : Owned.VectorState UInt8) (items : List Solanalib.Runtime.CpiMeta)
    (item : Solanalib.Runtime.CpiMeta) :
    sampleTypes.metas.push (bytes, [some items]) ((0 : Nat), item)
      (.returned () (bytes, [some (items ++ [item])])) :=
  ⟨.returned () [some (items ++ [item])], ⟨items, rfl, rfl⟩, rfl⟩

/-- Metadata cleanup retires its current token, without changing byte state. -/
theorem metas_drop (bytes : Owned.VectorState UInt8) (items : List Solanalib.Runtime.CpiMeta) :
    sampleTypes.metas.drop (bytes, [some items]) (0 : Nat)
      (.returned () (bytes, [none])) :=
  ⟨.returned () [none], ⟨items, rfl, rfl⟩, rfl⟩

/-- Every actual push and extension in a plan has an execution on the sample
ledger. The proof composes those calls, rather than assigning the final bytes. -/
theorem write_data_returns (steps : List DataStep) (prior : Solanalib.Runtime.Bytes)
    (metas : Owned.VectorState Solanalib.Runtime.CpiMeta) :
    writeData sampleTypes (0 : Nat) steps ([some prior], metas) ()
      (.returned () ([some (prior ++ steps.flatMap DataStep.bytes)], metas)) := by
  induction steps generalizing prior with
  | nil => simp [writeData]
  | cons step steps induction =>
    cases step with
    | push byte =>
      refine ⟨.returned () ([some (prior ++ [byte])], metas), bytes_push _ _ _, ?_⟩
      simpa [DataStep.bytes, List.append_assoc] using induction (prior ++ [byte])
    | extend extra =>
      refine ⟨.returned () ([some (prior ++ extra)], metas), bytes_extend _ _ _, ?_⟩
      simpa [DataStep.bytes, List.append_assoc] using induction (prior ++ extra)

/-- The reserved metadata branch executes one provider push per source item. -/
theorem push_metas_returns (items prior : List Solanalib.Runtime.CpiMeta)
    (bytes : Owned.VectorState UInt8) :
    pushMetas sampleTypes (0 : Nat) items (bytes, [some prior]) ()
      (.returned () (bytes, [some (prior ++ items)])) := by
  induction items generalizing prior with
  | nil => simp [pushMetas]
  | cons item items induction =>
    refine ⟨.returned () (bytes, [some (prior ++ [item])]), metas_push _ _ _, ?_⟩
    simpa [List.append_assoc] using induction (prior ++ [item])

/-- Every metadata-construction form has a complete normal execution,
preserving whichever byte ledger exists at this source point. -/
theorem build_metas_returns (plan : MetaPlan) (bytes : Owned.VectorState UInt8) :
    buildMetas sampleTypes plan (bytes, []) ()
      (.returned (0 : Nat) (bytes, [some plan.items])) := by
  cases plan with
  | fromList items => exact metas_from_list _ [] items
  | withCapacity capacity items =>
    refine build_metas_reserved (metas_capacity bytes [] capacity)
      (push_metas_returns items [] bytes) ?_
    rfl
  | fromListThenPush initial rest =>
    refine build_metas_literal_tail (metas_from_list bytes [] initial)
      (push_metas_returns rest initial bytes) ?_
    rfl

/-- Packing has a complete normal execution while preserving any earlier
metadata owner; all byte pushes and extensions are executed individually. -/
theorem build_data_returns (steps : List DataStep) (metas : Owned.VectorState
  Solanalib.Runtime.CpiMeta) :
    buildData sampleTypes steps ([], metas) ()
      (.returned (0 : Nat) ([some (steps.flatMap DataStep.bytes)], metas)) := by
  exact build_data_allocated (bytes_capacity [] metas sampleTypes.enumSize)
    (write_data_returns steps [] metas) rfl

/-- Each returned handle selects the first slot of its own typed ledger;
both numerical indices are zero. -/
def returnedValue (plan : Plan) : Value sampleTypes := ⟨plan.programId, (0 : Nat), (0 : Nat)⟩

/-- The successful constructor retains the packed data and ordered metadata
in the two live slots owned by its returned instruction. -/
def returnedState (plan : Plan) : State := ([some plan.data], [some plan.metas.items])

/-- Any admitted plan has a successful execution on the concrete two-ledger
reference. Both owners move out normally and are not cleaned up. -/
theorem run_returns (plan : Plan)
    (admitted : Instruction.checkProgram plan.programs plan.programId = .ok ()) :
    run sampleTypes initialState plan
      (.returned (.ok (returnedValue plan)) (returnedState plan)) := by
  cases order : plan.order with
  | dataThenMetas =>
    exact run_from_prepared_data admitted order (bytes_capacity [] [] sampleTypes.enumSize)
      (write_data_returns plan.dataSteps [] []) (build_metas_returns plan.metas [some plan.data])
        rfl
  | metasThenData =>
    exact run_from_prepared_metas admitted order (build_metas_returns plan.metas [])
      (build_data_returns plan.dataSteps [some plan.metas.items]) rfl

/-- The successful operational result observes exactly the wire value of the plan. -/
theorem returned_observation (plan : Plan) :
    observe sampleTypes (returnedState plan) (returnedValue plan) =
      some plan.instruction := rfl

/-- Success retains both live vector resources, rather than their old snapshots. -/
theorem returned_ownership (plan : Plan) :
    sampleTypes.bytes.current (returnedState plan) (returnedValue plan).data = some plan.data ∧
      sampleTypes.metas.current (returnedState plan) (returnedValue plan).metas =
        some plan.metas.items := ⟨rfl, rfl⟩


end Solanalib.Specs.Core.Token.InstructionAllocated.Witness
