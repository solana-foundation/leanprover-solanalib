/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Instruction
public import Solanalib.Specs.Core.FieldReference
public import Solanalib.Specs.Core.OwnedCleanup
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionClone

/-- Primitive Vec clone, with the same current-resource vocabulary used by
builders. The dependency owns partial initialization and its cleanup. -/
structure VectorClone (State Element Resource Unwind Terminal : Type) where
  vectors : Owned.VectorOps State Element Resource Unwind Terminal
  copy : Callback.Run State Resource Resource Unwind Terminal

/-- Exact contents and freshness on a returned primitive clone. The input is
borrowed and remains live with the same contents. Other-resource frames are
separate, because these local laws alone do not imply them. -/
structure VectorClone.Laws {State Element Resource Unwind Terminal : Type}
    (ops : VectorClone State Element Resource Unwind Terminal) : Prop where
  contents : ∀ before source values copy after,
    ops.vectors.current before source = some values →
    ops.copy before source (.returned copy after) →
      ops.vectors.current after copy = some values
  fresh : ∀ before source copy after,
    ops.copy before source (.returned copy after) →
      ops.vectors.current before copy = none
  source : ∀ before source values copy after,
    ops.vectors.current before source = some values →
    ops.copy before source (.returned copy after) →
      ops.vectors.current after source = some values

structure Types where
  State : Type
  Reference : Type
  MetaResource : Type
  ByteResource : Type
  Unwind : Type
  Terminal : Type

abbrev Value (types : Types) :=
  Instruction.OwnedValue types.MetaResource types.ByteResource

structure Providers (types : Types) where
  access : FieldReference.Access types.State types.Reference (Value types)
  metas : VectorClone types.State Instruction.Meta types.MetaResource types.Unwind types.Terminal
  bytes : VectorClone types.State UInt8 types.ByteResource types.Unwind types.Terminal
  doubleUnwind : Owned.DoubleUnwind types.State types.Unwind types.Terminal

structure Args (types : Types) where
  source : types.Reference
  providers : Providers types

/-- Derived field order is program ID, metadata Vec, then byte Vec. Only the
new metadata Vec is owned if the second clone unwinds; the borrowed instruction
and its vectors are never dropped by this operation. -/
def copyRun (types : Types) (providers : Providers types) (source : Value types) :
    Callback.Run types.State Unit (Value types) types.Unwind types.Terminal :=
  fun before _ => Callback.bind providers.metas.copy
    (fun metas after => Owned.protect providers.doubleUnwind
      [providers.metas.vectors.dropAction metas]
      (fun state _ => Callback.map
        (fun bytes => (⟨source.programId, metas, bytes⟩ : Value types))
        providers.bytes.copy state source.data)
      after ()) before source.metas

def run (types : Types) (before : types.State) (args : Args types)
    (outcome : Outcome types.State (Value types) types.Unwind types.Terminal) : Prop :=
  ∃ source, args.providers.access.current before args.source = some source ∧
    copyRun types args.providers source before () outcome

def family : Family where
  Index := Types
  State := Types.State
  Args := Args
  Value := Value
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun types => {
    requires := fun before args =>
      ∃ source, args.providers.access.Reads before args.source source
    post := fun before args outcome =>
      ∃ source, args.providers.access.Reads before args.source source ∧
        copyRun types args.providers source before () outcome }

def reference : FamilyRun family := run

theorem reference_correct : FamilyReference family reference := by
  intro types before args outcome admitted execution
  obtain ⟨source, current, copied⟩ := execution
  obtain ⟨_, live, _⟩ := admitted
  exact ⟨source, ⟨live, current⟩, copied⟩

/-- Two normal dependency clones construct exactly the two returned handles.
The byte clone starts in the actual state returned by the metadata clone. -/
theorem copyRun_returned (types : Types) (providers : Providers types)
    (source : Value types) (before middle after : types.State)
    (metas : types.MetaResource) (bytes : types.ByteResource)
    (metaCopy : providers.metas.copy before source.metas (.returned metas middle))
    (byteCopy : providers.bytes.copy middle source.data (.returned bytes after)) :
    copyRun types providers source before ()
      (.returned ⟨source.programId, metas, bytes⟩ after) := by
  refine ⟨.returned metas middle, metaCopy, ?_⟩
  refine ⟨.returned ⟨source.programId, metas, bytes⟩ after, ?_, rfl⟩
  exact ⟨.returned bytes after, byteCopy, rfl⟩

/-- The exact observed clone follows from local Vec clone laws and the one
needed frame: cloning bytes preserves the newly cloned metadata contents.
The original source bytes are read in the actual second-call state. -/
theorem observe_returned (types : Types) (providers : Providers types)
    (source : Value types) (before middle after : types.State)
    (metas : types.MetaResource) (bytes : types.ByteResource)
    (accounts : List Instruction.Meta) (data : _root_.Solanalib.Runtime.Bytes)
    (metaLaws : providers.metas.Laws) (byteLaws : providers.bytes.Laws)
    (metaCurrent : providers.metas.vectors.current before source.metas = some accounts)
    (byteCurrent : providers.bytes.vectors.current middle source.data = some data)
    (metaCopy : providers.metas.copy before source.metas (.returned metas middle))
    (byteCopy : providers.bytes.copy middle source.data (.returned bytes after))
    (frame : providers.metas.vectors.current after metas =
      providers.metas.vectors.current middle metas) :
    (⟨source.programId, metas, bytes⟩ : Value types).observe
      (providers.metas.vectors.current after) (providers.bytes.vectors.current after) =
      some (Instruction.make source.programId accounts data) := by
  apply Instruction.OwnedValue.observe_of_current
  · rw [frame]
    exact metaLaws.contents before source.metas accounts metas middle metaCurrent metaCopy
  · exact byteLaws.contents middle source.data data bytes after byteCurrent byteCopy

/-- Primitive freshness prevents treating the borrowed source owner as the owner of the
new clone whenever the source has represented current contents. -/
theorem returned_resource_distinct {State Element Resource Unwind Terminal : Type}
    (ops : VectorClone State Element Resource Unwind Terminal) (laws : ops.Laws)
    (before after : State) (source copy : Resource) (values : List Element)
    (current : ops.vectors.current before source = some values)
    (copied : ops.copy before source (.returned copy after)) : copy ≠ source := by
  intro same
  have fresh := laws.fresh before source copy after copied
  rw [same, current] at fresh
  cases fresh

end Solanalib.Specs.Core.InstructionClone
