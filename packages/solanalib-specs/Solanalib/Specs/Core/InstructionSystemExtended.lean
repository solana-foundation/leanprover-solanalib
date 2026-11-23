/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionBuilderFamily

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionSystemExtended

structure PrefundSource where
  newAccount : _root_.Solanalib.Runtime.Pubkey
  payer : Option (_root_.Solanalib.Runtime.Pubkey × Nat)
  space : Nat
  owner : _root_.Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- `Some (payer, 0)` still adds a payer; aliases remain separate metadata
positions. This is local instruction construction, without runtime checks. -/
def PrefundSource.metas (source : PrefundSource) : List Instruction.Meta :=
  [Instruction.accountMeta source.newAccount true true] ++
    match source.payer with
    | none => []
    | some (payer, _) => [Instruction.accountMeta payer true true]

def PrefundSource.lamports (source : PrefundSource) : Nat :=
  match source.payer with
  | none => 0
  | some (_, lamports) => lamports

structure PrefundData where
  lamports : Nat
  space : Nat
  owner : _root_.Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

def PrefundData.bytes (data : PrefundData) : _root_.Solanalib.Runtime.Bytes :=
  _root_.Solanalib.Runtime.u32le 13 ++ _root_.Solanalib.Runtime.u64le data.lamports ++
    _root_.Solanalib.Runtime.u64le data.space ++ data.owner.bytes

def PrefundSource.data (source : PrefundSource) : PrefundData :=
  ⟨source.lamports, source.space, source.owner⟩

def PrefundSource.value (source : PrefundSource) : Instruction.Value :=
  Instruction.make Instruction.systemProgramId source.metas source.data.bytes

structure SeedSource where
  fromAddress : _root_.Solanalib.Runtime.Pubkey
  toAddress : _root_.Solanalib.Runtime.Pubkey
  base : _root_.Solanalib.Runtime.Pubkey
  seed : _root_.Solanalib.Runtime.Bytes
  lamports : Nat
  space : Nat
  owner : _root_.Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- The reviewed 1.0.0/legacy constructors always include the third metadata
position, including when the base equals the funding or destination key. -/
def SeedSource.metas (source : SeedSource) : List Instruction.Meta :=
  [Instruction.accountMeta source.fromAddress true true,
    Instruction.accountMeta source.toAddress false true,
    Instruction.accountMeta source.base true false]

/-- Exact bincode enum/string encoding: byte length, then all seed bytes.
No seed-length or derived-address check is performed by this constructor.
UTF-8, source integer widths and target layouts are separate bindings. -/
def seedBytes (base : _root_.Solanalib.Runtime.Pubkey) (seed : _root_.Solanalib.Runtime.Bytes)
    (lamports space : Nat) (owner : _root_.Solanalib.Runtime.Pubkey) :
      _root_.Solanalib.Runtime.Bytes :=
  _root_.Solanalib.Runtime.u32le 3 ++ base.bytes ++ _root_.Solanalib.Runtime.u64le seed.length ++
    seed ++
    _root_.Solanalib.Runtime.u64le lamports ++ _root_.Solanalib.Runtime.u64le space ++ owner.bytes

def SeedSource.value (source : SeedSource) : Instruction.Value :=
  Instruction.make Instruction.systemProgramId source.metas
    (seedBytes source.base source.seed source.lamports source.space source.owner)

structure Types where
  State : Type
  MetaResource : Type
  ByteResource : Type
  Error : Type
  Unwind : Type
  Terminal : Type

def Types.builder (types : Types) (Data : Type) : InstructionBuilder.Types :=
  ⟨types.State, Data, types.MetaResource, types.ByteResource,
    types.Error, types.Unwind, types.Terminal⟩

structure PrefundArgs (types : Types) where
  source : PrefundSource
  format : InstructionBuilder.Format
  providers : InstructionBuilder.Providers (types.builder PrefundData)

/-- A possible push is protected before the vector is moved into Instruction.
Once moved, the existing builder alone owns its unwind cleanup. -/
def prefundAfterAllocation (types : Types) (args : PrefundArgs types)
    (metas : types.MetaResource) :
    Callback.Run types.State Unit (InstructionBuilder.Value (types.builder PrefundData))
      types.Unwind types.Terminal :=
  fun before _ =>
    let construct := fun state => InstructionBuilder.run (types.builder PrefundData)
      args.format state ⟨Instruction.systemProgramId, args.source.data, metas, args.providers⟩
    match args.source.payer with
    | none => construct before
    | some (payer, _) =>
      Callback.bind
        (Owned.protect args.providers.doubleUnwind
          [args.providers.metaVec.dropAction metas]
          args.providers.metaVec.push)
        (fun _ after => construct after)
        before (metas, Instruction.accountMeta payer true true)

def prefundRun (types : Types) (before : types.State) (args : PrefundArgs types) :
    Outcome types.State (InstructionBuilder.Value (types.builder PrefundData))
      types.Unwind types.Terminal → Prop :=
  Callback.bind args.providers.metaVec.fromList
    (fun metas after => prefundAfterAllocation types args metas after ())
    before [Instruction.accountMeta args.source.newAccount true true]

def prefundFamily : Family where
  Index := Types
  State := Types.State
  Args := PrefundArgs
  Value := fun types => InstructionBuilder.Value (types.builder PrefundData)
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun types => { requires := fun _ _ => True, post := prefundRun types }

def prefundReference : FamilyRun prefundFamily := prefundRun

theorem prefundReference_correct : FamilyReference prefundFamily prefundReference := by
  intro _ _ _ _ _ execution
  exact execution

structure SeedTypes extends Types where
  SeedResource : Type

/-- The temporary SystemInstruction contains the owned String identity, not a
saved copy of its bytes. Serialization must observe it in its current state. -/
structure SeedData (SeedResource : Type) where
  base : _root_.Solanalib.Runtime.Pubkey
  seed : SeedResource
  lamports : Nat
  space : Nat
  owner : _root_.Solanalib.Runtime.Pubkey

def SeedTypes.builder (types : SeedTypes) : InstructionBuilder.Types :=
  types.toTypes.builder (SeedData types.SeedResource)

structure SeedArgs (types : SeedTypes) where
  source : SeedSource
  providers : InstructionBuilder.Providers types.builder
  /-- The source `str::to_string` copy and String cleanup use owned vector
  resources. UTF-8 is not revalidated; it is guaranteed by the Rust input. -/
  strings : Owned.VectorOps types.State UInt8 types.SeedResource types.Unwind types.Terminal

def seedData (types : SeedTypes) (source : SeedSource) (seed : types.SeedResource) :
    SeedData types.SeedResource :=
  ⟨source.base, seed, source.lamports, source.space, source.owner⟩

/-- Drop the temporary String after the constructor call, including its unwind
path. If that drop itself unwinds after construction, the not-yet-returned
Instruction is cleaned in struct field order by this generalized provider
graph. Termination skips all later cleanup. The pinned source interpretation
requires lawful GlobalAlloc String deallocation, which cannot unwind. The
generalized unwind branch is not compiler return-place cleanup evidence. -/
def finishSeed (types : SeedTypes) (args : SeedArgs types) (seed : types.SeedResource)
    (pending final : Outcome types.State (InstructionBuilder.Value types.builder)
      types.Unwind types.Terminal) : Prop :=
  match pending with
  | .returned instruction state =>
    Owned.protect args.providers.doubleUnwind
      [args.providers.metaVec.dropAction instruction.metas,
        args.providers.byteVec.dropAction instruction.data]
      (fun before _ outcome => Owned.cleanup args.providers.doubleUnwind
        [args.strings.dropAction seed] (.returned instruction before) outcome)
      state () final
  | .unwound reason state => Owned.cleanup args.providers.doubleUnwind
      [args.strings.dropAction seed] (.unwound reason state) final
  | .terminated reason => final = .terminated reason

def seedAfterCopy (types : SeedTypes) (args : SeedArgs types)
    (metas : types.MetaResource) (seed : types.SeedResource) (before : types.State)
    (final : Outcome types.State (InstructionBuilder.Value types.builder)
      types.Unwind types.Terminal) : Prop :=
  ∃ pending, InstructionBuilder.run types.builder .bincode before
      ⟨Instruction.systemProgramId, seedData types args.source seed, metas, args.providers⟩ pending
        ∧
    finishSeed types args seed pending final

/-- Account metadata is allocated first; String copying is protected by the
still-local metadata owner. Only after that copy returns are metadata moved
into the serializer/unwrap/cleanup operation of Instruction. -/
def seedAfterAllocation (types : SeedTypes) (args : SeedArgs types)
    (metas : types.MetaResource) (before : types.State) :
    Outcome types.State (InstructionBuilder.Value types.builder)
      types.Unwind types.Terminal → Prop :=
  Callback.bind
    (Owned.protect args.providers.doubleUnwind
      [args.providers.metaVec.dropAction metas] args.strings.fromList)
    (fun seed after => seedAfterCopy types args metas seed after)
    before args.source.seed

def seedRun (types : SeedTypes) (before : types.State) (args : SeedArgs types) :
    Outcome types.State (InstructionBuilder.Value types.builder)
      types.Unwind types.Terminal → Prop :=
  Callback.bind args.providers.metaVec.fromList
    (fun metas after => seedAfterAllocation types args metas after)
    before args.source.metas

def seedFamily : Family where
  Index := SeedTypes
  State := fun types => types.State
  Args := SeedArgs
  Value := fun types => InstructionBuilder.Value types.builder
  Unwind := fun types => types.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => { requires := fun _ _ => True, post := seedRun types }

def seedReference : FamilyRun seedFamily := seedRun

theorem seedReference_correct : FamilyReference seedFamily seedReference := by
  intro _ _ _ _ _ execution
  exact execution

/-- A normal temporary drop preserves the built instruction, at the actual
post-drop state; it does not drop the transferred resources of the result. -/
theorem finishSeed_returned (types : SeedTypes) (args : SeedArgs types)
    (seed : types.SeedResource) (instruction : InstructionBuilder.Value types.builder)
    (before after : types.State)
    (dropped : args.strings.drop before seed (.returned () after)) :
    finishSeed types args seed (.returned instruction before) (.returned instruction after) := by
  refine ⟨.returned instruction after, ?_, rfl⟩
  exact ⟨.returned () after, dropped, rfl⟩

/-- Serialization receives the exact temporary identity, and a normal drop
then consumes that temporary without replacing the returned vectors. -/
theorem seedAfterCopy_returned (types : SeedTypes) (args : SeedArgs types)
    (metas : types.MetaResource) (seed : types.SeedResource) (bytes : types.ByteResource)
    (before serialized after : types.State)
    (encoding : args.providers.serialize before (.bincode, seedData types args.source seed)
      (.returned (.ok bytes) serialized))
    (dropped : args.strings.drop serialized seed (.returned () after)) :
    seedAfterCopy types args metas seed before
      (.returned ⟨Instruction.systemProgramId, metas, bytes⟩ after) := by
  refine ⟨.returned ⟨Instruction.systemProgramId, metas, bytes⟩ serialized, ?_, ?_⟩
  · exact InstructionBuilder.run_of_serialized _ _ _ _ _ _ encoding
  · exact finishSeed_returned types args seed _ serialized after dropped

end Solanalib.Specs.Core.InstructionSystemExtended
