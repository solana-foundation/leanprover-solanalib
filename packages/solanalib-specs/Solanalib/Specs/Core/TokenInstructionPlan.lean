/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionConstructors

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.InstructionAllocated

open Solanalib.Specs.Core.Token.Instruction

/-- Distinguish the single-byte push of the source from its bulk slice extension. -/
inductive DataStep where
  /-- One source Vec::push of a byte. -/
  | push (byte : UInt8)
  /-- One source extension of an ordered byte slice. -/
  | extend (bytes : Bytes)
  deriving DecidableEq, Repr

/-- A Vec literal and a reserved, subsequently populated Vec have different
allocation and cleanup boundaries even when their final values coincide. -/
inductive MetaPlan where
  /-- One literal metadata-vector constructor call. -/
  | fromList (items : List Solanalib.Runtime.CpiMeta)
  /-- Reserve once, then push the supplied metadata in order. -/
  | withCapacity (capacity : Nat) (items : List Solanalib.Runtime.CpiMeta)
  /-- Construct a literal prefix, then push the remaining metadata in order. -/
  | fromListThenPush (initial rest : List Solanalib.Runtime.CpiMeta)
  deriving DecidableEq, Repr

/-- The two vector owners may be constructed in different source orders. -/
inductive BuildOrder where
  /-- Pack instruction data before constructing the account metadata. -/
  | dataThenMetas
  /-- Complete account metadata before packing the returned instruction data. -/
  | metasThenData
  deriving DecidableEq, Repr

/-- The finite SDK constructor plan. TokenInstruction::pack reserves its
target-dependent enum size and then performs the specified byte writes. The
order field places that operation relative to metadata construction; program
admission precedes every allocation in either order. -/
structure Plan where
  /-- The program IDs accepted before any allocation call. -/
  programs : ProgramSet
  /-- The caller-supplied program ID retained in the instruction. -/
  programId : Solanalib.Runtime.Pubkey
  /-- Source-ordered byte push and extension calls. -/
  dataSteps : List DataStep
  /-- The source metadata construction strategy and ordered values. -/
  metas : MetaPlan
  /-- Source evaluation order of metadata construction and byte packing. -/
  order : BuildOrder := .dataThenMetas
  deriving DecidableEq, Repr

/-- Transfer uses a legacy-only admission and reserves the complete metadata
count before ordered pushes, including repeated external signers. -/
def transferPlan (args : TransferArgs) : Plan := {
  programs := .legacy
  programId := args.programId
  dataSteps := [.push 3, .extend (Solanalib.Runtime.u64le args.amount)]
  metas := .withCapacity (3 + args.signers.length)
    (authorityInstruction args.toAuthorityArgs (transferData args.amount)).metas }

/-- Checked transfer packs the decimal as a separate single-byte push. -/
def transferCheckedPlan (programs : ProgramSet) (args : TransferCheckedArgs) : Plan := {
  programs
  programId := args.programId
  dataSteps := [.push 12, .extend (Solanalib.Runtime.u64le args.amount), .push (UInt8.ofNat
    args.decimals)]
  metas := .withCapacity (4 + args.signers.length) (transferCheckedInstruction args).metas }

/-- The expected returned byte value, separate from its allocation lifecycle. -/
def DataStep.bytes : DataStep → Bytes
  | .push byte => [byte]
  | .extend bytes => bytes

/-- The value observation of a plan does not assert that its allocation steps return. -/
def Plan.data (plan : Plan) : Bytes := plan.dataSteps.flatMap DataStep.bytes

/-- Every metadata construction form retains the supplied ordered values. -/
def MetaPlan.items : MetaPlan → List Solanalib.Runtime.CpiMeta
  | .fromList items => items
  | .withCapacity _ items => items
  | .fromListThenPush initial rest => initial ++ rest

/-- The value-level observation of a completed constructor. -/
def Plan.instruction (plan : Plan) : Solanalib.Runtime.CpiInstruction :=
  ⟨plan.programId, plan.metas.items, plan.data⟩

/-- The allocation plan retains the data and metadata of the checked transfer. -/
theorem transferCheckedPlan_value (programs : ProgramSet) (args : TransferCheckedArgs) :
    (transferCheckedPlan programs args).instruction = transferCheckedInstruction args := by
  simp [Plan.instruction, Plan.data, MetaPlan.items, transferCheckedPlan,
    transferCheckedInstruction, transferCheckedData, DataStep.bytes,
    Solanalib.Specs.Core.Instruction.make]


end Solanalib.Specs.Core.Token.InstructionAllocated
