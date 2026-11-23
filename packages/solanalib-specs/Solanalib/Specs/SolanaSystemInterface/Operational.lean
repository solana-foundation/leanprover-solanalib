/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaSystemInterface.Instruction
public import Solanalib.Specs.Core.InstructionBuilderSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaSystemInterface.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The actual variants supplied to the feature-selected serializer. Source
integer representation belongs to the interpretation of that serializer. -/
inductive SystemData where
  | createAccount (lamports space : Nat) (owner : _root_.Solanalib.Runtime.Pubkey)
  | transfer (lamports : Nat)

def SystemData.bytes : SystemData → _root_.Solanalib.Runtime.Bytes
  | .createAccount lamports space owner =>
    _root_.Solanalib.Runtime.u32le 0 ++ _root_.Solanalib.Runtime.u64le lamports ++
      _root_.Solanalib.Runtime.u64le space ++ owner.bytes
  | .transfer lamports => Instruction.systemAmountData 2 lamports

structure OperationalTypes where
  State : Type
  MetaResource : Type
  ByteResource : Type
  Error : Type
  Unwind : Type
  Terminal : Type

def OperationalTypes.builder (types : OperationalTypes) : InstructionBuilder.Types :=
  ⟨types.State, SystemData, types.MetaResource, types.ByteResource,
    types.Error, types.Unwind, types.Terminal⟩

structure CreateAccountOperationalArgs (types : OperationalTypes) where
  source : CreateAccountArgs
  format : InstructionBuilder.Format
  providers : InstructionBuilder.Providers types.builder

structure TransferOperationalArgs (types : OperationalTypes) where
  source : TransferArgs
  format : InstructionBuilder.Format
  providers : InstructionBuilder.Providers types.builder

def createAccountAllocation (types : OperationalTypes) (args : CreateAccountOperationalArgs types) :
    InstructionBuilder.AllocateArgs types.builder where
  programId := Instruction.systemProgramId
  data := .createAccount args.source.lamports args.source.space args.source.owner
  accounts := [Instruction.accountMeta args.source.fromAddress true true,
    Instruction.accountMeta args.source.toAddress true true]
  providers := args.providers

def transferAllocation (types : OperationalTypes) (args : TransferOperationalArgs types) :
    InstructionBuilder.AllocateArgs types.builder where
  programId := Instruction.systemProgramId
  data := .transfer args.source.lamports
  accounts := [Instruction.accountMeta args.source.fromAddress true true,
    Instruction.accountMeta args.source.toAddress false true]
  providers := args.providers

/-- Complete constructor control flow above explicit vector, serializer,
unwrap-failure and drop dependencies. A value observation remains separately
available; deriving it needs the local primitive/codec/frame guarantees. -/
def create_account_operational_contract : Family where
  Index := OperationalTypes
  State := OperationalTypes.State
  Args := CreateAccountOperationalArgs
  Value := fun types => InstructionBuilder.Value types.builder
  Unwind := OperationalTypes.Unwind
  Terminal := OperationalTypes.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args => InstructionBuilder.allocateRun types.builder args.format before
      (createAccountAllocation types args) }

def create_account_operational_run : FamilyRun create_account_operational_contract :=
  fun types before args => InstructionBuilder.allocateRun types.builder args.format before
    (createAccountAllocation types args)

theorem create_account_operational_reference :
    FamilyReference create_account_operational_contract create_account_operational_run := by
  intro _ _ _ _ _ execution
  exact execution

def transfer_operational_contract : Family where
  Index := OperationalTypes
  State := OperationalTypes.State
  Args := TransferOperationalArgs
  Value := fun types => InstructionBuilder.Value types.builder
  Unwind := OperationalTypes.Unwind
  Terminal := OperationalTypes.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args => InstructionBuilder.allocateRun types.builder args.format before
      (transferAllocation types args) }

def transfer_operational_run : FamilyRun transfer_operational_contract :=
  fun types before args => InstructionBuilder.allocateRun types.builder args.format before
    (transferAllocation types args)

theorem transfer_operational_reference :
    FamilyReference transfer_operational_contract transfer_operational_run := by
  intro _ _ _ _ _ execution
  exact execution

def create_account_operational_sample : create_account_operational_contract.Index :=
  ⟨InstructionBuilder.Sample.State, Nat, Nat, Nat, Nat, Nat⟩

def transfer_operational_sample : transfer_operational_contract.Index :=
  ⟨InstructionBuilder.Sample.State, Nat, Nat, Nat, Nat, Nat⟩

def createAccountSampleArgs : CreateAccountOperationalArgs create_account_operational_sample where
  source := ⟨.zero, .zero, 7, 32, _root_.Solanalib.Runtime.Pubkey.ofNat 9⟩
  format := .bincode
  providers := InstructionBuilder.Sample.providers SystemData SystemData.bytes

def transferSampleArgs : TransferOperationalArgs transfer_operational_sample where
  source := ⟨.zero, .zero, 7⟩
  format := .wincode
  providers := InstructionBuilder.Sample.providers SystemData SystemData.bytes

def createAccountSampleMiddle : InstructionBuilder.Sample.State :=
  InstructionBuilder.Sample.allocateMetas {} (createAccountAllocation _
    createAccountSampleArgs).accounts

def transferSampleMiddle : InstructionBuilder.Sample.State :=
  InstructionBuilder.Sample.allocateMetas {} (transferAllocation _ transferSampleArgs).accounts

def createAccountSampleAfter : InstructionBuilder.Sample.State :=
  InstructionBuilder.Sample.afterSerialize SystemData.bytes .bincode createAccountSampleMiddle
    (createAccountAllocation _ createAccountSampleArgs).data

def transferSampleAfter : InstructionBuilder.Sample.State :=
  InstructionBuilder.Sample.afterSerialize SystemData.bytes .wincode transferSampleMiddle
    (transferAllocation _ transferSampleArgs).data

theorem create_account_operational_satisfiable :
    FamilySatisfiable create_account_operational_contract create_account_operational_sample :=
  ⟨({} : InstructionBuilder.Sample.State), createAccountSampleArgs, trivial⟩

theorem transfer_operational_satisfiable :
    FamilySatisfiable transfer_operational_contract transfer_operational_sample :=
  ⟨({} : InstructionBuilder.Sample.State), transferSampleArgs, trivial⟩

theorem create_account_operational_has_execution :
    FamilyHasExecution create_account_operational_contract create_account_operational_run
      create_account_operational_sample := by
  refine ⟨({} : InstructionBuilder.Sample.State), createAccountSampleArgs,
    .returned ⟨.zero, (0 : Nat), (0 : Nat)⟩ createAccountSampleAfter, ?_, ?_⟩
  · trivial
  · apply InstructionBuilder.allocateRun_of_returned _ _ _ createAccountSampleMiddle _ (0 : Nat)
    · rfl
    · exact InstructionBuilder.run_of_serialized _ _ _ _ _ _ rfl

theorem transfer_operational_has_execution :
    FamilyHasExecution transfer_operational_contract transfer_operational_run
      transfer_operational_sample := by
  refine ⟨({} : InstructionBuilder.Sample.State), transferSampleArgs,
    .returned ⟨.zero, (0 : Nat), (0 : Nat)⟩ transferSampleAfter, ?_, ?_⟩
  · trivial
  · apply InstructionBuilder.allocateRun_of_returned _ _ _ transferSampleMiddle _ (0 : Nat)
    · rfl
    · exact InstructionBuilder.run_of_serialized _ _ _ _ _ _ rfl

end Solanalib.Specs.SolanaSystemInterface.instruction
