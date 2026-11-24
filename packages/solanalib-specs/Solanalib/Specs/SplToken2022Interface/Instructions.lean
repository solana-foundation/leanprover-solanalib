/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionAllocatedFamilyWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplToken2022Interface

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.Instruction

/-- The declared identity of the Token-2022 program. -/
def id_contract := valueContract (fun (_ : Unit) => True) (fun _ => token2022ProgramId)

/-- The declared Token-2022 program identity as a pure reference. -/
def id_reference := valueReference (fun (_ : Unit) => token2022ProgramId)

theorem id_reference_realizes : id_contract.RealizedBy id_reference :=
  valueReference_realizes _ _

theorem id_satisfiable : id_contract.Satisfiable := ⟨(), (), trivial⟩

/-- This source check accepts both programs. It does not assert that a supplied
program account has an executable flag or contains trusted program code. -/
def check_spl_token_program_account_contract :=
  valueContract (fun (_ : Solanalib.Runtime.Pubkey) => True) (checkProgram .either)

/-- The pure identity check accepts legacy Token and Token-2022 addresses. -/
def check_spl_token_program_account_reference := valueReference (checkProgram .either)

theorem check_spl_token_program_account_reference_realizes :
    check_spl_token_program_account_contract.RealizedBy
      check_spl_token_program_account_reference := valueReference_realizes _ _

theorem check_spl_token_program_account_satisfiable :
    check_spl_token_program_account_contract.Satisfiable := ⟨(), token2022ProgramId, trivial⟩

namespace instruction

/-- The initialization wire value accepts either program and serializes its
owner in data, leaving just the account and mint in metadata. -/
def initialize_account3_value_contract :=
  valueContract (fun (_ : InitializeAccount3Args) => True) (initializeAccount3 .either)

/-- Pure initialization admission, metadata and owner-byte observations. -/
def initialize_account3_value_reference := valueReference (initializeAccount3 .either)

theorem initialize_account3_value_reference_realizes :
    initialize_account3_value_contract.RealizedBy initialize_account3_value_reference :=
  valueReference_realizes _ _

theorem initialize_account3_value_satisfiable : initialize_account3_value_contract.Satisfiable :=
  ⟨(), ⟨token2022ProgramId, .zero, .zero, .zero⟩, trivial⟩

/-- Close-account admission and wire construction preserve signer order and
duplicates without asserting execution of the resulting instruction. -/
def close_account_value_contract :=
  valueContract (fun (_ : AuthorityArgs) => True) (closeAccount .either)

/-- Pure close-account admission, discriminator and authority metadata. -/
def close_account_value_reference := valueReference (closeAccount .either)

theorem close_account_value_reference_realizes :
    close_account_value_contract.RealizedBy close_account_value_reference :=
      valueReference_realizes _ _

theorem close_account_value_satisfiable : close_account_value_contract.Satisfiable :=
  ⟨(), ⟨token2022ProgramId, .zero, .zero, .zero, []⟩, trivial⟩

/-- The exact constructor result, including rejected program IDs. There is no
assertion here that executing the resulting transfer succeeds. -/
def transfer_checked_value_contract :=
  valueContract (fun (_ : TransferCheckedArgs) => True) (transferChecked .either)

/-- Pure checked-transfer bytes and metadata for either admitted program. -/
def transfer_checked_value_reference := valueReference (transferChecked .either)

theorem transfer_checked_value_reference_realizes :
    transfer_checked_value_contract.RealizedBy transfer_checked_value_reference :=
  valueReference_realizes _ _

theorem transfer_checked_value_satisfiable : transfer_checked_value_contract.Satisfiable :=
  ⟨(), ⟨⟨⟨token2022ProgramId, .zero, .zero, .zero, []⟩, 0⟩, .zero, 0⟩, trivial⟩

/-- Unlike the other selected constructors, this instruction rejects the
legacy Token program ID. -/
def withdraw_excess_lamports_value_contract :=
  valueContract (fun (_ : AuthorityArgs) => True) withdrawExcessLamports

/-- Pure Token-2022-only withdrawal admission and ordered authority metadata. -/
def withdraw_excess_lamports_value_reference := valueReference withdrawExcessLamports

theorem withdraw_excess_lamports_value_reference_realizes :
    withdraw_excess_lamports_value_contract.RealizedBy withdraw_excess_lamports_value_reference :=
  valueReference_realizes _ _

theorem withdraw_excess_lamports_value_satisfiable :
  withdraw_excess_lamports_value_contract.Satisfiable :=
  ⟨(), ⟨token2022ProgramId, .zero, .zero, .zero, []⟩, trivial⟩

/-- The complete local allocation and cleanup sequence of the constructor, with
explicit vector providers and actual capacity arguments. A successful return
moves both actual resource handles into the instruction. -/
def initialize_account3_contract : Family :=
  InstructionAllocated.family InitializeAccount3Args (InstructionAllocated.initializeAccount3Plan
    .either)

/-- Initialization executes byte allocation, owner serialization and the
metadata literal through the selected primitive providers. -/
def initialize_account3_reference : FamilyRun initialize_account3_contract :=
  InstructionAllocated.reference InitializeAccount3Args
    (InstructionAllocated.initializeAccount3Plan .either)

theorem initialize_account3_reference_holds :
    FamilyReference initialize_account3_contract initialize_account3_reference :=
  InstructionAllocated.reference_holds _ _

/-- A mathematical ledger instantiation; it does not assert a Rust layout or
allocator guarantee. -/
def initialize_account3_sample : initialize_account3_contract.Index :=
  InstructionAllocated.Witness.sampleTypes

/-- A successful allocation, packing and metadata execution with both vectors
still owned by the returned instruction. -/
theorem initialize_account3_has_execution :
    FamilyHasExecution initialize_account3_contract initialize_account3_reference
      initialize_account3_sample :=
  InstructionAllocated.Witness.family_hasExecution
    (InstructionAllocated.initializeAccount3Plan .either)
      InstructionAllocated.Witness.tokenInitialize rfl

theorem initialize_account3_satisfiable :
    FamilySatisfiable initialize_account3_contract initialize_account3_sample :=
  initialize_account3_has_execution.satisfiable

/-- The complete local allocation and cleanup sequence of the constructor, with
explicit vector providers and actual capacity arguments. A successful return
moves both actual resource handles into the instruction. -/
def close_account_contract : Family :=
  InstructionAllocated.family AuthorityArgs (InstructionAllocated.closeAccountPlan .either)

/-- Close-account construction executes byte and ordered metadata operations,
with actual ownership transfer and exceptional cleanup. -/
def close_account_reference : FamilyRun close_account_contract :=
  InstructionAllocated.reference AuthorityArgs (InstructionAllocated.closeAccountPlan .either)

theorem close_account_reference_holds :
    FamilyReference close_account_contract close_account_reference :=
  InstructionAllocated.reference_holds _ _

/-- A mathematical ledger instantiation; it does not assert a Rust layout or
allocator guarantee. -/
def close_account_sample : close_account_contract.Index :=
  InstructionAllocated.Witness.sampleTypes

/-- A successful allocation, packing and metadata execution with both vectors
still owned by the returned instruction. -/
theorem close_account_has_execution :
    FamilyHasExecution close_account_contract close_account_reference
      close_account_sample :=
  InstructionAllocated.Witness.family_hasExecution
    (InstructionAllocated.closeAccountPlan .either) InstructionAllocated.Witness.tokenAuthority rfl

theorem close_account_satisfiable :
    FamilySatisfiable close_account_contract close_account_sample :=
  close_account_has_execution.satisfiable

/-- The complete local allocation and cleanup sequence of the constructor, with
explicit vector providers and actual capacity arguments. A successful return
moves both actual resource handles into the instruction. -/
def transfer_checked_contract : Family :=
  InstructionAllocated.family TransferCheckedArgs (InstructionAllocated.transferCheckedPlan .either)

/-- Checked transfer executes the amount extension, separate decimals push
and ordered metadata construction through the selected primitive providers. -/
def transfer_checked_reference : FamilyRun transfer_checked_contract :=
  InstructionAllocated.reference TransferCheckedArgs (InstructionAllocated.transferCheckedPlan
    .either)

theorem transfer_checked_reference_holds :
    FamilyReference transfer_checked_contract transfer_checked_reference :=
  InstructionAllocated.reference_holds _ _

/-- A mathematical ledger instantiation; it does not assert a Rust layout or
allocator guarantee. -/
def transfer_checked_sample : transfer_checked_contract.Index :=
  InstructionAllocated.Witness.sampleTypes

/-- A successful allocation, packing and metadata execution with both vectors
still owned by the returned instruction. -/
theorem transfer_checked_has_execution :
    FamilyHasExecution transfer_checked_contract transfer_checked_reference
      transfer_checked_sample :=
  InstructionAllocated.Witness.family_hasExecution
    (InstructionAllocated.transferCheckedPlan .either) InstructionAllocated.Witness.tokenChecked rfl

theorem transfer_checked_satisfiable :
    FamilySatisfiable transfer_checked_contract transfer_checked_sample :=
  transfer_checked_has_execution.satisfiable

/-- The complete local allocation and cleanup sequence of the constructor, with
explicit vector providers and actual capacity arguments. A successful return
moves both actual resource handles into the instruction. -/
def withdraw_excess_lamports_contract : Family :=
  InstructionAllocated.family AuthorityArgs InstructionAllocated.withdrawExcessLamportsPlan

/-- Withdrawal rejects the legacy program before any allocation, constructs
the three-entry metadata literal, pushes signers, then packs tag38 while
retaining the completed metadata owner across packing cleanup. -/
def withdraw_excess_lamports_reference : FamilyRun withdraw_excess_lamports_contract :=
  InstructionAllocated.reference AuthorityArgs InstructionAllocated.withdrawExcessLamportsPlan

theorem withdraw_excess_lamports_reference_holds :
    FamilyReference withdraw_excess_lamports_contract withdraw_excess_lamports_reference :=
  InstructionAllocated.reference_holds _ _

/-- A mathematical ledger instantiation; it does not assert a Rust layout or
allocator guarantee. -/
def withdraw_excess_lamports_sample : withdraw_excess_lamports_contract.Index :=
  InstructionAllocated.Witness.sampleTypes

/-- A successful allocation, packing and metadata execution with both vectors
still owned by the returned instruction. -/
theorem withdraw_excess_lamports_has_execution :
    FamilyHasExecution withdraw_excess_lamports_contract withdraw_excess_lamports_reference
      withdraw_excess_lamports_sample :=
  InstructionAllocated.Witness.family_hasExecution
    InstructionAllocated.withdrawExcessLamportsPlan InstructionAllocated.Witness.tokenAuthority rfl

theorem withdraw_excess_lamports_satisfiable :
    FamilySatisfiable withdraw_excess_lamports_contract withdraw_excess_lamports_sample :=
  withdraw_excess_lamports_has_execution.satisfiable

end instruction
end Solanalib.Specs.SplToken2022Interface
