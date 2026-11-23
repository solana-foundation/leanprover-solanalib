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

namespace Solanalib.Specs.SplTokenInterface

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.Instruction

/-- The declared identity of the legacy Token program. -/
def id_contract := valueContract (fun (_ : Unit) => True) (fun _ => legacyProgramId)

/-- The declared legacy Token program identity as a pure reference. -/
def id_reference := valueReference (fun (_ : Unit) => legacyProgramId)

theorem id_reference_realizes : id_contract.RealizedBy id_reference :=
  valueReference_realizes _ _

theorem id_satisfiable : id_contract.Satisfiable := ⟨(), (), trivial⟩

namespace instruction

/-- `initialize_account3` accepts the legacy program ID only; the owner is
serialized into the instruction data and is absent from its account list. -/
def initialize_account3_value_contract :=
  valueContract (fun (_ : InitializeAccount3Args) => True) (initializeAccount3 .legacy)

/-- Pure initialization admission, metadata and owner-byte observations. -/
def initialize_account3_value_reference := valueReference (initializeAccount3 .legacy)

theorem initialize_account3_value_reference_realizes :
    initialize_account3_value_contract.RealizedBy initialize_account3_value_reference :=
  valueReference_realizes _ _

theorem initialize_account3_value_satisfiable : initialize_account3_value_contract.Satisfiable :=
  ⟨(), ⟨legacyProgramId, .zero, .zero, .zero⟩, trivial⟩

/-- `transfer` retains signer multiplicity and order. Its constructor performs
no balance, account ownership or signature validation. -/
def transfer_value_contract := valueContract (fun (_ : TransferArgs) => True) transfer

/-- Pure legacy transfer admission, wire bytes and ordered signer metadata. -/
def transfer_value_reference := valueReference transfer

theorem transfer_value_reference_realizes : transfer_value_contract.RealizedBy
  transfer_value_reference :=
  valueReference_realizes _ _

theorem transfer_value_satisfiable : transfer_value_contract.Satisfiable :=
  ⟨(), ⟨⟨legacyProgramId, .zero, .zero, .zero, []⟩, 0⟩, trivial⟩

/-- The complete local allocation and cleanup sequence of the constructor, with
explicit vector providers and actual capacity arguments. A successful return
moves both actual resource handles into the instruction. -/
def initialize_account3_contract : Family :=
  InstructionAllocated.family InitializeAccount3Args (InstructionAllocated.initializeAccount3Plan
    .legacy)

/-- Initialization executes the source byte allocation and metadata literal
through the selected primitive providers, retaining their exceptional exits. -/
def initialize_account3_reference : FamilyRun initialize_account3_contract :=
  InstructionAllocated.reference InitializeAccount3Args
    (InstructionAllocated.initializeAccount3Plan .legacy)

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
    (InstructionAllocated.initializeAccount3Plan .legacy)
      InstructionAllocated.Witness.legacyInitialize rfl

theorem initialize_account3_satisfiable :
    FamilySatisfiable initialize_account3_contract initialize_account3_sample :=
  initialize_account3_has_execution.satisfiable

/-- The complete local allocation and cleanup sequence of the constructor, with
explicit vector providers and actual capacity arguments. A successful return
moves both actual resource handles into the instruction. -/
def transfer_contract : Family :=
  InstructionAllocated.family TransferArgs InstructionAllocated.transferPlan

/-- Transfer executes ordered byte and metadata operations with ownership
transfer on success and the selected cleanup behavior on exceptional exits. -/
def transfer_reference : FamilyRun transfer_contract :=
  InstructionAllocated.reference TransferArgs InstructionAllocated.transferPlan

theorem transfer_reference_holds :
    FamilyReference transfer_contract transfer_reference :=
  InstructionAllocated.reference_holds _ _

/-- A mathematical ledger instantiation; it does not assert a Rust layout or
allocator guarantee. -/
def transfer_sample : transfer_contract.Index :=
  InstructionAllocated.Witness.sampleTypes

/-- A successful allocation, packing and metadata execution with both vectors
still owned by the returned instruction. -/
theorem transfer_has_execution :
    FamilyHasExecution transfer_contract transfer_reference
      transfer_sample :=
  InstructionAllocated.Witness.family_hasExecution
    InstructionAllocated.transferPlan InstructionAllocated.Witness.legacyTransfer rfl

theorem transfer_satisfiable :
    FamilySatisfiable transfer_contract transfer_sample :=
  transfer_has_execution.satisfiable

end instruction
end Solanalib.Specs.SplTokenInterface
