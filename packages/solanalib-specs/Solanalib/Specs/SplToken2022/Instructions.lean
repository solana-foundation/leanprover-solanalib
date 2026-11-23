/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestOnchainContract
public import Solanalib.Specs.Core.TokenRequestAllocatedWitness
public import Solanalib.Specs.Core.TokenInstructionAdditionalPlans
public import Solanalib.Specs.Core.TokenInstructionAllocatedFamilyWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplToken2022.onchain

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token.Onchain

/-- Supporting value-level preparation. This observation omits allocation and
Rc effects; the primary contract below includes their operational exits. -/
def invoke_transfer_checked_value_contract : Family := invokeTransferCheckedFamily

/-- The supporting checked-transfer value reference. -/
def invoke_transfer_checked_value_reference : FamilyRun invoke_transfer_checked_value_contract :=
  invokeTransferCheckedRun

theorem invoke_transfer_checked_value_reference_holds :
    FamilyReference invoke_transfer_checked_value_contract invoke_transfer_checked_value_reference
      :=
  invokeTransferCheckedReference

/-- Closed sample for the supporting value observation. -/
def invoke_transfer_checked_value_sample : invoke_transfer_checked_value_contract.Index :=
  sampleTypes

theorem invoke_transfer_checked_value_satisfiable :
    FamilySatisfiable invoke_transfer_checked_value_contract invoke_transfer_checked_value_sample :=
  invokeTransferCheckedSatisfiable

theorem invoke_transfer_checked_value_has_execution :
    FamilyHasExecution invoke_transfer_checked_value_contract
      invoke_transfer_checked_value_reference
      invoke_transfer_checked_value_sample :=
  invokeTransferCheckedHasExecution

/-- Full ordinary local preparation for the selected fee=None entry point,
including vector operations, multisig selection, hook resolution, live shared
borrows, Rc moves and cleanup. The final invocation remains opaque. -/
def invoke_transfer_checked_contract : Family := Token.OnchainAllocated.family

/-- The source-ordered operational reference for every dependency interpretation. -/
def invoke_transfer_checked_reference : FamilyRun invoke_transfer_checked_contract :=
  Token.OnchainAllocated.reference

theorem invoke_transfer_checked_reference_holds :
    FamilyReference invoke_transfer_checked_contract invoke_transfer_checked_reference :=
  Token.OnchainAllocated.reference_holds

/-- A closed initialized-mint execution with actual vector ledgers, Rc counts
and a successful opaque invocation. It does not assert production allocation. -/
def invoke_transfer_checked_sample : invoke_transfer_checked_contract.Index :=
  Token.OnchainAllocated.Witness.sample

theorem invoke_transfer_checked_has_execution :
    FamilyHasExecution invoke_transfer_checked_contract invoke_transfer_checked_reference
      invoke_transfer_checked_sample :=
  Token.OnchainAllocated.Witness.has_execution

theorem invoke_transfer_checked_satisfiable :
    FamilySatisfiable invoke_transfer_checked_contract invoke_transfer_checked_sample :=
  invoke_transfer_checked_has_execution.satisfiable

end Solanalib.Specs.SplToken2022.onchain

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SplToken2022.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Instruction
open Solanalib.Specs.Core.Token.InstructionAllocated

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def initialize_mint_close_authority_contract : Family := family (InitializeMintCloseAuthorityArgs)
  (initializeMintCloseAuthorityPlan)

/-- Operational reference at the selected complete dependency interpretation. -/
def initialize_mint_close_authority_reference : FamilyRun initialize_mint_close_authority_contract
  := reference (InitializeMintCloseAuthorityArgs) (initializeMintCloseAuthorityPlan)

/-- The reference follows the same local dependency sequence for every index. -/
theorem initialize_mint_close_authority_reference_holds :
    FamilyReference initialize_mint_close_authority_contract
      initialize_mint_close_authority_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def initialize_mint_close_authority_sample : initialize_mint_close_authority_contract.Index :=
  Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem initialize_mint_close_authority_has_execution :
    FamilyHasExecution initialize_mint_close_authority_contract
      initialize_mint_close_authority_reference initialize_mint_close_authority_sample :=
  Witness.family_hasExecution (initializeMintCloseAuthorityPlan) (⟨⟨token2022ProgramId, .ofNat 1⟩,
    some .zero⟩ : InitializeMintCloseAuthorityArgs) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem initialize_mint_close_authority_satisfiable : FamilySatisfiable
  initialize_mint_close_authority_contract initialize_mint_close_authority_sample :=
  initialize_mint_close_authority_has_execution.satisfiable

end Solanalib.Specs.SplToken2022.instruction

namespace Solanalib.Specs.SplToken2022.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Instruction
open Solanalib.Specs.Core.Token.InstructionAllocated

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def burn_checked_contract : Family := family (AmountDecimalsArgs) (burnCheckedPlan .either)

/-- Operational reference at the selected complete dependency interpretation. -/
def burn_checked_reference : FamilyRun burn_checked_contract := reference (AmountDecimalsArgs)
  (burnCheckedPlan .either)

/-- The reference follows the same local dependency sequence for every index. -/
theorem burn_checked_reference_holds :
    FamilyReference burn_checked_contract burn_checked_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def burn_checked_sample : burn_checked_contract.Index := Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem burn_checked_has_execution :
    FamilyHasExecution burn_checked_contract burn_checked_reference burn_checked_sample :=
  Witness.family_hasExecution (burnCheckedPlan .either)
    (⟨⟨InstructionAllocated.Witness.tokenAuthority, 513⟩, 255⟩ : AmountDecimalsArgs) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem burn_checked_satisfiable : FamilySatisfiable burn_checked_contract burn_checked_sample :=
  burn_checked_has_execution.satisfiable

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def freeze_account_contract : Family := family (AuthorityArgs) (freezeAccountPlan .either)

/-- Operational reference at the selected complete dependency interpretation. -/
def freeze_account_reference : FamilyRun freeze_account_contract := reference (AuthorityArgs)
  (freezeAccountPlan .either)

/-- The reference follows the same local dependency sequence for every index. -/
theorem freeze_account_reference_holds :
    FamilyReference freeze_account_contract freeze_account_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def freeze_account_sample : freeze_account_contract.Index := Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem freeze_account_has_execution :
    FamilyHasExecution freeze_account_contract freeze_account_reference freeze_account_sample :=
  Witness.family_hasExecution (freezeAccountPlan .either)
    (InstructionAllocated.Witness.tokenAuthority : AuthorityArgs) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem freeze_account_satisfiable : FamilySatisfiable freeze_account_contract
  freeze_account_sample :=
  freeze_account_has_execution.satisfiable

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def thaw_account_contract : Family := family (AuthorityArgs) (thawAccountPlan .either)

/-- Operational reference at the selected complete dependency interpretation. -/
def thaw_account_reference : FamilyRun thaw_account_contract := reference (AuthorityArgs)
  (thawAccountPlan .either)

/-- The reference follows the same local dependency sequence for every index. -/
theorem thaw_account_reference_holds :
    FamilyReference thaw_account_contract thaw_account_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def thaw_account_sample : thaw_account_contract.Index := Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem thaw_account_has_execution :
    FamilyHasExecution thaw_account_contract thaw_account_reference thaw_account_sample :=
  Witness.family_hasExecution (thawAccountPlan .either)
    (InstructionAllocated.Witness.tokenAuthority : AuthorityArgs) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem thaw_account_satisfiable : FamilySatisfiable thaw_account_contract thaw_account_sample :=
  thaw_account_has_execution.satisfiable

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def mint_to_contract : Family := family (TransferArgs) (mintToPlan .either)

/-- Operational reference at the selected complete dependency interpretation. -/
def mint_to_reference : FamilyRun mint_to_contract := reference (TransferArgs) (mintToPlan .either)

/-- The reference follows the same local dependency sequence for every index. -/
theorem mint_to_reference_holds :
    FamilyReference mint_to_contract mint_to_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def mint_to_sample : mint_to_contract.Index := Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem mint_to_has_execution :
    FamilyHasExecution mint_to_contract mint_to_reference mint_to_sample :=
  Witness.family_hasExecution (mintToPlan .either) (⟨InstructionAllocated.Witness.tokenAuthority,
    513⟩ : TransferArgs) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem mint_to_satisfiable : FamilySatisfiable mint_to_contract mint_to_sample :=
  mint_to_has_execution.satisfiable

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def set_authority_contract : Family := family (SetAuthorityArgs 17) (setAuthorityPlan .either)

/-- Operational reference at the selected complete dependency interpretation. -/
def set_authority_reference : FamilyRun set_authority_contract := reference (SetAuthorityArgs 17)
  (setAuthorityPlan .either)

/-- The reference follows the same local dependency sequence for every index. -/
theorem set_authority_reference_holds :
    FamilyReference set_authority_contract set_authority_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def set_authority_sample : set_authority_contract.Index := Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem set_authority_has_execution :
    FamilyHasExecution set_authority_contract set_authority_reference set_authority_sample :=
  Witness.family_hasExecution (setAuthorityPlan .either) (⟨token2022ProgramId, .ofNat 1, some
    .zero, ⟨16, by decide⟩, .ofNat 2, [.ofNat 3, .ofNat 3]⟩ : SetAuthorityArgs 17) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem set_authority_satisfiable : FamilySatisfiable set_authority_contract set_authority_sample :=
  set_authority_has_execution.satisfiable

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def initialize_mint2_contract : Family := family (InitializeMint2Args) (initializeMint2Plan .either)

/-- Operational reference at the selected complete dependency interpretation. -/
def initialize_mint2_reference : FamilyRun initialize_mint2_contract := reference
  (InitializeMint2Args) (initializeMint2Plan .either)

/-- The reference follows the same local dependency sequence for every index. -/
theorem initialize_mint2_reference_holds :
    FamilyReference initialize_mint2_contract initialize_mint2_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def initialize_mint2_sample : initialize_mint2_contract.Index := Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem initialize_mint2_has_execution :
    FamilyHasExecution initialize_mint2_contract initialize_mint2_reference initialize_mint2_sample
      :=
  Witness.family_hasExecution (initializeMint2Plan .either) (⟨token2022ProgramId, .ofNat 1, 255,
    .ofNat 2, some .zero⟩ : InitializeMint2Args) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem initialize_mint2_satisfiable : FamilySatisfiable initialize_mint2_contract
  initialize_mint2_sample :=
  initialize_mint2_has_execution.satisfiable

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def initialize_immutable_owner_contract : Family := family (SingleAccountArgs)
  (initializeImmutableOwnerPlan .either)

/-- Operational reference at the selected complete dependency interpretation. -/
def initialize_immutable_owner_reference : FamilyRun initialize_immutable_owner_contract :=
  reference (SingleAccountArgs) (initializeImmutableOwnerPlan .either)

/-- The reference follows the same local dependency sequence for every index. -/
theorem initialize_immutable_owner_reference_holds :
    FamilyReference initialize_immutable_owner_contract initialize_immutable_owner_reference :=
      reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def initialize_immutable_owner_sample : initialize_immutable_owner_contract.Index :=
  Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem initialize_immutable_owner_has_execution :
    FamilyHasExecution initialize_immutable_owner_contract initialize_immutable_owner_reference
      initialize_immutable_owner_sample :=
  Witness.family_hasExecution (initializeImmutableOwnerPlan .either) (⟨legacyProgramId, .ofNat 1⟩ :
    SingleAccountArgs) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem initialize_immutable_owner_satisfiable : FamilySatisfiable
  initialize_immutable_owner_contract initialize_immutable_owner_sample :=
  initialize_immutable_owner_has_execution.satisfiable

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def initialize_non_transferable_mint_contract : Family := family (SingleAccountArgs)
  (initializeNonTransferableMintPlan)

/-- Operational reference at the selected complete dependency interpretation. -/
def initialize_non_transferable_mint_reference : FamilyRun
  initialize_non_transferable_mint_contract := reference (SingleAccountArgs)
  (initializeNonTransferableMintPlan)

/-- The reference follows the same local dependency sequence for every index. -/
theorem initialize_non_transferable_mint_reference_holds :
    FamilyReference initialize_non_transferable_mint_contract
      initialize_non_transferable_mint_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def initialize_non_transferable_mint_sample : initialize_non_transferable_mint_contract.Index :=
  Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem initialize_non_transferable_mint_has_execution :
    FamilyHasExecution initialize_non_transferable_mint_contract
      initialize_non_transferable_mint_reference initialize_non_transferable_mint_sample :=
  Witness.family_hasExecution (initializeNonTransferableMintPlan) (⟨token2022ProgramId, .ofNat 1⟩ :
    SingleAccountArgs) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem initialize_non_transferable_mint_satisfiable : FamilySatisfiable
  initialize_non_transferable_mint_contract initialize_non_transferable_mint_sample :=
  initialize_non_transferable_mint_has_execution.satisfiable

end Solanalib.Specs.SplToken2022.instruction

namespace Solanalib.Specs.SplToken2022.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Instruction

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

end Solanalib.Specs.SplToken2022.instruction

namespace Solanalib.Specs.SplToken2022.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Instruction

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

end Solanalib.Specs.SplToken2022.instruction

namespace Solanalib.Specs.SplToken2022.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Instruction

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

end Solanalib.Specs.SplToken2022.instruction
