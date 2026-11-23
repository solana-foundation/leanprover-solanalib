/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionAdditionalPlans
public import Solanalib.Specs.Core.TokenInstructionAllocatedFamilyWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplToken.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Instruction
open Solanalib.Specs.Core.Token.InstructionAllocated

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def burn_checked_contract : Family := family (AmountDecimalsArgs) (burnCheckedPlan .legacy)

/-- Operational reference at the selected complete dependency interpretation. -/
def burn_checked_reference : FamilyRun burn_checked_contract := reference (AmountDecimalsArgs)
  (burnCheckedPlan .legacy)

/-- The reference follows the same local dependency sequence for every index. -/
theorem burn_checked_reference_holds :
    FamilyReference burn_checked_contract burn_checked_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def burn_checked_sample : burn_checked_contract.Index := Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem burn_checked_has_execution :
    FamilyHasExecution burn_checked_contract burn_checked_reference burn_checked_sample :=
  Witness.family_hasExecution (burnCheckedPlan .legacy) (⟨⟨⟨legacyProgramId, .ofNat 1, .ofNat 2,
    .ofNat 3, [.ofNat 4, .ofNat 4]⟩, 513⟩, 255⟩ : AmountDecimalsArgs) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem burn_checked_satisfiable : FamilySatisfiable burn_checked_contract burn_checked_sample :=
  burn_checked_has_execution.satisfiable

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def close_account_contract : Family := family (AuthorityArgs) (closeAccountPlan .legacy)

/-- Operational reference at the selected complete dependency interpretation. -/
def close_account_reference : FamilyRun close_account_contract := reference (AuthorityArgs)
  (closeAccountPlan .legacy)

/-- The reference follows the same local dependency sequence for every index. -/
theorem close_account_reference_holds :
    FamilyReference close_account_contract close_account_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def close_account_sample : close_account_contract.Index := Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem close_account_has_execution :
    FamilyHasExecution close_account_contract close_account_reference close_account_sample :=
  Witness.family_hasExecution (closeAccountPlan .legacy) (⟨legacyProgramId, .ofNat 1, .ofNat 2,
    .ofNat 3, []⟩ : AuthorityArgs) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem close_account_satisfiable : FamilySatisfiable close_account_contract close_account_sample :=
  close_account_has_execution.satisfiable

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def mint_to_contract : Family := family (TransferArgs) (mintToPlan .legacy)

/-- Operational reference at the selected complete dependency interpretation. -/
def mint_to_reference : FamilyRun mint_to_contract := reference (TransferArgs) (mintToPlan .legacy)

/-- The reference follows the same local dependency sequence for every index. -/
theorem mint_to_reference_holds :
    FamilyReference mint_to_contract mint_to_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def mint_to_sample : mint_to_contract.Index := Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem mint_to_has_execution :
    FamilyHasExecution mint_to_contract mint_to_reference mint_to_sample :=
  Witness.family_hasExecution (mintToPlan .legacy) (InstructionAllocated.Witness.legacyTransfer :
    TransferArgs) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem mint_to_satisfiable : FamilySatisfiable mint_to_contract mint_to_sample :=
  mint_to_has_execution.satisfiable

/-- Exact source packing, ordered metadata allocation and cleanup through
explicit vector providers. Every actual provider state and finite exit is retained. -/
def set_authority_contract : Family := family (SetAuthorityArgs 4) (setAuthorityPlan .legacy)

/-- Operational reference at the selected complete dependency interpretation. -/
def set_authority_reference : FamilyRun set_authority_contract := reference (SetAuthorityArgs 4)
  (setAuthorityPlan .legacy)

/-- The reference follows the same local dependency sequence for every index. -/
theorem set_authority_reference_holds :
    FamilyReference set_authority_contract set_authority_reference := reference_holds _ _

/-- Closed two-ledger witness; its layout constants are mathematical sample inputs. -/
def set_authority_sample : set_authority_contract.Index := Witness.sampleTypes

/-- A complete successful construction, including each byte and metadata operation. -/
theorem set_authority_has_execution :
    FamilyHasExecution set_authority_contract set_authority_reference set_authority_sample :=
  Witness.family_hasExecution (setAuthorityPlan .legacy) (⟨legacyProgramId, .ofNat 1, some .zero,
    ⟨3, by decide⟩, .ofNat 2, [.ofNat 3, .ofNat 3]⟩ : SetAuthorityArgs 4) rfl

/-- The witnessed input is admitted without a callback termination premise. -/
theorem set_authority_satisfiable : FamilySatisfiable set_authority_contract set_authority_sample :=
  set_authority_has_execution.satisfiable

end Solanalib.Specs.SplToken.instruction
