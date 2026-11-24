/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorContextOperations

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Context fields move unchanged. The `AccountInfoProgram` families retain
generic `NewTypes`/`CpiTypes` carriers, including `Program : Type`. Exact source
profiles and Entries supply an owned AccountInfo or a copied Pubkey as required
by the selected call. The separate context family keeps its own complete
resource contract and catalog member. -/

namespace Solanalib.Specs.AnchorLang.context

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorContextOperations

namespace Context

/-- Move the bump payload and preserve all three borrowed references; no account trait callback is
reached. -/
def new_contract : Family := contextNewFamily
def new_run : FamilyRun new_contract := contextNewRun
def new_sample : new_contract.Index := contextSample
theorem new_reference : FamilyReference new_contract new_run :=
  contextNew_reference
theorem new_has_execution :
    FamilyHasExecution new_contract new_run new_sample :=
  contextNew_execution
theorem new_satisfiable : FamilySatisfiable new_contract new_sample :=
  new_has_execution.satisfiable

end Context

namespace CpiContext.AccountInfoProgram

/-- Move the actual accounts and program representation, create a fresh empty remaining vector, and
use the empty borrowed signer descriptor. -/
def new_contract : Family := newFamily
def new_run : FamilyRun new_contract := newRun
def new_sample : new_contract.Index := cpiSample
theorem new_reference : FamilyReference new_contract new_run :=
  AnchorContextOperations.new_reference
theorem new_has_execution :
    FamilyHasExecution new_contract new_run new_sample :=
  new_execution
theorem new_satisfiable : FamilySatisfiable new_contract new_sample :=
  new_has_execution.satisfiable

end CpiContext.AccountInfoProgram

namespace CpiContext.AccountInfoProgram

/-- Replace only the borrowed signer descriptor; the moved accounts, program and remaining vector
retain their identities. -/
def with_signer_contract : Family := withSignerFamily
def with_signer_run : FamilyRun with_signer_contract := withSignerRun
def with_signer_sample : with_signer_contract.Index := cpiSample.toCpiTypes
theorem with_signer_reference : FamilyReference with_signer_contract with_signer_run :=
  withSigner_reference
theorem with_signer_has_execution :
    FamilyHasExecution with_signer_contract with_signer_run with_signer_sample :=
  withSigner_execution
theorem with_signer_satisfiable : FamilySatisfiable with_signer_contract with_signer_sample :=
  with_signer_has_execution.satisfiable

end CpiContext.AccountInfoProgram


namespace CpiContext.AccountInfoProgram

/-- The older constructor moves an owned AccountInfo program and accounts, retains the borrowed
signers, and obtains one fresh empty remaining-vector owner. -/
def new_with_signer_contract : Family := newWithSignerFamily
def new_with_signer_run : FamilyRun new_with_signer_contract := newWithSignerRun
def new_with_signer_sample : new_with_signer_contract.Index := cpiSample
theorem new_with_signer_reference : FamilyReference new_with_signer_contract new_with_signer_run :=
  newWithSigner_reference
theorem new_with_signer_has_execution :
    FamilyHasExecution new_with_signer_contract new_with_signer_run new_with_signer_sample :=
  newWithSigner_execution
theorem new_with_signer_satisfiable : FamilySatisfiable new_with_signer_contract
  new_with_signer_sample :=
  new_with_signer_has_execution.satisfiable

end CpiContext.AccountInfoProgram

end Solanalib.Specs.AnchorLang.context

namespace Solanalib.Specs.AnchorLang.context

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorContextOperations

namespace CpiContext

/-- Destroy the previous remaining vector at the current state before installing the moved
replacement vector. -/
def with_remaining_accounts_contract : Family := withRemainingFamily
def with_remaining_accounts_run : FamilyRun with_remaining_accounts_contract := withRemainingRun
def with_remaining_accounts_sample : with_remaining_accounts_contract.Index := remainingSample
theorem with_remaining_accounts_reference : FamilyReference with_remaining_accounts_contract
  with_remaining_accounts_run :=
  withRemaining_reference
theorem with_remaining_accounts_has_execution :
    FamilyHasExecution with_remaining_accounts_contract with_remaining_accounts_run
      with_remaining_accounts_sample :=
  withRemaining_execution
theorem with_remaining_accounts_satisfiable : FamilySatisfiable with_remaining_accounts_contract
  with_remaining_accounts_sample :=
  with_remaining_accounts_has_execution.satisfiable

end CpiContext


end Solanalib.Specs.AnchorLang.context
