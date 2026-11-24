/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TransferHookResolutionFacts
public import Solanalib.Specs.Core.TransferHookResolutionErrors
public import Solanalib.Specs.Core.TransferHookResolutionWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplTransferHookInterface.onchain

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Exact local account preparation, with source-ordered allocation, TLV and
seed resolution, privilege reduction, Rc aliases and finite cleanup exits.
This helper does not invoke a CPI. Source realization remains an assumption. -/
def add_extra_accounts_for_execute_cpi_contract : Family := TransferHookResolution.family

def add_extra_accounts_for_execute_cpi_reference :
    FamilyRun add_extra_accounts_for_execute_cpi_contract := TransferHookResolution.reference

theorem add_extra_accounts_for_execute_cpi_reference_holds :
    FamilyReference add_extra_accounts_for_execute_cpi_contract
      add_extra_accounts_for_execute_cpi_reference := TransferHookResolution.reference_correct

def add_extra_accounts_for_execute_cpi_sample :
    add_extra_accounts_for_execute_cpi_contract.Index := TransferHookResolution.Sample.sampleTypes

theorem add_extra_accounts_for_execute_cpi_has_execution :
    FamilyHasExecution add_extra_accounts_for_execute_cpi_contract
      add_extra_accounts_for_execute_cpi_reference add_extra_accounts_for_execute_cpi_sample :=
  TransferHookResolution.Sample.has_execution

theorem add_extra_accounts_for_execute_cpi_satisfiable :
    FamilySatisfiable add_extra_accounts_for_execute_cpi_contract
      add_extra_accounts_for_execute_cpi_sample := TransferHookResolution.Sample.satisfiable

end Solanalib.Specs.SplTransferHookInterface.onchain
