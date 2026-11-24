/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressDerived

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaLoaderV3Interface

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Operations

/-! Prepare the exact seed boundaries/order and fixed program ID, invoke the
resolved PDA search, and discard only the returned bump. -/

def get_program_data_address_contract : Family := uninitDerivedFamily Value loaderInputs
def get_program_data_address_run : FamilyRun get_program_data_address_contract :=
  uninitDerivedReference Value loaderInputs
def get_program_data_address_sample : get_program_data_address_contract.Index := uninitFindSample

theorem get_program_data_address_reference : FamilyReference get_program_data_address_contract
  get_program_data_address_run :=
  uninitDerivedReference_correct Value loaderInputs

theorem get_program_data_address_has_execution :
    FamilyHasExecution get_program_data_address_contract get_program_data_address_run
      get_program_data_address_sample :=
  uninitDerivedSample_execution Value loaderInputs (_root_.Solanalib.Runtime.Pubkey.zero)

theorem get_program_data_address_satisfiable :
    FamilySatisfiable get_program_data_address_contract get_program_data_address_sample :=
  get_program_data_address_has_execution.satisfiable

end Solanalib.Specs.SolanaLoaderV3Interface
