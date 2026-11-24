/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressOperations
public import Solanalib.Specs.SolanaAddress.Address.Cmp

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaAddress.Address

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Operations

/-! The selected solana-address 2.6.1 Solana create wrapper.
The complete create family retains the initialized-output premise and the
actual status conversion and panic provider. -/

def create_program_address_solana_contract : Family := createFamily .uninitialized .address
def create_program_address_solana_run : FamilyRun create_program_address_solana_contract :=
  createReference .uninitialized .address
def create_program_address_solana_sample : create_program_address_solana_contract.Index :=
  createSample .uninitialized

theorem create_program_address_solana_reference : FamilyReference
  create_program_address_solana_contract create_program_address_solana_run :=
  createReference_correct .uninitialized .address

theorem create_program_address_solana_has_execution :
    FamilyHasExecution create_program_address_solana_contract create_program_address_solana_run
      create_program_address_solana_sample :=
  createSample_execution .uninitialized .address

theorem create_program_address_solana_satisfiable :
    FamilySatisfiable create_program_address_solana_contract create_program_address_solana_sample :=
  create_program_address_solana_has_execution.satisfiable

end Solanalib.Specs.SolanaAddress.Address
