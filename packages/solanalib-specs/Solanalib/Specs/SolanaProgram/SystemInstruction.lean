/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionSystemExtendedSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.system_instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core

def create_account_with_seed_contract := InstructionSystemExtended.seedFamily
def create_account_with_seed_run := InstructionSystemExtended.seedReference
def create_account_with_seed_sample := InstructionSystemExtended.Sample.seedTypes

theorem create_account_with_seed_reference :
    FamilyReference create_account_with_seed_contract create_account_with_seed_run :=
  InstructionSystemExtended.seedReference_correct

theorem create_account_with_seed_satisfiable :
    FamilySatisfiable create_account_with_seed_contract create_account_with_seed_sample :=
  InstructionSystemExtended.Sample.seed_execution.satisfiable

theorem create_account_with_seed_has_execution :
    FamilyHasExecution create_account_with_seed_contract create_account_with_seed_run
      create_account_with_seed_sample := InstructionSystemExtended.Sample.seed_execution

end Solanalib.Specs.SolanaProgram.system_instruction
