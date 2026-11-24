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

namespace Solanalib.Specs.SolanaSystemInterface.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Full local constructor control flow, including optional payer push and
the selected serializer. This invokes no System program operation. -/
def create_account_allow_prefund_contract := InstructionSystemExtended.prefundFamily
def create_account_allow_prefund_run := InstructionSystemExtended.prefundReference
def create_account_allow_prefund_sample := InstructionSystemExtended.Sample.types

theorem create_account_allow_prefund_reference :
    FamilyReference create_account_allow_prefund_contract create_account_allow_prefund_run :=
  InstructionSystemExtended.prefundReference_correct

theorem create_account_allow_prefund_satisfiable :
    FamilySatisfiable create_account_allow_prefund_contract create_account_allow_prefund_sample :=
  InstructionSystemExtended.Sample.prefund_execution.satisfiable

theorem create_account_allow_prefund_has_execution :
    FamilyHasExecution create_account_allow_prefund_contract create_account_allow_prefund_run
      create_account_allow_prefund_sample := InstructionSystemExtended.Sample.prefund_execution

end Solanalib.Specs.SolanaSystemInterface.instruction
