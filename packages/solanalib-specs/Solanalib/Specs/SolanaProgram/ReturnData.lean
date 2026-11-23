/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.ReturnData

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.program

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Versioned source dispatch to the Solana return-data helper or host stub,
retaining every provider exit and applying no local runtime size check. -/
def set_return_data_contract : Family := ReturnData.family

/-- The complete callee-forwarding relation at each supplied model index. -/
def set_return_data_model : FamilyRun set_return_data_contract := ReturnData.reference

/-- An inhabited recording provider for the consistency witness. -/
def set_return_data_sample : set_return_data_contract.Index := ReturnData.sample

theorem set_return_data_reference :
    FamilyReference set_return_data_contract set_return_data_model := ReturnData.reference_correct

theorem set_return_data_hasExecution :
    FamilyHasExecution set_return_data_contract set_return_data_model set_return_data_sample :=
  ReturnData.sample_hasExecution

theorem set_return_data_satisfiable :
    FamilySatisfiable set_return_data_contract set_return_data_sample :=
  set_return_data_hasExecution.satisfiable

end Solanalib.Specs.SolanaProgram.program
