/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionMeta

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaInstruction.AccountMeta

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Borrowed, allocation-free field copy. Reviewed historical defining paths
are supplied by the build applicability registry. -/
def clone_contract := InstructionMeta.family
def clone_run := InstructionMeta.reference
def clone_sample := InstructionMeta.sample

theorem clone_reference : FamilyReference clone_contract clone_run :=
  InstructionMeta.reference_correct

theorem clone_satisfiable : FamilySatisfiable clone_contract clone_sample :=
  InstructionMeta.sample_satisfiable

theorem clone_has_execution :
    FamilyHasExecution clone_contract clone_run clone_sample :=
  InstructionMeta.sample_hasExecution

end Solanalib.Specs.SolanaInstruction.AccountMeta
