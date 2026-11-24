/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionsSysvarCheckedWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaInstructionsSysvar

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.InstructionsSysvar

def load_current_index_checked_contract : Family := Checked.currentFamily
def load_current_index_checked_run : FamilyRun load_current_index_checked_contract :=
  Checked.currentReference
def load_current_index_checked_sample : load_current_index_checked_contract.Index :=
  Checked.Witness.currentSample

theorem load_current_index_checked_reference : FamilyReference load_current_index_checked_contract
  load_current_index_checked_run :=
  Checked.current_reference

theorem load_current_index_checked_hasExecution :
    FamilyHasExecution load_current_index_checked_contract load_current_index_checked_run
      load_current_index_checked_sample :=
  Checked.Witness.current_hasExecution

theorem load_current_index_checked_satisfiable : FamilySatisfiable
  load_current_index_checked_contract load_current_index_checked_sample :=
  load_current_index_checked_hasExecution.satisfiable

def load_instruction_at_checked_contract : Family := Checked.instructionFamily
def load_instruction_at_checked_run : FamilyRun load_instruction_at_checked_contract :=
  Checked.instructionReference
def load_instruction_at_checked_sample : load_instruction_at_checked_contract.Index :=
  Checked.Witness.instructionSample

theorem load_instruction_at_checked_reference : FamilyReference
  load_instruction_at_checked_contract load_instruction_at_checked_run :=
  Checked.instruction_reference

theorem load_instruction_at_checked_hasExecution :
    FamilyHasExecution load_instruction_at_checked_contract load_instruction_at_checked_run
      load_instruction_at_checked_sample :=
  Checked.Witness.instruction_hasExecution

theorem load_instruction_at_checked_satisfiable : FamilySatisfiable
  load_instruction_at_checked_contract load_instruction_at_checked_sample :=
  load_instruction_at_checked_hasExecution.satisfiable

end Solanalib.Specs.SolanaInstructionsSysvar
