/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionsSysvarGeneric

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Pinocchio.sysvars.instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace Instructions.Generic

/-- The generic two-Deref footer family with admitted checked reads. -/
def load_current_index_contract := InstructionsSysvar.Generic.currentFamily
/-- The unchanged raw reference relation for the generic two-Deref footer family. -/
def load_current_index_run := InstructionsSysvar.Generic.currentRun
/-- The explicit inhabited mathematical sample for the generic two-Deref footer family. -/
def load_current_index_sample := InstructionsSysvar.Generic.Sample.index

theorem load_current_index_reference :
    FamilyReference load_current_index_contract load_current_index_run :=
  InstructionsSysvar.Generic.current_reference

theorem load_current_index_hasExecution :
    FamilyHasExecution load_current_index_contract load_current_index_run load_current_index_sample
      :=
  InstructionsSysvar.Generic.Sample.current_execution

theorem load_current_index_satisfiable :
    FamilySatisfiable load_current_index_contract load_current_index_sample :=
  load_current_index_hasExecution.satisfiable

/-- The generic branch-sensitive lookup family with admitted checked reads. -/
def load_instruction_at_contract := InstructionsSysvar.Generic.atFamily
/-- The unchanged raw reference relation for the generic branch-sensitive lookup family. -/
def load_instruction_at_run := InstructionsSysvar.Generic.atRun
/-- The explicit inhabited mathematical sample for the generic branch-sensitive lookup family. -/
def load_instruction_at_sample := InstructionsSysvar.Generic.Sample.index

theorem load_instruction_at_reference :
    FamilyReference load_instruction_at_contract load_instruction_at_run :=
  InstructionsSysvar.Generic.at_reference

theorem load_instruction_at_hasExecution :
    FamilyHasExecution load_instruction_at_contract load_instruction_at_run
      load_instruction_at_sample :=
  InstructionsSysvar.Generic.Sample.at_execution

theorem load_instruction_at_satisfiable :
    FamilySatisfiable load_instruction_at_contract load_instruction_at_sample :=
  load_instruction_at_hasExecution.satisfiable

end Instructions.Generic

namespace IntrospectedInstruction.Generic

/-- The current-memory program reference family with admitted checked reads. -/
def get_program_id_contract := InstructionsSysvar.Generic.programFamily
/-- The unchanged raw reference relation for the current-memory program reference family. -/
def get_program_id_run := InstructionsSysvar.Generic.programRun
/-- The explicit inhabited mathematical sample for the current-memory program reference family. -/
def get_program_id_sample := InstructionsSysvar.Generic.Sample.memory

theorem get_program_id_reference : FamilyReference get_program_id_contract get_program_id_run :=
  InstructionsSysvar.Generic.program_reference

theorem get_program_id_hasExecution :
    FamilyHasExecution get_program_id_contract get_program_id_run get_program_id_sample :=
  InstructionsSysvar.Generic.Sample.program_execution

theorem get_program_id_satisfiable : FamilySatisfiable get_program_id_contract
  get_program_id_sample :=
  get_program_id_hasExecution.satisfiable

/-- The current-memory data reference family with admitted checked reads. -/
def get_instruction_data_contract := InstructionsSysvar.Generic.dataFamily
/-- The unchanged raw reference relation for the current-memory data reference family. -/
def get_instruction_data_run := InstructionsSysvar.Generic.dataRun
/-- The explicit inhabited mathematical sample for the current-memory data reference family. -/
def get_instruction_data_sample := InstructionsSysvar.Generic.Sample.memory

theorem get_instruction_data_reference :
    FamilyReference get_instruction_data_contract get_instruction_data_run :=
  InstructionsSysvar.Generic.data_reference

theorem get_instruction_data_hasExecution :
    FamilyHasExecution get_instruction_data_contract get_instruction_data_run
      get_instruction_data_sample :=
  InstructionsSysvar.Generic.Sample.data_execution

theorem get_instruction_data_satisfiable :
    FamilySatisfiable get_instruction_data_contract get_instruction_data_sample :=
  get_instruction_data_hasExecution.satisfiable

end IntrospectedInstruction.Generic

end Solanalib.Specs.Pinocchio.sysvars.instructions
