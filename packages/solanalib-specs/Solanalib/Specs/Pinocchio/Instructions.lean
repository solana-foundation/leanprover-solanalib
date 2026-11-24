/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionsSysvar

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Pinocchio.sysvars.instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-! These contracts interpret the Ref-backed receiver. The separate
`InstructionsGeneric` module retains generic custom `T::deref` effects;
they are not silently replaced by these pure guard reads. -/

namespace Instructions

/-- A Ref-backed receiver retaining its original shared guard. -/
abbrev Value := InstructionsSysvar.Instructions

/-- Checked key/borrow source contract; successful slice formation is readable without any
serialization premise. -/
def try_from_contract :
    Solanalib.Contracts.Model AccountView.State AccountView.Handle (Except ProgramError.Value
      Value) :=
  .returning InstructionsSysvar.constructorReady
    (fun before handle value after => InstructionsSysvar.tryFrom before handle = (value, after) ∧
      InstructionsSysvar.checkedTryFrom before handle = some (value, after))

/-- The unchanged key-first constructor and shared acquisition operation. -/
def try_from_run := InstructionsSysvar.tryFrom

theorem try_from_reference : try_from_contract.RealizedBy try_from_run := by
  intro before handle ready
  exact ⟨rfl, InstructionsSysvar.constructor_checked before handle ready⟩

theorem try_from_hasExecution : try_from_contract.HasExecution (returnsOf try_from_run) :=
  ⟨InstructionsSysvar.Witness.initial, Sysvar.Witness.handle,
    .returned (.ok InstructionsSysvar.Witness.source) InstructionsSysvar.Witness.borrowed,
    InstructionsSysvar.Witness.constructor_ready, rfl⟩

theorem try_from_satisfiable : try_from_contract.Satisfiable := try_from_hasExecution.satisfiable

/-- Source footer domain with the exact checked current two-byte result. -/
def load_current_index_contract : Solanalib.Contracts.Model AccountView.State Value UInt16 :=
  .returning InstructionsSysvar.currentIndexReady
    (fun before source value after =>
      after = before ∧ value = InstructionsSysvar.currentIndex before source ∧
      InstructionsSysvar.checkedCurrentIndex before source = some value)

/-- The unchanged total mathematical current-index observer. -/
def load_current_index_run (state : AccountView.State) (source : Value) :
    UInt16 × AccountView.State := (InstructionsSysvar.currentIndex state source, state)

theorem load_current_index_reference :
    load_current_index_contract.RealizedBy load_current_index_run := by
  intro before source ready
  exact ⟨rfl, rfl, InstructionsSysvar.currentIndex_checked before source ready⟩

theorem load_current_index_hasExecution :
    load_current_index_contract.HasExecution (returnsOf load_current_index_run) :=
  ⟨InstructionsSysvar.Witness.borrowed, InstructionsSysvar.Witness.source,
    .returned 0 InstructionsSysvar.Witness.borrowed, InstructionsSysvar.Witness.current_ready, rfl⟩

theorem load_current_index_satisfiable : load_current_index_contract.Satisfiable :=
  load_current_index_hasExecution.satisfiable

/-- Source count/table domain with branch-sensitive checked pointer formation. -/
def load_instruction_at_contract :
    Solanalib.Contracts.Model AccountView.State (Value × UInt64)
      (Except ProgramError.Value InstructionsSysvar.IntrospectedInstruction) :=
  .returning InstructionsSysvar.instructionAtReady
    (fun before args value after =>
      after = before ∧ value = InstructionsSysvar.instructionAt before args ∧
      InstructionsSysvar.checkedInstructionAt before args = some value)

/-- The unchanged mathematical count check and offset lookup. -/
def load_instruction_at_run (state : AccountView.State) (args : Value × UInt64) :
    Except ProgramError.Value InstructionsSysvar.IntrospectedInstruction × AccountView.State :=
  (InstructionsSysvar.instructionAt state args, state)

theorem load_instruction_at_reference :
    load_instruction_at_contract.RealizedBy load_instruction_at_run := by
  intro before args ready
  exact ⟨rfl, rfl, InstructionsSysvar.instructionAt_checked before args ready⟩

theorem load_instruction_at_hasExecution :
    load_instruction_at_contract.HasExecution (returnsOf load_instruction_at_run) :=
  ⟨InstructionsSysvar.Witness.borrowed, (InstructionsSysvar.Witness.source, 0),
    .returned (.ok InstructionsSysvar.Witness.instruction) InstructionsSysvar.Witness.borrowed,
    InstructionsSysvar.Witness.instruction_ready, rfl⟩

theorem load_instruction_at_satisfiable : load_instruction_at_contract.Satisfiable :=
  load_instruction_at_hasExecution.satisfiable

end Instructions

namespace IntrospectedInstruction

/-- An introspected pointer relative to its original guarded slice. -/
abbrev Value := InstructionsSysvar.IntrospectedInstruction

/-- Source entry/count domain yielding the complete 32-byte borrowed program region. -/
def get_program_id_contract :
    Solanalib.Contracts.Model AccountView.State Value InstructionsSysvar.ProgramIdRef :=
  .returning InstructionsSysvar.programIdReady
    (fun before instruction value after =>
      after = before ∧ value = InstructionsSysvar.programId before instruction ∧
      InstructionsSysvar.checkedProgramId before instruction = some value ∧
      (value.bytes before).length = 32)

/-- The unchanged mathematical borrowed program-pointer observer. -/
def get_program_id_run (state : AccountView.State) (instruction : Value) :
    InstructionsSysvar.ProgramIdRef × AccountView.State :=
  (InstructionsSysvar.programId state instruction, state)

theorem get_program_id_reference : get_program_id_contract.RealizedBy get_program_id_run := by
  intro before instruction ready
  exact ⟨rfl, rfl, InstructionsSysvar.programId_checked before instruction ready⟩

theorem get_program_id_hasExecution :
    get_program_id_contract.HasExecution (returnsOf get_program_id_run) :=
  ⟨InstructionsSysvar.Witness.borrowed, InstructionsSysvar.Witness.instruction,
    .returned ⟨InstructionsSysvar.Witness.source, 39⟩ InstructionsSysvar.Witness.borrowed,
    InstructionsSysvar.Witness.program_ready, rfl⟩

theorem get_program_id_satisfiable : get_program_id_contract.Satisfiable :=
  get_program_id_hasExecution.satisfiable

/-- Source count/length/payload domain yielding the complete current borrowed slice. -/
def get_instruction_data_contract :
    Solanalib.Contracts.Model AccountView.State Value InstructionsSysvar.DataRef :=
  .returning InstructionsSysvar.dataReady
    (fun before instruction value after =>
      after = before ∧ value = InstructionsSysvar.data before instruction ∧
      InstructionsSysvar.checkedData before instruction = some value ∧
      (value.bytes before).length = value.length)

/-- The unchanged mathematical borrowed data-slice observer. -/
def get_instruction_data_run (state : AccountView.State) (instruction : Value) :
    InstructionsSysvar.DataRef × AccountView.State :=
  (InstructionsSysvar.data state instruction, state)

theorem get_instruction_data_reference :
    get_instruction_data_contract.RealizedBy get_instruction_data_run := by
  intro before instruction ready
  exact ⟨rfl, rfl, InstructionsSysvar.data_checked before instruction ready⟩

theorem get_instruction_data_hasExecution :
    get_instruction_data_contract.HasExecution (returnsOf get_instruction_data_run) :=
  ⟨InstructionsSysvar.Witness.borrowed, InstructionsSysvar.Witness.instruction,
    .returned ⟨InstructionsSysvar.Witness.source, 73, 3⟩ InstructionsSysvar.Witness.borrowed,
    InstructionsSysvar.Witness.data_ready, rfl⟩

theorem get_instruction_data_satisfiable : get_instruction_data_contract.Satisfiable :=
  get_instruction_data_hasExecution.satisfiable

end IntrospectedInstruction

end Solanalib.Specs.Pinocchio.sysvars.instructions
