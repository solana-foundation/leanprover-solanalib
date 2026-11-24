/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Instruction
public import Solanalib.Specs.Core.InstructionMeta
public import Solanalib.Specs.Core.InstructionCloneSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.instruction.AccountMeta

open Solanalib.Specs.Core.Instruction

def new_model (before : Unit) (args : _root_.Solanalib.Runtime.Pubkey × Bool) : Meta × Unit :=
  (accountMeta args.1 args.2 true, before)

def new_contract : Solanalib.Contracts.Model Unit (_root_.Solanalib.Runtime.Pubkey × Bool) (Meta) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = accountMeta args.1 args.2 true)

theorem new_reference : new_contract.RealizedBy new_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem new_satisfiable : new_contract.Satisfiable :=
  ⟨(), (.zero, false), trivial⟩

def new_readonly_model (before : Unit) (args : _root_.Solanalib.Runtime.Pubkey × Bool) : Meta ×
  Unit :=
  (accountMeta args.1 args.2 false, before)

def new_readonly_contract : Solanalib.Contracts.Model Unit (_root_.Solanalib.Runtime.Pubkey × Bool)
  (Meta) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = accountMeta args.1 args.2 false)

theorem new_readonly_reference : new_readonly_contract.RealizedBy new_readonly_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem new_readonly_satisfiable : new_readonly_contract.Satisfiable :=
  ⟨(), (.zero, false), trivial⟩

end Solanalib.Specs.SolanaProgram.instruction.AccountMeta

namespace Solanalib.Specs.SolanaProgram.instruction.AccountMeta

open Solanalib.Contracts.Model Solanalib.Specs.Core

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

end Solanalib.Specs.SolanaProgram.instruction.AccountMeta

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.instruction.Instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The selected solana-program 1.15.2 Instruction clone uses the shared
InstructionClone family. It preserves a borrowed input and constructs two
owned vectors in field order, retaining allocation and cleanup outcomes. -/
def clone_contract := InstructionClone.family
def clone_run := InstructionClone.reference
def clone_sample := InstructionClone.Sample.types

theorem clone_reference : FamilyReference clone_contract clone_run :=
  InstructionClone.reference_correct

theorem clone_satisfiable : FamilySatisfiable clone_contract clone_sample :=
  InstructionClone.Sample.execution.satisfiable

theorem clone_has_execution :
    FamilyHasExecution clone_contract clone_run clone_sample :=
  InstructionClone.Sample.execution

end Solanalib.Specs.SolanaProgram.instruction.Instruction
