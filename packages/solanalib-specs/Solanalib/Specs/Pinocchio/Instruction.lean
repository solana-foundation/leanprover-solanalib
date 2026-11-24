/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionBorrowed

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Pinocchio.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Instruction.Borrowed

namespace AccountMeta
def readonly_contract := metaFamily false false
def readonly_run := metaRun false false
def readonly_sample := metaSample
theorem readonly_reference : FamilyReference readonly_contract readonly_run := meta_reference _ _
theorem readonly_hasExecution : FamilyHasExecution readonly_contract readonly_run readonly_sample
  := meta_hasExecution _ _
theorem readonly_satisfiable : FamilySatisfiable readonly_contract readonly_sample :=
  readonly_hasExecution.satisfiable

def readonly_signer_contract := metaFamily false true
def readonly_signer_run := metaRun false true
def readonly_signer_sample := metaSample
theorem readonly_signer_reference : FamilyReference readonly_signer_contract readonly_signer_run :=
  meta_reference _ _
theorem readonly_signer_hasExecution : FamilyHasExecution readonly_signer_contract
  readonly_signer_run readonly_signer_sample := meta_hasExecution _ _
theorem readonly_signer_satisfiable : FamilySatisfiable readonly_signer_contract
  readonly_signer_sample := readonly_signer_hasExecution.satisfiable

def writable_contract := metaFamily true false
def writable_run := metaRun true false
def writable_sample := metaSample
theorem writable_reference : FamilyReference writable_contract writable_run := meta_reference _ _
theorem writable_hasExecution : FamilyHasExecution writable_contract writable_run writable_sample
  := meta_hasExecution _ _
theorem writable_satisfiable : FamilySatisfiable writable_contract writable_sample :=
  writable_hasExecution.satisfiable

def writable_signer_contract := metaFamily true true
def writable_signer_run := metaRun true true
def writable_signer_sample := metaSample
theorem writable_signer_reference : FamilyReference writable_signer_contract writable_signer_run :=
  meta_reference _ _
theorem writable_signer_hasExecution : FamilyHasExecution writable_signer_contract
  writable_signer_run writable_signer_sample := meta_hasExecution _ _
theorem writable_signer_satisfiable : FamilySatisfiable writable_signer_contract
  writable_signer_sample := writable_signer_hasExecution.satisfiable
end AccountMeta

namespace Seed
def from_array_contract := seedArrayFamily
def from_array_run := seedArrayRun
def from_array_sample := seedArraySample
theorem from_array_reference : FamilyReference from_array_contract from_array_run :=
  seedArray_reference
theorem from_array_hasExecution : FamilyHasExecution from_array_contract from_array_run
  from_array_sample := seedArray_hasExecution
theorem from_array_satisfiable : FamilySatisfiable from_array_contract from_array_sample :=
  from_array_hasExecution.satisfiable
end Seed

end Solanalib.Specs.Pinocchio.instruction
