/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSystemWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.system_program

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Complete allocate wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def allocate_contract : Family := AnchorSystem.family .boxedLegacy .allocate

/-- The same full resource/control relation is the registered reference. -/
def allocate_run : FamilyRun allocate_contract := AnchorSystem.reference .boxedLegacy .allocate

/-- Universal correctness for every fixed generic provider assignment. -/
theorem allocate_reference : FamilyReference allocate_contract allocate_run :=
  AnchorSystem.reference_holds .boxedLegacy .allocate

/-- A finite nonempty resource interpretation for the closed witness. -/
def allocate_sample : allocate_contract.Index := AnchorSystem.Sample.index .boxedLegacy

/-- The actual sample constructor returns readable current resources. -/
theorem allocate_satisfiable : FamilySatisfiable allocate_contract allocate_sample :=
  AnchorSystem.Sample.satisfiable .boxedLegacy .allocate

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem allocate_has_execution :
    FamilyHasExecution allocate_contract allocate_run allocate_sample :=
  AnchorSystem.Sample.execution .boxedLegacy .allocate

/-- Complete assign wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def assign_contract : Family := AnchorSystem.family .boxedLegacy .assign

/-- The same full resource/control relation is the registered reference. -/
def assign_run : FamilyRun assign_contract := AnchorSystem.reference .boxedLegacy .assign

/-- Universal correctness for every fixed generic provider assignment. -/
theorem assign_reference : FamilyReference assign_contract assign_run :=
  AnchorSystem.reference_holds .boxedLegacy .assign

/-- A finite nonempty resource interpretation for the closed witness. -/
def assign_sample : assign_contract.Index := AnchorSystem.Sample.index .boxedLegacy

/-- The actual sample constructor returns readable current resources. -/
theorem assign_satisfiable : FamilySatisfiable assign_contract assign_sample :=
  AnchorSystem.Sample.satisfiable .boxedLegacy .assign

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem assign_has_execution :
    FamilyHasExecution assign_contract assign_run assign_sample :=
  AnchorSystem.Sample.execution .boxedLegacy .assign

/-- Complete create_account wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def create_account_contract : Family := AnchorSystem.family .boxedLegacy .createAccount

/-- The same full resource/control relation is the registered reference. -/
def create_account_run : FamilyRun create_account_contract := AnchorSystem.reference .boxedLegacy
  .createAccount

/-- Universal correctness for every fixed generic provider assignment. -/
theorem create_account_reference : FamilyReference create_account_contract create_account_run :=
  AnchorSystem.reference_holds .boxedLegacy .createAccount

/-- A finite nonempty resource interpretation for the closed witness. -/
def create_account_sample : create_account_contract.Index := AnchorSystem.Sample.index .boxedLegacy

/-- The actual sample constructor returns readable current resources. -/
theorem create_account_satisfiable : FamilySatisfiable create_account_contract
  create_account_sample :=
  AnchorSystem.Sample.satisfiable .boxedLegacy .createAccount

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem create_account_has_execution :
    FamilyHasExecution create_account_contract create_account_run create_account_sample :=
  AnchorSystem.Sample.execution .boxedLegacy .createAccount

/-- Complete transfer wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def transfer_contract : Family := AnchorSystem.family .boxedLegacy .transfer

/-- The same full resource/control relation is the registered reference. -/
def transfer_run : FamilyRun transfer_contract := AnchorSystem.reference .boxedLegacy .transfer

/-- Universal correctness for every fixed generic provider assignment. -/
theorem transfer_reference : FamilyReference transfer_contract transfer_run :=
  AnchorSystem.reference_holds .boxedLegacy .transfer

/-- A finite nonempty resource interpretation for the closed witness. -/
def transfer_sample : transfer_contract.Index := AnchorSystem.Sample.index .boxedLegacy

/-- The actual sample constructor returns readable current resources. -/
theorem transfer_satisfiable : FamilySatisfiable transfer_contract transfer_sample :=
  AnchorSystem.Sample.satisfiable .boxedLegacy .transfer

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem transfer_has_execution :
    FamilyHasExecution transfer_contract transfer_run transfer_sample :=
  AnchorSystem.Sample.execution .boxedLegacy .transfer

end Solanalib.Specs.AnchorLang.system_program

namespace Solanalib.Specs.AnchorLang.system_program

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace System

/-- The public System marker returns the fixed, canonical system address. -/
def id_run (before : Unit) (_ : Unit) : _root_.Solanalib.Runtime.Pubkey × Unit :=
  (Instruction.systemProgramId, before)

/-- This method returns a copy of ID and has no callback or account access. -/
def id_contract : Solanalib.Contracts.Model Unit Unit _root_.Solanalib.Runtime.Pubkey :=
  .returning (fun _ _ => True)
    (fun before _ value after => value = Instruction.systemProgramId ∧ after = before)

/-- The complete pure reference preserves its ambient mathematical state. -/
theorem id_reference : id_contract.RealizedBy id_run := fun _ _ _ => ⟨rfl, rfl⟩

/-- The marker method has an inhabited input. -/
theorem id_satisfiable : id_contract.Satisfiable := ⟨(), (), trivial⟩

end System

end Solanalib.Specs.AnchorLang.system_program

@[expose] public section

set_option autoImplicit false

/-! System wrapper contracts for the selected Anchor 1.1.2 operations.
The catalog records the exact source and build conditions. -/

namespace Solanalib.Specs.AnchorLang.system_program

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Complete allocate wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def allocate_unit_borsh_contract : Family := AnchorSystem.family .boxedModern .allocate

/-- The same full resource/control relation is the registered reference. -/
def allocate_unit_borsh_run : FamilyRun allocate_unit_borsh_contract := AnchorSystem.reference
  .boxedModern .allocate

/-- Universal correctness for every fixed generic provider assignment. -/
theorem allocate_unit_borsh_reference : FamilyReference allocate_unit_borsh_contract
  allocate_unit_borsh_run :=
  AnchorSystem.reference_holds .boxedModern .allocate

/-- A finite nonempty resource interpretation for the closed witness. -/
def allocate_unit_borsh_sample : allocate_unit_borsh_contract.Index := AnchorSystem.Sample.index
  .boxedModern

/-- The actual sample constructor returns readable current resources. -/
theorem allocate_unit_borsh_satisfiable : FamilySatisfiable allocate_unit_borsh_contract
  allocate_unit_borsh_sample :=
  AnchorSystem.Sample.satisfiable .boxedModern .allocate

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem allocate_unit_borsh_has_execution :
    FamilyHasExecution allocate_unit_borsh_contract allocate_unit_borsh_run
      allocate_unit_borsh_sample :=
  AnchorSystem.Sample.execution .boxedModern .allocate

/-- Complete assign wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def assign_unit_borsh_contract : Family := AnchorSystem.family .boxedModern .assign

/-- The same full resource/control relation is the registered reference. -/
def assign_unit_borsh_run : FamilyRun assign_unit_borsh_contract := AnchorSystem.reference
  .boxedModern .assign

/-- Universal correctness for every fixed generic provider assignment. -/
theorem assign_unit_borsh_reference : FamilyReference assign_unit_borsh_contract
  assign_unit_borsh_run :=
  AnchorSystem.reference_holds .boxedModern .assign

/-- A finite nonempty resource interpretation for the closed witness. -/
def assign_unit_borsh_sample : assign_unit_borsh_contract.Index := AnchorSystem.Sample.index
  .boxedModern

/-- The actual sample constructor returns readable current resources. -/
theorem assign_unit_borsh_satisfiable : FamilySatisfiable assign_unit_borsh_contract
  assign_unit_borsh_sample :=
  AnchorSystem.Sample.satisfiable .boxedModern .assign

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem assign_unit_borsh_has_execution :
    FamilyHasExecution assign_unit_borsh_contract assign_unit_borsh_run assign_unit_borsh_sample :=
  AnchorSystem.Sample.execution .boxedModern .assign

/-- Complete create_account wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def create_account_unit_borsh_contract : Family := AnchorSystem.family .boxedModern .createAccount

/-- The same full resource/control relation is the registered reference. -/
def create_account_unit_borsh_run : FamilyRun create_account_unit_borsh_contract :=
  AnchorSystem.reference .boxedModern .createAccount

/-- Universal correctness for every fixed generic provider assignment. -/
theorem create_account_unit_borsh_reference : FamilyReference create_account_unit_borsh_contract
  create_account_unit_borsh_run :=
  AnchorSystem.reference_holds .boxedModern .createAccount

/-- A finite nonempty resource interpretation for the closed witness. -/
def create_account_unit_borsh_sample : create_account_unit_borsh_contract.Index :=
  AnchorSystem.Sample.index .boxedModern

/-- The actual sample constructor returns readable current resources. -/
theorem create_account_unit_borsh_satisfiable : FamilySatisfiable
  create_account_unit_borsh_contract create_account_unit_borsh_sample :=
  AnchorSystem.Sample.satisfiable .boxedModern .createAccount

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem create_account_unit_borsh_has_execution :
    FamilyHasExecution create_account_unit_borsh_contract create_account_unit_borsh_run
      create_account_unit_borsh_sample :=
  AnchorSystem.Sample.execution .boxedModern .createAccount

/-- Complete transfer wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def transfer_unit_borsh_contract : Family := AnchorSystem.family .boxedModern .transfer

/-- The same full resource/control relation is the registered reference. -/
def transfer_unit_borsh_run : FamilyRun transfer_unit_borsh_contract := AnchorSystem.reference
  .boxedModern .transfer

/-- Universal correctness for every fixed generic provider assignment. -/
theorem transfer_unit_borsh_reference : FamilyReference transfer_unit_borsh_contract
  transfer_unit_borsh_run :=
  AnchorSystem.reference_holds .boxedModern .transfer

/-- A finite nonempty resource interpretation for the closed witness. -/
def transfer_unit_borsh_sample : transfer_unit_borsh_contract.Index := AnchorSystem.Sample.index
  .boxedModern

/-- The actual sample constructor returns readable current resources. -/
theorem transfer_unit_borsh_satisfiable : FamilySatisfiable transfer_unit_borsh_contract
  transfer_unit_borsh_sample :=
  AnchorSystem.Sample.satisfiable .boxedModern .transfer

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem transfer_unit_borsh_has_execution :
    FamilyHasExecution transfer_unit_borsh_contract transfer_unit_borsh_run
      transfer_unit_borsh_sample :=
  AnchorSystem.Sample.execution .boxedModern .transfer

end Solanalib.Specs.AnchorLang.system_program

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.system_program

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Complete allocate wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def allocate_inline_borsh_contract : Family := AnchorSystem.family .inlineLegacy .allocate

/-- The same full resource/control relation is the registered reference. -/
def allocate_inline_borsh_run : FamilyRun allocate_inline_borsh_contract := AnchorSystem.reference
  .inlineLegacy .allocate

/-- Universal correctness for every fixed generic provider assignment. -/
theorem allocate_inline_borsh_reference : FamilyReference allocate_inline_borsh_contract
  allocate_inline_borsh_run :=
  AnchorSystem.reference_holds .inlineLegacy .allocate

/-- A finite nonempty resource interpretation for the closed witness. -/
def allocate_inline_borsh_sample : allocate_inline_borsh_contract.Index :=
  AnchorSystem.Sample.index .inlineLegacy

/-- The actual sample constructor returns readable current resources. -/
theorem allocate_inline_borsh_satisfiable : FamilySatisfiable allocate_inline_borsh_contract
  allocate_inline_borsh_sample :=
  AnchorSystem.Sample.satisfiable .inlineLegacy .allocate

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem allocate_inline_borsh_has_execution :
    FamilyHasExecution allocate_inline_borsh_contract allocate_inline_borsh_run
      allocate_inline_borsh_sample :=
  AnchorSystem.Sample.execution .inlineLegacy .allocate

/-- Complete assign wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def assign_inline_borsh_contract : Family := AnchorSystem.family .inlineLegacy .assign

/-- The same full resource/control relation is the registered reference. -/
def assign_inline_borsh_run : FamilyRun assign_inline_borsh_contract := AnchorSystem.reference
  .inlineLegacy .assign

/-- Universal correctness for every fixed generic provider assignment. -/
theorem assign_inline_borsh_reference : FamilyReference assign_inline_borsh_contract
  assign_inline_borsh_run :=
  AnchorSystem.reference_holds .inlineLegacy .assign

/-- A finite nonempty resource interpretation for the closed witness. -/
def assign_inline_borsh_sample : assign_inline_borsh_contract.Index := AnchorSystem.Sample.index
  .inlineLegacy

/-- The actual sample constructor returns readable current resources. -/
theorem assign_inline_borsh_satisfiable : FamilySatisfiable assign_inline_borsh_contract
  assign_inline_borsh_sample :=
  AnchorSystem.Sample.satisfiable .inlineLegacy .assign

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem assign_inline_borsh_has_execution :
    FamilyHasExecution assign_inline_borsh_contract assign_inline_borsh_run
      assign_inline_borsh_sample :=
  AnchorSystem.Sample.execution .inlineLegacy .assign

/-- Complete create_account wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def create_account_inline_borsh_contract : Family := AnchorSystem.family .inlineLegacy
  .createAccount

/-- The same full resource/control relation is the registered reference. -/
def create_account_inline_borsh_run : FamilyRun create_account_inline_borsh_contract :=
  AnchorSystem.reference .inlineLegacy .createAccount

/-- Universal correctness for every fixed generic provider assignment. -/
theorem create_account_inline_borsh_reference : FamilyReference
  create_account_inline_borsh_contract create_account_inline_borsh_run :=
  AnchorSystem.reference_holds .inlineLegacy .createAccount

/-- A finite nonempty resource interpretation for the closed witness. -/
def create_account_inline_borsh_sample : create_account_inline_borsh_contract.Index :=
  AnchorSystem.Sample.index .inlineLegacy

/-- The actual sample constructor returns readable current resources. -/
theorem create_account_inline_borsh_satisfiable : FamilySatisfiable
  create_account_inline_borsh_contract create_account_inline_borsh_sample :=
  AnchorSystem.Sample.satisfiable .inlineLegacy .createAccount

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem create_account_inline_borsh_has_execution :
    FamilyHasExecution create_account_inline_borsh_contract create_account_inline_borsh_run
      create_account_inline_borsh_sample :=
  AnchorSystem.Sample.execution .inlineLegacy .createAccount

/-- Complete transfer wrapper model above the exact primitive constructor,
release-selected error conversion, resource cleanup and opaque CPI providers. -/
def transfer_inline_borsh_contract : Family := AnchorSystem.family .inlineLegacy .transfer

/-- The same full resource/control relation is the registered reference. -/
def transfer_inline_borsh_run : FamilyRun transfer_inline_borsh_contract := AnchorSystem.reference
  .inlineLegacy .transfer

/-- Universal correctness for every fixed generic provider assignment. -/
theorem transfer_inline_borsh_reference : FamilyReference transfer_inline_borsh_contract
  transfer_inline_borsh_run :=
  AnchorSystem.reference_holds .inlineLegacy .transfer

/-- A finite nonempty resource interpretation for the closed witness. -/
def transfer_inline_borsh_sample : transfer_inline_borsh_contract.Index :=
  AnchorSystem.Sample.index .inlineLegacy

/-- The actual sample constructor returns readable current resources. -/
theorem transfer_inline_borsh_satisfiable : FamilySatisfiable transfer_inline_borsh_contract
  transfer_inline_borsh_sample :=
  AnchorSystem.Sample.satisfiable .inlineLegacy .transfer

/-- A complete finite mathematical execution, with request and cleanup. -/
theorem transfer_inline_borsh_has_execution :
    FamilyHasExecution transfer_inline_borsh_contract transfer_inline_borsh_run
      transfer_inline_borsh_sample :=
  AnchorSystem.Sample.execution .inlineLegacy .transfer

end Solanalib.Specs.AnchorLang.system_program
