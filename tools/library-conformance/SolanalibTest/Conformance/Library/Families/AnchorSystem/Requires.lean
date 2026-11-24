/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorSystem.Checker

set_option autoImplicit false
open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorSystem

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSystem

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem boxedLegacy_allocate_requires
    (invoke : State .boxedLegacy → CpiRequest.Request AccountInfo.Value → InvokeOut .boxedLegacy)
    (before : State .boxedLegacy)
    (args : Args (Sample.index .boxedLegacy).resources (Profile.context .boxedLegacy) .allocate) :
    (system_program.allocate_contract.contract (recordedIndex
      .boxedLegacy invoke)).requires before args := by
  letI := fixtureReady .boxedLegacy .allocate
    system_program.allocate_contract.contract rfl invoke before args
  exact of_decide_eq_true rfl

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem boxedLegacy_assign_requires
    (invoke : State .boxedLegacy → CpiRequest.Request AccountInfo.Value → InvokeOut .boxedLegacy)
    (before : State .boxedLegacy)
    (args : Args (Sample.index .boxedLegacy).resources (Profile.context .boxedLegacy) .assign) :
    (system_program.assign_contract.contract (recordedIndex .boxedLegacy
      invoke)).requires before args := by
  letI := fixtureReady .boxedLegacy .assign
    system_program.assign_contract.contract rfl invoke before args
  exact of_decide_eq_true rfl

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem boxedLegacy_create_account_requires
    (invoke : State .boxedLegacy → CpiRequest.Request AccountInfo.Value → InvokeOut .boxedLegacy)
    (before : State .boxedLegacy)
    (args : Args (Sample.index .boxedLegacy).resources (Profile.context .boxedLegacy)
      .createAccount) :
    (system_program.create_account_contract.contract (recordedIndex
      .boxedLegacy invoke)).requires before args := by
  letI := fixtureReady .boxedLegacy .createAccount
    system_program.create_account_contract.contract rfl invoke before
    args
  exact of_decide_eq_true rfl

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem boxedLegacy_transfer_requires
    (invoke : State .boxedLegacy → CpiRequest.Request AccountInfo.Value → InvokeOut .boxedLegacy)
    (before : State .boxedLegacy)
    (args : Args (Sample.index .boxedLegacy).resources (Profile.context .boxedLegacy) .transfer) :
    (system_program.transfer_contract.contract (recordedIndex
      .boxedLegacy invoke)).requires before args := by
  letI := fixtureReady .boxedLegacy .transfer
    system_program.transfer_contract.contract rfl invoke before args
  exact of_decide_eq_true rfl

end SolanalibTest.Conformance.Library.Families.AnchorSystem

namespace SolanalibTest.Conformance.Library.Families.AnchorSystem
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSystem

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem boxedModern_allocate_requires
    (invoke : State .boxedModern → CpiRequest.Request AccountInfo.Value → InvokeOut .boxedModern)
    (before : State .boxedModern)
    (args : Args (Sample.index .boxedModern).resources (Profile.context .boxedModern) .allocate) :
    (system_program.allocate_unit_borsh_contract.contract (recordedIndex
      .boxedModern invoke)).requires before args := by
  letI := fixtureReady .boxedModern .allocate
    system_program.allocate_unit_borsh_contract.contract rfl invoke
    before args
  exact of_decide_eq_true rfl

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem boxedModern_assign_requires
    (invoke : State .boxedModern → CpiRequest.Request AccountInfo.Value → InvokeOut .boxedModern)
    (before : State .boxedModern)
    (args : Args (Sample.index .boxedModern).resources (Profile.context .boxedModern) .assign) :
    (system_program.assign_unit_borsh_contract.contract (recordedIndex
      .boxedModern invoke)).requires before args := by
  letI := fixtureReady .boxedModern .assign
    system_program.assign_unit_borsh_contract.contract rfl invoke before
    args
  exact of_decide_eq_true rfl

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem boxedModern_create_account_requires
    (invoke : State .boxedModern → CpiRequest.Request AccountInfo.Value → InvokeOut .boxedModern)
    (before : State .boxedModern)
    (args : Args (Sample.index .boxedModern).resources (Profile.context .boxedModern)
      .createAccount) :
    (system_program.create_account_unit_borsh_contract.contract
      (recordedIndex .boxedModern invoke)).requires before args := by
  letI := fixtureReady .boxedModern .createAccount
    system_program.create_account_unit_borsh_contract.contract rfl
    invoke before args
  exact of_decide_eq_true rfl

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem boxedModern_transfer_requires
    (invoke : State .boxedModern → CpiRequest.Request AccountInfo.Value → InvokeOut .boxedModern)
    (before : State .boxedModern)
    (args : Args (Sample.index .boxedModern).resources (Profile.context .boxedModern) .transfer) :
    (system_program.transfer_unit_borsh_contract.contract (recordedIndex
      .boxedModern invoke)).requires before args := by
  letI := fixtureReady .boxedModern .transfer
    system_program.transfer_unit_borsh_contract.contract rfl invoke
    before args
  exact of_decide_eq_true rfl

end SolanalibTest.Conformance.Library.Families.AnchorSystem

namespace SolanalibTest.Conformance.Library.Families.AnchorSystem
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSystem

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem inlineLegacy_allocate_requires
    (invoke : State .inlineLegacy → CpiRequest.Request AccountInfo.Value → InvokeOut .inlineLegacy)
    (before : State .inlineLegacy)
    (args : Args (Sample.index .inlineLegacy).resources (Profile.context .inlineLegacy) .allocate) :
    (system_program.allocate_inline_borsh_contract.contract
      (recordedIndex .inlineLegacy invoke)).requires before args := by
  letI := fixtureReady .inlineLegacy .allocate
    system_program.allocate_inline_borsh_contract.contract rfl invoke
    before args
  exact of_decide_eq_true rfl

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem inlineLegacy_assign_requires
    (invoke : State .inlineLegacy → CpiRequest.Request AccountInfo.Value → InvokeOut .inlineLegacy)
    (before : State .inlineLegacy)
    (args : Args (Sample.index .inlineLegacy).resources (Profile.context .inlineLegacy) .assign) :
    (system_program.assign_inline_borsh_contract.contract (recordedIndex
      .inlineLegacy invoke)).requires before args := by
  letI := fixtureReady .inlineLegacy .assign
    system_program.assign_inline_borsh_contract.contract rfl invoke
    before args
  exact of_decide_eq_true rfl

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem inlineLegacy_create_account_requires
    (invoke : State .inlineLegacy → CpiRequest.Request AccountInfo.Value → InvokeOut .inlineLegacy)
    (before : State .inlineLegacy)
    (args : Args (Sample.index .inlineLegacy).resources (Profile.context .inlineLegacy)
      .createAccount) :
    (system_program.create_account_inline_borsh_contract.contract
      (recordedIndex .inlineLegacy invoke)).requires before args := by
  letI := fixtureReady .inlineLegacy .createAccount
    system_program.create_account_inline_borsh_contract.contract rfl
    invoke before args
  exact of_decide_eq_true rfl

/-- The exact registered precondition holds at the checker index in every input state. -/
theorem inlineLegacy_transfer_requires
    (invoke : State .inlineLegacy → CpiRequest.Request AccountInfo.Value → InvokeOut .inlineLegacy)
    (before : State .inlineLegacy)
    (args : Args (Sample.index .inlineLegacy).resources (Profile.context .inlineLegacy) .transfer) :
    (system_program.transfer_inline_borsh_contract.contract
      (recordedIndex .inlineLegacy invoke)).requires before args := by
  letI := fixtureReady .inlineLegacy .transfer
    system_program.transfer_inline_borsh_contract.contract rfl invoke
    before args
  exact of_decide_eq_true rfl

end SolanalibTest.Conformance.Library.Families.AnchorSystem
