/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.ProgramOptionOperations

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgramOption.COption

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Derived variant equality with the actual borrowed payload callback. -/
abbrev eq_contract : Family := ProgramOption.eqFamily

/-- Exact relational reference at every source interpretation. -/
abbrev eq_run : FamilyRun eq_contract := ProgramOption.eqRun

theorem eq_reference : FamilyReference eq_contract eq_run :=
  ProgramOption.eqReference

/-- Closed registered source-type and callback sample. -/
abbrev eq_sample := ProgramOption.eqSample

theorem eq_has_execution : FamilyHasExecution eq_contract eq_run eq_sample :=
  ProgramOption.eqExecution

theorem eq_satisfiable : FamilySatisfiable eq_contract eq_sample :=
  ProgramOption.eqSatisfiable

/-- Move a present value, or use the nonreturning panic provider with the exact diagnostic. -/
abbrev unwrap_contract : Family := ProgramOption.unwrapFamily

/-- Exact relational reference at every source interpretation. -/
abbrev unwrap_run : FamilyRun unwrap_contract := ProgramOption.unwrapRun

theorem unwrap_reference : FamilyReference unwrap_contract unwrap_run :=
  ProgramOption.unwrapReference

/-- Closed registered source-type and callback sample. -/
abbrev unwrap_sample := ProgramOption.unwrapSample

theorem unwrap_has_execution : FamilyHasExecution unwrap_contract unwrap_run unwrap_sample :=
  ProgramOption.unwrapExecution

theorem unwrap_satisfiable : FamilySatisfiable unwrap_contract unwrap_sample :=
  ProgramOption.unwrapSatisfiable


end Solanalib.Specs.SolanaProgramOption.COption
