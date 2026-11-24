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

namespace Solanalib.Specs.SolanaProgram.program_option.COption

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Move the payload unchanged from COption into the ordinary Option enum. -/
abbrev into_option_contract : Family := ProgramOption.intoOptionFamily

/-- Exact relational reference at every source interpretation. -/
abbrev into_option_run : FamilyRun into_option_contract := ProgramOption.intoOptionRun

theorem into_option_reference : FamilyReference into_option_contract into_option_run :=
  ProgramOption.intoOptionReference

/-- Closed registered source-type and callback sample. -/
abbrev into_option_sample := ProgramOption.intoOptionSample

theorem into_option_has_execution : FamilyHasExecution into_option_contract into_option_run
  into_option_sample :=
  ProgramOption.intoOptionExecution

theorem into_option_satisfiable : FamilySatisfiable into_option_contract into_option_sample :=
  ProgramOption.intoOptionSatisfiable


end Solanalib.Specs.SolanaProgram.program_option.COption

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.program_option.COption

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Compare the borrowed query with the payload in the source direction. -/
abbrev contains_contract : Family := ProgramOption.containsFamily

/-- Exact relational reference at every source interpretation. -/
abbrev contains_run : FamilyRun contains_contract := ProgramOption.containsRun

theorem contains_reference : FamilyReference contains_contract contains_run :=
  ProgramOption.containsReference

/-- Closed registered source-type and callback sample. -/
abbrev contains_sample := ProgramOption.containsSample

theorem contains_has_execution : FamilyHasExecution contains_contract contains_run contains_sample
  :=
  ProgramOption.containsExecution

theorem contains_satisfiable : FamilySatisfiable contains_contract contains_sample :=
  ProgramOption.containsSatisfiable

/-- Inspect only the absent discriminant. -/
abbrev is_none_contract : Family := ProgramOption.isNoneFamily

/-- Exact relational reference at every source interpretation. -/
abbrev is_none_run : FamilyRun is_none_contract := ProgramOption.isNoneRun

theorem is_none_reference : FamilyReference is_none_contract is_none_run :=
  ProgramOption.isNoneReference

/-- Closed registered source-type and callback sample. -/
abbrev is_none_sample := ProgramOption.isNoneSample

theorem is_none_has_execution : FamilyHasExecution is_none_contract is_none_run is_none_sample :=
  ProgramOption.isNoneExecution

theorem is_none_satisfiable : FamilySatisfiable is_none_contract is_none_sample :=
  ProgramOption.isNoneSatisfiable

/-- Call Default only on None and preserve all of its effects and exits. -/
abbrev unwrap_or_default_contract : Family := ProgramOption.unwrapOrDefaultFamily

/-- Exact relational reference at every source interpretation. -/
abbrev unwrap_or_default_run : FamilyRun unwrap_or_default_contract :=
  ProgramOption.unwrapOrDefaultRun

theorem unwrap_or_default_reference : FamilyReference unwrap_or_default_contract
  unwrap_or_default_run :=
  ProgramOption.unwrapOrDefaultReference

/-- Closed registered source-type and callback sample. -/
abbrev unwrap_or_default_sample := ProgramOption.unwrapOrDefaultSample

theorem unwrap_or_default_has_execution : FamilyHasExecution unwrap_or_default_contract
  unwrap_or_default_run unwrap_or_default_sample :=
  ProgramOption.unwrapOrDefaultExecution

theorem unwrap_or_default_satisfiable : FamilySatisfiable unwrap_or_default_contract
  unwrap_or_default_sample :=
  ProgramOption.unwrapOrDefaultSatisfiable

end Solanalib.Specs.SolanaProgram.program_option.COption
