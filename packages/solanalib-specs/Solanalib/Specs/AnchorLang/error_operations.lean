/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOperationsWitnesses
public import Solanalib.Specs.Core.AnchorErrorOperationsEquality

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! These boxed annotation families retain a generic complete ProgramError
payload and the raw ordered primitive relation. The inherited modern
families have different readiness premises and ownership postconditions;
the individual `Ops.fromOwned` translation does not equate them. -/

namespace Solanalib.Specs.AnchorLang.error.Error.GenericProgram

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorErrorOperations

/-- Exact boxed error representation; moved payloads and any replaced diagnostic owners are
preserved through the explicit primitive operations. -/
def with_pubkeys_contract : Family := select (pubkeysFamily) (fun types : Types => types.storage =
  .boxed)
def with_pubkeys_run : FamilyRun with_pubkeys_contract := selectRun (pubkeysFamily) (fun types :
  Types => types.storage = .boxed) (pubkeysRun)
def with_pubkeys_sample : with_pubkeys_contract.Index := ⟨sampleAt .boxed, rfl⟩
theorem with_pubkeys_reference : FamilyReference with_pubkeys_contract with_pubkeys_run :=
  select_reference _ _ _ (pubkeys_reference)
theorem with_pubkeys_has_execution :
    FamilyHasExecution with_pubkeys_contract with_pubkeys_run with_pubkeys_sample :=
  select_execution _ _ _ _ rfl (pubkeys_executionAt .boxed)
theorem with_pubkeys_satisfiable : FamilySatisfiable with_pubkeys_contract with_pubkeys_sample :=
  with_pubkeys_has_execution.satisfiable

/-- Generic callback conversion and source-ordered cleanup for the boxed receiver. Finite unwind and
terminal paths retain the actual dependency states. -/
def with_account_name_contract : Family := select (nameFamily) (fun types : NameTypes =>
  types.storage = .boxed)
def with_account_name_run : FamilyRun with_account_name_contract := selectRun (nameFamily) (fun
  types : NameTypes => types.storage = .boxed) (nameRun)
def with_account_name_sample : with_account_name_contract.Index := ⟨nameSampleAt .boxed, rfl⟩
theorem with_account_name_reference : FamilyReference with_account_name_contract
  with_account_name_run :=
  select_reference _ _ _ (name_reference)
theorem with_account_name_has_execution :
    FamilyHasExecution with_account_name_contract with_account_name_run with_account_name_sample :=
  select_execution _ _ _ _ rfl (name_executionAt .boxed)
theorem with_account_name_satisfiable : FamilySatisfiable with_account_name_contract
  with_account_name_sample :=
  with_account_name_has_execution.satisfiable

/-- Generic callback conversion and source-ordered cleanup for the boxed receiver. Finite unwind and
terminal paths retain the actual dependency states. -/
def with_values_contract : Family := select (valuesFamily) (fun types : ValuesTypes =>
  types.storage = .boxed)
def with_values_run : FamilyRun with_values_contract := selectRun (valuesFamily) (fun types :
  ValuesTypes => types.storage = .boxed) (valuesRun)
def with_values_sample : with_values_contract.Index := ⟨valuesSampleAt .boxed, rfl⟩
theorem with_values_reference : FamilyReference with_values_contract with_values_run :=
  select_reference _ _ _ (values_reference)
theorem with_values_has_execution :
    FamilyHasExecution with_values_contract with_values_run with_values_sample :=
  select_execution _ _ _ _ rfl (values_executionAt .boxed)
theorem with_values_satisfiable : FamilySatisfiable with_values_contract with_values_sample :=
  with_values_has_execution.satisfiable


end Solanalib.Specs.AnchorLang.error.Error.GenericProgram

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.error.Error

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorErrorOperations

/-- Borrow both actual boxed payloads. Anchor errors compare only their numeric code; program errors
compare their complete old enum, including Borsh String contents. -/
def eq_contract : Family := equalityFamily
def eq_run : FamilyRun eq_contract := equalityRun
def eq_sample : eq_contract.Index := equalitySample
theorem eq_reference : FamilyReference eq_contract eq_run :=
  equality_reference
theorem eq_has_execution :
    FamilyHasExecution eq_contract eq_run eq_sample :=
  equality_hasExecution
theorem eq_satisfiable : FamilySatisfiable eq_contract eq_sample :=
  eq_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.error.Error

namespace Solanalib.Specs.AnchorLang.error.Error

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorErrorOperations

/-- Consume the complete IO-to-ProgramError dependency, including custom Display or Drop unwind,
then allocate the Anchor box only after a normal conversion. -/
def from_io_error_contract : Family := select (ioFamily) (fun types : IoTypes => types.storage =
  .boxed)
def from_io_error_run : FamilyRun from_io_error_contract := selectRun (ioFamily) (fun types :
  IoTypes => types.storage = .boxed) (ioRun)
def from_io_error_sample : from_io_error_contract.Index := ⟨ioSample, rfl⟩
theorem from_io_error_reference : FamilyReference from_io_error_contract from_io_error_run :=
  select_reference _ _ _ (io_reference)
theorem from_io_error_has_execution :
    FamilyHasExecution from_io_error_contract from_io_error_run from_io_error_sample :=
  select_execution _ _ _ _ rfl (io_hasExecution)
theorem from_io_error_satisfiable : FamilySatisfiable from_io_error_contract from_io_error_sample :=
  from_io_error_has_execution.satisfiable


end Solanalib.Specs.AnchorLang.error.Error

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.error.Error

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorErrorOperations

/-- Exact inline error representation; moved payloads and any replaced diagnostic owners are
preserved through the explicit primitive operations. -/
def from_anchor_error_inline_contract : Family := select (fromAnchorFamily) (fun types : Types =>
  types.storage = .inline)
def from_anchor_error_inline_run : FamilyRun from_anchor_error_inline_contract := selectRun
  (fromAnchorFamily) (fun types : Types => types.storage = .inline) (fromAnchorRun)
def from_anchor_error_inline_sample : from_anchor_error_inline_contract.Index := ⟨sampleAt .inline,
  rfl⟩
theorem from_anchor_error_inline_reference : FamilyReference from_anchor_error_inline_contract
  from_anchor_error_inline_run :=
  select_reference _ _ _ (fromAnchor_reference)
theorem from_anchor_error_inline_has_execution :
    FamilyHasExecution from_anchor_error_inline_contract from_anchor_error_inline_run
      from_anchor_error_inline_sample :=
  select_execution _ _ _ _ rfl (fromAnchor_executionAt .inline)
theorem from_anchor_error_inline_satisfiable : FamilySatisfiable from_anchor_error_inline_contract
  from_anchor_error_inline_sample :=
  from_anchor_error_inline_has_execution.satisfiable

/-- Exact inline error representation; moved payloads and any replaced diagnostic owners are
preserved through the explicit primitive operations. -/
def from_program_error_inline_contract : Family := select (fromProgramFamily) (fun types : Types =>
  types.storage = .inline)
def from_program_error_inline_run : FamilyRun from_program_error_inline_contract := selectRun
  (fromProgramFamily) (fun types : Types => types.storage = .inline) (fromProgramRun)
def from_program_error_inline_sample : from_program_error_inline_contract.Index := ⟨sampleAt
  .inline, rfl⟩
theorem from_program_error_inline_reference : FamilyReference from_program_error_inline_contract
  from_program_error_inline_run :=
  select_reference _ _ _ (fromProgram_reference)
theorem from_program_error_inline_has_execution :
    FamilyHasExecution from_program_error_inline_contract from_program_error_inline_run
      from_program_error_inline_sample :=
  select_execution _ _ _ _ rfl (fromProgram_executionAt .inline)
theorem from_program_error_inline_satisfiable : FamilySatisfiable
  from_program_error_inline_contract from_program_error_inline_sample :=
  from_program_error_inline_has_execution.satisfiable

/-- Generic callback conversion and source-ordered cleanup for the inline receiver. Finite unwind
and terminal paths retain the actual dependency states. -/
def with_account_name_inline_contract : Family := select (nameFamily) (fun types : NameTypes =>
  types.storage = .inline)
def with_account_name_inline_run : FamilyRun with_account_name_inline_contract := selectRun
  (nameFamily) (fun types : NameTypes => types.storage = .inline) (nameRun)
def with_account_name_inline_sample : with_account_name_inline_contract.Index := ⟨nameSampleAt
  .inline, rfl⟩
theorem with_account_name_inline_reference : FamilyReference with_account_name_inline_contract
  with_account_name_inline_run :=
  select_reference _ _ _ (name_reference)
theorem with_account_name_inline_has_execution :
    FamilyHasExecution with_account_name_inline_contract with_account_name_inline_run
      with_account_name_inline_sample :=
  select_execution _ _ _ _ rfl (name_executionAt .inline)
theorem with_account_name_inline_satisfiable : FamilySatisfiable with_account_name_inline_contract
  with_account_name_inline_sample :=
  with_account_name_inline_has_execution.satisfiable

/-- Exact inline error representation; moved payloads and any replaced diagnostic owners are
preserved through the explicit primitive operations. -/
def with_pubkeys_inline_contract : Family := select (pubkeysFamily) (fun types : Types =>
  types.storage = .inline)
def with_pubkeys_inline_run : FamilyRun with_pubkeys_inline_contract := selectRun (pubkeysFamily)
  (fun types : Types => types.storage = .inline) (pubkeysRun)
def with_pubkeys_inline_sample : with_pubkeys_inline_contract.Index := ⟨sampleAt .inline, rfl⟩
theorem with_pubkeys_inline_reference : FamilyReference with_pubkeys_inline_contract
  with_pubkeys_inline_run :=
  select_reference _ _ _ (pubkeys_reference)
theorem with_pubkeys_inline_has_execution :
    FamilyHasExecution with_pubkeys_inline_contract with_pubkeys_inline_run
      with_pubkeys_inline_sample :=
  select_execution _ _ _ _ rfl (pubkeys_executionAt .inline)
theorem with_pubkeys_inline_satisfiable : FamilySatisfiable with_pubkeys_inline_contract
  with_pubkeys_inline_sample :=
  with_pubkeys_inline_has_execution.satisfiable

/-- Exact inline error representation; moved payloads and any replaced diagnostic owners are
preserved through the explicit primitive operations. -/
def with_source_inline_contract : Family := select (sourceFamily) (fun types : Types =>
  types.storage = .inline)
def with_source_inline_run : FamilyRun with_source_inline_contract := selectRun (sourceFamily) (fun
  types : Types => types.storage = .inline) (sourceRun)
def with_source_inline_sample : with_source_inline_contract.Index := ⟨sampleAt .inline, rfl⟩
theorem with_source_inline_reference : FamilyReference with_source_inline_contract
  with_source_inline_run :=
  select_reference _ _ _ (source_reference)
theorem with_source_inline_has_execution :
    FamilyHasExecution with_source_inline_contract with_source_inline_run with_source_inline_sample
      :=
  select_execution _ _ _ _ rfl (source_executionAt .inline)
theorem with_source_inline_satisfiable : FamilySatisfiable with_source_inline_contract
  with_source_inline_sample :=
  with_source_inline_has_execution.satisfiable

/-- Generic callback conversion and source-ordered cleanup for the inline receiver. Finite unwind
and terminal paths retain the actual dependency states. -/
def with_values_inline_contract : Family := select (valuesFamily) (fun types : ValuesTypes =>
  types.storage = .inline)
def with_values_inline_run : FamilyRun with_values_inline_contract := selectRun (valuesFamily) (fun
  types : ValuesTypes => types.storage = .inline) (valuesRun)
def with_values_inline_sample : with_values_inline_contract.Index := ⟨valuesSampleAt .inline, rfl⟩
theorem with_values_inline_reference : FamilyReference with_values_inline_contract
  with_values_inline_run :=
  select_reference _ _ _ (values_reference)
theorem with_values_inline_has_execution :
    FamilyHasExecution with_values_inline_contract with_values_inline_run with_values_inline_sample
      :=
  select_execution _ _ _ _ rfl (values_executionAt .inline)
theorem with_values_inline_satisfiable : FamilySatisfiable with_values_inline_contract
  with_values_inline_sample :=
  with_values_inline_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.error.Error
