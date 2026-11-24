/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOperationsLogWitnesses
public import Solanalib.Specs.Core.AnchorErrorOperationsWitnesses
public import Solanalib.Specs.Core.AnchorErrorCodeTables

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! These operations belong to anchor-lang-error, with 1.1.2 as their inspected
reference. Catalog compatibility and the exact source-entry selections remain
separate from these complete mathematical families. -/

namespace Solanalib.Specs.AnchorLangError.Error

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorErrorOperations

/-- Log the exact origin-dependent format and comparisons in order for the
selected boxed modern ProgramError profile; logger unwind drops the temporary
format String. -/
def log_contract : Family := select (logFamily .modern) (fun types : LogTypes .modern =>
  types.storage = .boxed)
def log_run : FamilyRun log_contract := selectRun (logFamily .modern) (fun types : LogTypes .modern
  => types.storage = .boxed) (logRun)
def log_sample : log_contract.Index := ⟨logSampleAt .modern .boxed, rfl⟩
theorem log_reference : FamilyReference log_contract log_run :=
  select_reference _ _ _ (AnchorErrorOperations.log_reference .modern)
theorem log_has_execution :
    FamilyHasExecution log_contract log_run log_sample :=
  select_execution _ _ _ _ rfl (log_executionAt .modern .boxed)
theorem log_satisfiable : FamilySatisfiable log_contract log_sample :=
  log_has_execution.satisfiable


end Solanalib.Specs.AnchorLangError.Error

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLangError

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorErrorOperations

namespace Error

/-- Convert only variants from this exact reviewed enum table, allocating the name and formatted
message in source order before constructing the selected error representation. -/
def from_error_code_contract : Family := select (codeFamily CodeTables.v1_1_2) (fun types : Types
  => types.storage = .boxed)
def from_error_code_run : FamilyRun from_error_code_contract := selectRun (codeFamily
  CodeTables.v1_1_2) (fun types : Types => types.storage = .boxed) (codeRun CodeTables.v1_1_2)
def from_error_code_sample : from_error_code_contract.Index := ⟨sampleAt .boxed, rfl⟩
theorem from_error_code_reference : FamilyReference from_error_code_contract from_error_code_run :=
  select_reference _ _ _ (code_reference CodeTables.v1_1_2)
theorem from_error_code_has_execution :
    FamilyHasExecution from_error_code_contract from_error_code_run from_error_code_sample :=
  select_execution _ _ _ _ rfl (code_executionAt .boxed CodeTables.v1_1_2 ⟨0, by decide⟩)
theorem from_error_code_satisfiable : FamilySatisfiable from_error_code_contract
  from_error_code_sample :=
  from_error_code_has_execution.satisfiable

end Error

namespace ErrorCode

/-- Allocate the exact name of the selected source enum variant; no unrelated error, formatting or
Box operation is required. -/
def name_contract : Family := codeNameFamily CodeTables.v1_1_2
def name_run : FamilyRun name_contract := codeNameRun CodeTables.v1_1_2
def name_sample : name_contract.Index := codeNameSample
theorem name_reference : FamilyReference name_contract name_run :=
  codeName_reference CodeTables.v1_1_2
theorem name_has_execution :
    FamilyHasExecution name_contract name_run name_sample :=
  codeName_hasExecution CodeTables.v1_1_2 ⟨0, by decide⟩
theorem name_satisfiable : FamilySatisfiable name_contract name_sample :=
  name_has_execution.satisfiable

end ErrorCode

end Solanalib.Specs.AnchorLangError

namespace Solanalib.Specs.AnchorLangError.Error

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorErrorOperations

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

end Solanalib.Specs.AnchorLangError.Error
