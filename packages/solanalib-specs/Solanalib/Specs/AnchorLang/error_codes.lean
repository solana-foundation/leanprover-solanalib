/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOperationsWitnesses
public import Solanalib.Specs.Core.AnchorErrorCodeTables

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.error

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorErrorOperations

namespace Error

/-- Convert only variants from this exact reviewed enum table, allocating the name and formatted
message in source order before constructing the selected error representation. -/
def from_error_code_contract : Family := select (codeFamily CodeTables.v0_32_1) (fun types : Types
  => types.storage = .boxed)
def from_error_code_run : FamilyRun from_error_code_contract := selectRun (codeFamily
  CodeTables.v0_32_1) (fun types : Types => types.storage = .boxed) (codeRun CodeTables.v0_32_1)
def from_error_code_sample : from_error_code_contract.Index := ⟨sampleAt .boxed, rfl⟩
theorem from_error_code_reference : FamilyReference from_error_code_contract from_error_code_run :=
  select_reference _ _ _ (code_reference CodeTables.v0_32_1)
theorem from_error_code_has_execution :
    FamilyHasExecution from_error_code_contract from_error_code_run from_error_code_sample :=
  select_execution _ _ _ _ rfl (code_executionAt .boxed CodeTables.v0_32_1 ⟨0, by decide⟩)
theorem from_error_code_satisfiable : FamilySatisfiable from_error_code_contract
  from_error_code_sample :=
  from_error_code_has_execution.satisfiable

end Error

namespace ErrorCode

/-- Allocate the exact name of the selected source enum variant; no unrelated error, formatting or
Box operation is required. -/
def name_contract : Family := codeNameFamily CodeTables.v0_32_1
def name_run : FamilyRun name_contract := codeNameRun CodeTables.v0_32_1
def name_sample : name_contract.Index := codeNameSample
theorem name_reference : FamilyReference name_contract name_run :=
  codeName_reference CodeTables.v0_32_1
theorem name_has_execution :
    FamilyHasExecution name_contract name_run name_sample :=
  codeName_hasExecution CodeTables.v0_32_1 ⟨0, by decide⟩
theorem name_satisfiable : FamilySatisfiable name_contract name_sample :=
  name_has_execution.satisfiable

end ErrorCode

end Solanalib.Specs.AnchorLang.error

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.error

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorErrorOperations

namespace Error

/-- Convert only variants from this exact reviewed enum table, allocating the name and formatted
message in source order before constructing the selected error representation. -/
def from_error_code_account_migration_contract : Family := select (codeFamily CodeTables.v1_0_2)
  (fun types : Types => types.storage = .boxed)
def from_error_code_account_migration_run : FamilyRun from_error_code_account_migration_contract :=
  selectRun (codeFamily CodeTables.v1_0_2) (fun types : Types => types.storage = .boxed) (codeRun
  CodeTables.v1_0_2)
def from_error_code_account_migration_sample : from_error_code_account_migration_contract.Index :=
  ⟨sampleAt .boxed, rfl⟩
theorem from_error_code_account_migration_reference : FamilyReference
  from_error_code_account_migration_contract from_error_code_account_migration_run :=
  select_reference _ _ _ (code_reference CodeTables.v1_0_2)
theorem from_error_code_account_migration_has_execution :
    FamilyHasExecution from_error_code_account_migration_contract
      from_error_code_account_migration_run from_error_code_account_migration_sample :=
  select_execution _ _ _ _ rfl (code_executionAt .boxed CodeTables.v1_0_2 ⟨0, by decide⟩)
theorem from_error_code_account_migration_satisfiable : FamilySatisfiable
  from_error_code_account_migration_contract from_error_code_account_migration_sample :=
  from_error_code_account_migration_has_execution.satisfiable

end Error

namespace ErrorCode

/-- Allocate the exact name of the selected source enum variant; no unrelated error, formatting or
Box operation is required. -/
def name_account_migration_contract : Family := codeNameFamily CodeTables.v1_0_2
def name_account_migration_run : FamilyRun name_account_migration_contract := codeNameRun
  CodeTables.v1_0_2
def name_account_migration_sample : name_account_migration_contract.Index := codeNameSample
theorem name_account_migration_reference : FamilyReference name_account_migration_contract
  name_account_migration_run :=
  codeName_reference CodeTables.v1_0_2
theorem name_account_migration_has_execution :
    FamilyHasExecution name_account_migration_contract name_account_migration_run
      name_account_migration_sample :=
  codeName_hasExecution CodeTables.v1_0_2 ⟨0, by decide⟩
theorem name_account_migration_satisfiable : FamilySatisfiable name_account_migration_contract
  name_account_migration_sample :=
  name_account_migration_has_execution.satisfiable

end ErrorCode

end Solanalib.Specs.AnchorLang.error

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.error

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorErrorOperations

namespace Error

/-- Convert only variants from this exact reviewed enum table, allocating the name and formatted
message in source order before constructing the selected error representation. -/
def from_legacy_error_code_contract : Family := select (codeFamily CodeTables.v0_29_0) (fun types :
  Types => types.storage = .boxed)
def from_legacy_error_code_run : FamilyRun from_legacy_error_code_contract := selectRun (codeFamily
  CodeTables.v0_29_0) (fun types : Types => types.storage = .boxed) (codeRun CodeTables.v0_29_0)
def from_legacy_error_code_sample : from_legacy_error_code_contract.Index := ⟨sampleAt .boxed, rfl⟩
theorem from_legacy_error_code_reference : FamilyReference from_legacy_error_code_contract
  from_legacy_error_code_run :=
  select_reference _ _ _ (code_reference CodeTables.v0_29_0)
theorem from_legacy_error_code_has_execution :
    FamilyHasExecution from_legacy_error_code_contract from_legacy_error_code_run
      from_legacy_error_code_sample :=
  select_execution _ _ _ _ rfl (code_executionAt .boxed CodeTables.v0_29_0 ⟨0, by decide⟩)
theorem from_legacy_error_code_satisfiable : FamilySatisfiable from_legacy_error_code_contract
  from_legacy_error_code_sample :=
  from_legacy_error_code_has_execution.satisfiable

end Error

namespace ErrorCode

/-- Allocate the exact name of the selected source enum variant; no unrelated error, formatting or
Box operation is required. -/
def name_legacy_contract : Family := codeNameFamily CodeTables.v0_29_0
def name_legacy_run : FamilyRun name_legacy_contract := codeNameRun CodeTables.v0_29_0
def name_legacy_sample : name_legacy_contract.Index := codeNameSample
theorem name_legacy_reference : FamilyReference name_legacy_contract name_legacy_run :=
  codeName_reference CodeTables.v0_29_0
theorem name_legacy_has_execution :
    FamilyHasExecution name_legacy_contract name_legacy_run name_legacy_sample :=
  codeName_hasExecution CodeTables.v0_29_0 ⟨0, by decide⟩
theorem name_legacy_satisfiable : FamilySatisfiable name_legacy_contract name_legacy_sample :=
  name_legacy_has_execution.satisfiable

end ErrorCode

end Solanalib.Specs.AnchorLang.error

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.error.Error

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorErrorOperations

/-- Convert only variants from this exact reviewed enum table, allocating the name and formatted
message in source order before constructing the selected error representation. -/
def from_error_code_inline_contract : Family := select (codeFamily CodeTables.v0_27_0) (fun types :
  Types => types.storage = .inline)
def from_error_code_inline_run : FamilyRun from_error_code_inline_contract := selectRun (codeFamily
  CodeTables.v0_27_0) (fun types : Types => types.storage = .inline) (codeRun CodeTables.v0_27_0)
def from_error_code_inline_sample : from_error_code_inline_contract.Index := ⟨sampleAt .inline, rfl⟩
theorem from_error_code_inline_reference : FamilyReference from_error_code_inline_contract
  from_error_code_inline_run :=
  select_reference _ _ _ (code_reference CodeTables.v0_27_0)
theorem from_error_code_inline_has_execution :
    FamilyHasExecution from_error_code_inline_contract from_error_code_inline_run
      from_error_code_inline_sample :=
  select_execution _ _ _ _ rfl (code_executionAt .inline CodeTables.v0_27_0 ⟨0, by decide⟩)
theorem from_error_code_inline_satisfiable : FamilySatisfiable from_error_code_inline_contract
  from_error_code_inline_sample :=
  from_error_code_inline_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.error.Error

namespace Solanalib.Specs.AnchorLang.error.ErrorCode

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorErrorOperations

/-- Allocate the exact name of the selected source enum variant; no unrelated error, formatting or
Box operation is required. -/
def name_pre_token_program_checks_contract : Family := codeNameFamily CodeTables.v0_27_0
def name_pre_token_program_checks_run : FamilyRun name_pre_token_program_checks_contract :=
  codeNameRun CodeTables.v0_27_0
def name_pre_token_program_checks_sample : name_pre_token_program_checks_contract.Index :=
  codeNameSample
theorem name_pre_token_program_checks_reference : FamilyReference
  name_pre_token_program_checks_contract name_pre_token_program_checks_run :=
  codeName_reference CodeTables.v0_27_0
theorem name_pre_token_program_checks_has_execution :
    FamilyHasExecution name_pre_token_program_checks_contract name_pre_token_program_checks_run
      name_pre_token_program_checks_sample :=
  codeName_hasExecution CodeTables.v0_27_0 ⟨0, by decide⟩
theorem name_pre_token_program_checks_satisfiable : FamilySatisfiable
  name_pre_token_program_checks_contract name_pre_token_program_checks_sample :=
  name_pre_token_program_checks_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.error.ErrorCode
