/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOperationsLogWitnesses

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.error.Error

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorErrorOperations

/-- Log the exact origin-dependent format and comparisons in order. Legacy Borsh status conversion
retains its String clone/drop; host logging unwind still drops the temporary format String. -/
def log_contract : Family := select (logFamily (.legacy .programError2_2_2)) (fun types : LogTypes
  (.legacy .programError2_2_2) => types.storage = .boxed)
def log_run : FamilyRun log_contract := selectRun (logFamily (.legacy .programError2_2_2)) (fun
  types : LogTypes (.legacy .programError2_2_2) => types.storage = .boxed) (logRun)
def log_sample : log_contract.Index := ⟨logSampleAt (.legacy .programError2_2_2) .boxed, rfl⟩
theorem log_reference : FamilyReference log_contract log_run :=
  select_reference _ _ _ (AnchorErrorOperations.log_reference (.legacy .programError2_2_2))
theorem log_has_execution :
    FamilyHasExecution log_contract log_run log_sample :=
  select_execution _ _ _ _ rfl (log_executionAt (.legacy .programError2_2_2) .boxed)
theorem log_satisfiable : FamilySatisfiable log_contract log_sample :=
  log_has_execution.satisfiable


end Solanalib.Specs.AnchorLang.error.Error

namespace Solanalib.Specs.AnchorLang.error.Error

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorErrorOperations

def log_modern_contract : Family := select (logFamily .modern) (fun types : LogTypes .modern =>
  types.storage = .boxed)
def log_modern_run : FamilyRun log_modern_contract := selectRun (logFamily .modern) (fun types :
  LogTypes .modern => types.storage = .boxed) (logRun)
def log_modern_sample : log_modern_contract.Index := ⟨logSampleAt .modern .boxed, rfl⟩
theorem log_modern_reference : FamilyReference log_modern_contract log_modern_run :=
  select_reference _ _ _ (AnchorErrorOperations.log_reference .modern)
theorem log_modern_has_execution :
    FamilyHasExecution log_modern_contract log_modern_run log_modern_sample :=
  select_execution _ _ _ _ rfl (log_executionAt .modern .boxed)
theorem log_modern_satisfiable : FamilySatisfiable log_modern_contract log_modern_sample :=
  log_modern_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.error.Error

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.error.Error

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorErrorOperations

/-- Log the exact origin-dependent format and comparisons in order. Legacy Borsh status conversion
retains its String clone/drop; host logging unwind still drops the temporary format String. -/
def log_legacy_program_contract : Family := select (logFamily (.legacy .solana1_18_26)) (fun types
  : LogTypes (.legacy .solana1_18_26) => types.storage = .boxed)
def log_legacy_program_run : FamilyRun log_legacy_program_contract := selectRun (logFamily (.legacy
  .solana1_18_26)) (fun types : LogTypes (.legacy .solana1_18_26) => types.storage = .boxed)
  (logRun)
def log_legacy_program_sample : log_legacy_program_contract.Index := ⟨logSampleAt (.legacy
  .solana1_18_26) .boxed, rfl⟩
theorem log_legacy_program_reference : FamilyReference log_legacy_program_contract
  log_legacy_program_run :=
  select_reference _ _ _ (AnchorErrorOperations.log_reference (.legacy .solana1_18_26))
theorem log_legacy_program_has_execution :
    FamilyHasExecution log_legacy_program_contract log_legacy_program_run log_legacy_program_sample
      :=
  select_execution _ _ _ _ rfl (log_executionAt (.legacy .solana1_18_26) .boxed)
theorem log_legacy_program_satisfiable : FamilySatisfiable log_legacy_program_contract
  log_legacy_program_sample :=
  log_legacy_program_has_execution.satisfiable


end Solanalib.Specs.AnchorLang.error.Error

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.error.Error

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorErrorOperations

/-- Log the exact origin-dependent format and comparisons in order. Legacy Borsh status conversion
retains its String clone/drop; host logging unwind still drops the temporary format String. -/
def log_inline_contract : Family := select (logFamily (.legacy .solana1_15_2)) (fun types :
  LogTypes (.legacy .solana1_15_2) => types.storage = .inline)
def log_inline_run : FamilyRun log_inline_contract := selectRun (logFamily (.legacy .solana1_15_2))
  (fun types : LogTypes (.legacy .solana1_15_2) => types.storage = .inline) (logRun)
def log_inline_sample : log_inline_contract.Index := ⟨logSampleAt (.legacy .solana1_15_2) .inline,
  rfl⟩
theorem log_inline_reference : FamilyReference log_inline_contract log_inline_run :=
  select_reference _ _ _ (AnchorErrorOperations.log_reference (.legacy .solana1_15_2))
theorem log_inline_has_execution :
    FamilyHasExecution log_inline_contract log_inline_run log_inline_sample :=
  select_execution _ _ _ _ rfl (log_executionAt (.legacy .solana1_15_2) .inline)
theorem log_inline_satisfiable : FamilySatisfiable log_inline_contract log_inline_sample :=
  log_inline_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.error.Error
