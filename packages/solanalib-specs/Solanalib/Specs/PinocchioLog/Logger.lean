/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.FixedLoggerAppend
public import Solanalib.Specs.Core.RawMemory
public import Solanalib.Specs.Core.RawRuntimeSample
public import Solanalib.Specs.Core.RawState

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.PinocchioLog.logger.Logger

open Solanalib.Contracts.Model Solanalib.Specs.Core

def default_contract := FixedLogger.defaultFamily
def default_run := FixedLogger.defaultRun
def default_sample := FixedLogger.defaultSample
theorem default_reference : FamilyReference default_contract default_run :=
  FixedLogger.default_reference
theorem default_hasExecution : FamilyHasExecution default_contract default_run default_sample :=
  FixedLogger.default_hasExecution
theorem default_satisfiable : FamilySatisfiable default_contract default_sample :=
  default_hasExecution.satisfiable

def append_contract := FixedLogger.appendFamily
def append_run := FixedLogger.appendRun
def append_sample := FixedLogger.appendSample
theorem append_reference : FamilyReference append_contract append_run :=
  FixedLogger.append_reference
theorem append_hasExecution : FamilyHasExecution append_contract append_run append_sample :=
  FixedLogger.append_hasExecution
theorem append_satisfiable : FamilySatisfiable append_contract append_sample :=
  append_hasExecution.satisfiable

def log_contract := FixedLogger.logFamily
def log_run := FixedLogger.logRun
def log_sample := FixedLogger.logSample
theorem log_reference : FamilyReference log_contract log_run := FixedLogger.log_reference
theorem log_hasExecution : FamilyHasExecution log_contract log_run log_sample :=
  FixedLogger.log_hasExecution
theorem log_satisfiable : FamilySatisfiable log_contract log_sample := log_hasExecution.satisfiable

end Solanalib.Specs.PinocchioLog.logger.Logger

namespace Solanalib.Specs.PinocchioLog.logger.syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime

/-- Complete request/output contract for `sol_memcpy_`. -/
def sol_memcpy__contract : Family := family RawMemory.copyStep
/-- The unchanged runtime operation as the mathematical reference. -/
def sol_memcpy__run : FamilyRun sol_memcpy__contract := run RawMemory.copyStep
/-- Correctness at every fixed runtime invocation. -/
theorem sol_memcpy__reference : FamilyReference sol_memcpy__contract sol_memcpy__run :=
  reference RawMemory.copyStep
/-- A closed, nonempty runtime interpretation. -/
def sol_memcpy__sample : sol_memcpy__contract.Index := Sample.index
/-- A concrete successful execution, including output bytes and the after-state. -/
theorem sol_memcpy__has_execution :
    FamilyHasExecution sol_memcpy__contract sol_memcpy__run sol_memcpy__sample :=
  ⟨Sample.state, ⟨256, 512, [1, 2, 3]⟩, .returned ⟨0, [[1, 2, 3]]⟩ (Sample.state), trivial, rfl⟩
/-- The successful execution witnesses satisfiable admission. -/
theorem sol_memcpy__satisfiable : FamilySatisfiable sol_memcpy__contract sol_memcpy__sample :=
  sol_memcpy__has_execution.satisfiable

end Solanalib.Specs.PinocchioLog.logger.syscalls

namespace Solanalib.Specs.PinocchioLog.logger.syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime

/-- Complete request/output contract for `sol_memset_`. -/
def sol_memset__contract : Family := family RawMemory.setStep
/-- The unchanged runtime operation as the mathematical reference. -/
def sol_memset__run : FamilyRun sol_memset__contract := run RawMemory.setStep
/-- Correctness at every fixed runtime invocation. -/
theorem sol_memset__reference : FamilyReference sol_memset__contract sol_memset__run :=
  reference RawMemory.setStep
/-- A closed, nonempty runtime interpretation. -/
def sol_memset__sample : sol_memset__contract.Index := Sample.index
/-- A concrete successful execution, including output bytes and the after-state. -/
theorem sol_memset__has_execution :
    FamilyHasExecution sol_memset__contract sol_memset__run sol_memset__sample :=
  ⟨Sample.state, ⟨42, 3⟩, .returned ⟨0, [[42, 42, 42]]⟩ (Sample.state), trivial, rfl⟩
/-- The successful execution witnesses satisfiable admission. -/
theorem sol_memset__satisfiable : FamilySatisfiable sol_memset__contract sol_memset__sample :=
  sol_memset__has_execution.satisfiable

end Solanalib.Specs.PinocchioLog.logger.syscalls
