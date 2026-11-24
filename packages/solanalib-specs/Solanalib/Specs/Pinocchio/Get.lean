/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.SysvarRent102Getter
public import Solanalib.Specs.Core.Sysvar
public import Solanalib.Specs.Core.RawMemory
public import Solanalib.Specs.Core.RawRuntimeSample
public import Solanalib.Specs.Core.RawState

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Pinocchio.sysvars

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace clock.Clock

abbrev Value := Sysvar.Clock

def get_contract := Sysvar.getterFamily Sysvar.pinClockConfig
def get_run := Sysvar.getterRun Sysvar.pinClockConfig
def get_sample := Sysvar.getterSample Sysvar.zeroClock

theorem get_reference : FamilyReference get_contract get_run :=
  Sysvar.getter_reference Sysvar.pinClockConfig

theorem get_hasExecution : FamilyHasExecution get_contract get_run get_sample :=
  Sysvar.getterSample_hasExecution Sysvar.pinClockConfig Sysvar.zeroClock

theorem get_satisfiable : FamilySatisfiable get_contract get_sample :=
  get_hasExecution.satisfiable

end clock.Clock

namespace rent.Rent.threshold_rate

def get_contract := Sysvar.getterFamily Sysvar.pinRent102Config
def get_run := Sysvar.getterRun Sysvar.pinRent102Config
def get_sample := Sysvar.getterSample Sysvar.defaultRent300.prefix102

theorem get_reference : FamilyReference get_contract get_run :=
  Sysvar.getter_reference Sysvar.pinRent102Config

theorem get_hasExecution : FamilyHasExecution get_contract get_run get_sample :=
  Sysvar.getterSample_hasExecution Sysvar.pinRent102Config Sysvar.defaultRent300.prefix102

theorem get_satisfiable : FamilySatisfiable get_contract get_sample :=
  get_hasExecution.satisfiable

end rent.Rent.threshold_rate

end Solanalib.Specs.Pinocchio.sysvars

namespace Solanalib.Specs.Pinocchio.sysvars.clock.Clock

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Initialization admission preserves every finite provider execution;
the getter does not supply a successful syscall or provider termination. -/
theorem get_hasOutcome_iff (index : Sysvar.GetterIndex Value) (before : index.State)
    (ready : (get_contract.contract index).requires before ()) :
    (∃ outcome, get_run index before () outcome) ↔
      ∃ exit, index.read before (index.target, Sysvar.pinClockConfig.request) exit :=
  Sysvar.get_hasOutcome_iff Sysvar.pinClockConfig index before ready

end Solanalib.Specs.Pinocchio.sysvars.clock.Clock

namespace Solanalib.Specs.Pinocchio.sysvars.clock.Clock

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- 0.9.2 calls the dedicated syscall with an uninitialized destination and
folds every nonzero status into UnsupportedSysvar. It is not the generic
sol_get_sysvar configuration used by 0.10.2. -/
def dedicatedConfig : Sysvar.GetterConfig Sysvar.Clock where
  request := ⟨.typed .clock, none⟩
  valid := Sysvar.clockValid
  error := fun status => if status = 0 then none else some .unsupportedSysvar

def get_dedicated_contract := Sysvar.getterFamily dedicatedConfig
def get_dedicated_run := Sysvar.getterRun dedicatedConfig
def get_dedicated_sample := Sysvar.getterSample Sysvar.zeroClock
theorem get_dedicated_reference : FamilyReference get_dedicated_contract get_dedicated_run :=
  Sysvar.getter_reference dedicatedConfig
theorem get_dedicated_hasExecution : FamilyHasExecution get_dedicated_contract get_dedicated_run
  get_dedicated_sample :=
  Sysvar.getterSample_hasExecution dedicatedConfig Sysvar.zeroClock
theorem get_dedicated_satisfiable : FamilySatisfiable get_dedicated_contract get_dedicated_sample
  := get_dedicated_hasExecution.satisfiable

end Solanalib.Specs.Pinocchio.sysvars.clock.Clock

namespace Solanalib.Specs.Pinocchio.syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime

/-- Complete request/output contract for `sol_get_clock_sysvar`. -/
def sol_get_clock_sysvar_contract : Family := family (RawState.typedStep .clock)
/-- The unchanged runtime operation as the mathematical reference. -/
def sol_get_clock_sysvar_run : FamilyRun sol_get_clock_sysvar_contract := run (RawState.typedStep
  .clock)
/-- Correctness at every fixed runtime invocation. -/
theorem sol_get_clock_sysvar_reference : FamilyReference sol_get_clock_sysvar_contract
  sol_get_clock_sysvar_run :=
  reference (RawState.typedStep .clock)
/-- A closed, nonempty runtime interpretation. -/
def sol_get_clock_sysvar_sample : sol_get_clock_sysvar_contract.Index := Sample.index
/-- A concrete successful execution, including output bytes and the after-state. -/
theorem sol_get_clock_sysvar_has_execution :
    FamilyHasExecution sol_get_clock_sysvar_contract sol_get_clock_sysvar_run
      sol_get_clock_sysvar_sample :=
  ⟨Sample.state, (256 : Nat), .returned ⟨0, [Sample.sysvars.clock.encode]⟩ (Sample.state), trivial,
    rfl⟩
/-- The successful execution witnesses satisfiable admission. -/
theorem sol_get_clock_sysvar_satisfiable : FamilySatisfiable sol_get_clock_sysvar_contract
  sol_get_clock_sysvar_sample :=
  sol_get_clock_sysvar_has_execution.satisfiable

end Solanalib.Specs.Pinocchio.syscalls
