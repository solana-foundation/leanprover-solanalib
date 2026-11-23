/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.EpochSchedule

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaSysvar.epoch_schedule.EpochSchedule

open Solanalib.Contracts.Model Solanalib.Specs.Core

def get_contract : Family := Sysvar.getterFamily EpochSchedule.getterConfig
def get_run : FamilyRun get_contract := Sysvar.getterRun EpochSchedule.getterConfig
def get_sample : get_contract.Index := Sysvar.getterSample EpochSchedule.defaultValue

theorem get_reference : FamilyReference get_contract get_run :=
  Sysvar.getter_reference EpochSchedule.getterConfig

theorem get_hasExecution :
    FamilyHasExecution get_contract get_run get_sample :=
  Sysvar.getterSample_hasExecution EpochSchedule.getterConfig EpochSchedule.defaultValue

theorem get_satisfiable : FamilySatisfiable get_contract get_sample :=
  get_hasExecution.satisfiable

end Solanalib.Specs.SolanaSysvar.epoch_schedule.EpochSchedule
