/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.SysvarSdk
public import Solanalib.Specs.SolanaRent.Rent

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaSysvar

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace clock.Clock

abbrev Value := Sysvar.Clock

def get_contract := Sysvar.getterFamily Sysvar.sdkClockConfig
def get_run := Sysvar.getterRun Sysvar.sdkClockConfig
def get_sample := Sysvar.getterSample Sysvar.zeroClock

theorem get_reference : FamilyReference get_contract get_run :=
  Sysvar.getter_reference Sysvar.sdkClockConfig

theorem get_hasExecution : FamilyHasExecution get_contract get_run get_sample :=
  Sysvar.getterSample_hasExecution Sysvar.sdkClockConfig Sysvar.zeroClock

theorem get_satisfiable : FamilySatisfiable get_contract get_sample :=
  get_hasExecution.satisfiable

end clock.Clock

namespace rent.Rent

abbrev Value := Solanalib.Specs.SolanaRent.Rent.Value

def get_contract := Sysvar.getterFamily Sysvar.sdkRentConfig
def get_run := Sysvar.getterRun Sysvar.sdkRentConfig
def get_sample := Sysvar.getterSample Sysvar.defaultRent300

theorem get_reference : FamilyReference get_contract get_run :=
  Sysvar.getter_reference Sysvar.sdkRentConfig

theorem get_hasExecution : FamilyHasExecution get_contract get_run get_sample :=
  Sysvar.getterSample_hasExecution Sysvar.sdkRentConfig Sysvar.defaultRent300

theorem get_satisfiable : FamilySatisfiable get_contract get_sample :=
  get_hasExecution.satisfiable

end rent.Rent

end Solanalib.Specs.SolanaSysvar
