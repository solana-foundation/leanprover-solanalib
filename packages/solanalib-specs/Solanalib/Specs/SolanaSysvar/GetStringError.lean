/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.SysvarSdkLegacy

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaSysvar

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace clock.Clock.string_error

def get_contract : Family := Sysvar.Legacy.family .split222 (⟨.typed .clock, some Sysvar.zeroClock⟩
  : Sysvar.ReadRequest _)
def get_run : FamilyRun get_contract := Sysvar.Legacy.reference .split222 (⟨.typed .clock, some
  Sysvar.zeroClock⟩ : Sysvar.ReadRequest _)
def get_sample : get_contract.Index := Sysvar.Legacy.sample Sysvar.zeroClock

theorem get_reference : FamilyReference get_contract get_run :=
  Sysvar.Legacy.reference_correct .split222 (⟨.typed .clock, some Sysvar.zeroClock⟩ :
    Sysvar.ReadRequest _)

theorem get_hasExecution :
    FamilyHasExecution get_contract get_run get_sample :=
  Sysvar.Legacy.sample_hasExecution .split222 (⟨.typed .clock, some Sysvar.zeroClock⟩ :
    Sysvar.ReadRequest _) Sysvar.zeroClock

theorem get_satisfiable : FamilySatisfiable get_contract get_sample :=
  get_hasExecution.satisfiable

end clock.Clock.string_error

namespace rent.Rent.string_error

def get_contract : Family := Sysvar.Legacy.family .split222 (⟨.typed .rent, some
  Sysvar.defaultRent300⟩ : Sysvar.ReadRequest _)
def get_run : FamilyRun get_contract := Sysvar.Legacy.reference .split222 (⟨.typed .rent, some
  Sysvar.defaultRent300⟩ : Sysvar.ReadRequest _)
def get_sample : get_contract.Index := Sysvar.Legacy.sample Sysvar.defaultRent300

theorem get_reference : FamilyReference get_contract get_run :=
  Sysvar.Legacy.reference_correct .split222 (⟨.typed .rent, some Sysvar.defaultRent300⟩ :
    Sysvar.ReadRequest _)

theorem get_hasExecution :
    FamilyHasExecution get_contract get_run get_sample :=
  Sysvar.Legacy.sample_hasExecution .split222 (⟨.typed .rent, some Sysvar.defaultRent300⟩ :
    Sysvar.ReadRequest _) Sysvar.defaultRent300

theorem get_satisfiable : FamilySatisfiable get_contract get_sample :=
  get_hasExecution.satisfiable

end rent.Rent.string_error


end Solanalib.Specs.SolanaSysvar
