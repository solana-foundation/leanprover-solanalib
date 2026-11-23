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

namespace Solanalib.Specs.SolanaProgram

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace sysvar.clock.Clock

def get_contract : Family := Sysvar.Legacy.family .program118 (⟨.typed .clock, some
  Sysvar.zeroClock⟩ : Sysvar.ReadRequest _)
def get_run : FamilyRun get_contract := Sysvar.Legacy.reference .program118 (⟨.typed .clock, some
  Sysvar.zeroClock⟩ : Sysvar.ReadRequest _)
def get_sample : get_contract.Index := Sysvar.Legacy.sample Sysvar.zeroClock

theorem get_reference : FamilyReference get_contract get_run :=
  Sysvar.Legacy.reference_correct .program118 (⟨.typed .clock, some Sysvar.zeroClock⟩ :
    Sysvar.ReadRequest _)

theorem get_hasExecution :
    FamilyHasExecution get_contract get_run get_sample :=
  Sysvar.Legacy.sample_hasExecution .program118 (⟨.typed .clock, some Sysvar.zeroClock⟩ :
    Sysvar.ReadRequest _) Sysvar.zeroClock

theorem get_satisfiable : FamilySatisfiable get_contract get_sample :=
  get_hasExecution.satisfiable

end sysvar.clock.Clock

namespace sysvar.rent.Rent

def get_contract : Family := Sysvar.Legacy.family .program118 (⟨.typed .rent, some
  Sysvar.defaultRent300⟩ : Sysvar.ReadRequest _)
def get_run : FamilyRun get_contract := Sysvar.Legacy.reference .program118 (⟨.typed .rent, some
  Sysvar.defaultRent300⟩ : Sysvar.ReadRequest _)
def get_sample : get_contract.Index := Sysvar.Legacy.sample Sysvar.defaultRent300

theorem get_reference : FamilyReference get_contract get_run :=
  Sysvar.Legacy.reference_correct .program118 (⟨.typed .rent, some Sysvar.defaultRent300⟩ :
    Sysvar.ReadRequest _)

theorem get_hasExecution :
    FamilyHasExecution get_contract get_run get_sample :=
  Sysvar.Legacy.sample_hasExecution .program118 (⟨.typed .rent, some Sysvar.defaultRent300⟩ :
    Sysvar.ReadRequest _) Sysvar.defaultRent300

theorem get_satisfiable : FamilySatisfiable get_contract get_sample :=
  get_hasExecution.satisfiable

end sysvar.rent.Rent


end Solanalib.Specs.SolanaProgram

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.sysvar.rent.Rent

open Solanalib.Contracts.Model Solanalib.Specs.Core

def get_legacy_error_table_contract : Family := Sysvar.Legacy.family .program115 (⟨.typed .rent,
  some Sysvar.defaultRent300⟩ : Sysvar.ReadRequest _)
def get_legacy_error_table_run : FamilyRun get_legacy_error_table_contract :=
  Sysvar.Legacy.reference .program115 (⟨.typed .rent, some Sysvar.defaultRent300⟩ :
  Sysvar.ReadRequest _)
def get_legacy_error_table_sample : get_legacy_error_table_contract.Index := Sysvar.Legacy.sample
  Sysvar.defaultRent300

theorem get_legacy_error_table_reference : FamilyReference get_legacy_error_table_contract
  get_legacy_error_table_run :=
  Sysvar.Legacy.reference_correct .program115 (⟨.typed .rent, some Sysvar.defaultRent300⟩ :
    Sysvar.ReadRequest _)

theorem get_legacy_error_table_hasExecution :
    FamilyHasExecution get_legacy_error_table_contract get_legacy_error_table_run
      get_legacy_error_table_sample :=
  Sysvar.Legacy.sample_hasExecution .program115 (⟨.typed .rent, some Sysvar.defaultRent300⟩ :
    Sysvar.ReadRequest _) Sysvar.defaultRent300

theorem get_legacy_error_table_satisfiable : FamilySatisfiable get_legacy_error_table_contract
  get_legacy_error_table_sample :=
  get_legacy_error_table_hasExecution.satisfiable

end Solanalib.Specs.SolanaProgram.sysvar.rent.Rent
