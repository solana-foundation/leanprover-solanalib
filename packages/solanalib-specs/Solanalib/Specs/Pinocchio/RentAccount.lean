/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Pinocchio.Rent
public import Solanalib.Specs.Core.SysvarAccount

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate

open Solanalib.Contracts.Model Solanalib.Specs.Core

def from_account_view_contract :
    Solanalib.Contracts.Model AccountView.State AccountView.Handle (Except ProgramError.Value
      Value) :=
  .returning Sysvar.Rent111ReadReady
    (fun before handle value after =>
      after = before ∧ Sysvar.Rent111ReadResult before handle value)

def from_account_view_run := Sysvar.rent111FromAccount

theorem from_account_view_reference :
    from_account_view_contract.RealizedBy from_account_view_run := by
  intro before handle ready
  exact ⟨Sysvar.rent111FromAccount_preserves_state before handle,
    Sysvar.rent111FromAccount_read ready⟩

theorem from_account_view_hasExecution :
    from_account_view_contract.HasExecution (returnsOf from_account_view_run) :=
  ⟨Sysvar.Witness.singleAccount Sysvar.Witness.rentAccount, Sysvar.Witness.handle,
    .returned (.ok ⟨6960⟩) (Sysvar.Witness.singleAccount Sysvar.Witness.rentAccount),
    Sysvar.Witness.rentAccount_ready, rfl⟩

theorem from_account_view_satisfiable : from_account_view_contract.Satisfiable :=
  from_account_view_hasExecution.satisfiable

end Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate
