/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Specs.Core.SysvarRent102
public import Solanalib.Specs.Core.SysvarRent

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate

open Solanalib.Contracts.Model Solanalib.Specs.Core

abbrev Value := Sysvar.Rent102
abbrev Profile := Sysvar.PinocchioProfile

def try_minimum_balance (profile : Profile) (args : Value × UInt64) :
    Outcome Profile (Except ProgramError.Value UInt64) Sysvar.Panic Sysvar.Panic :=
  Sysvar.arithmeticOutcome profile.arithmetic.panicStrategy profile
    (Sysvar.rent102Try profile args.1 args.2)

def try_minimum_balance_contract :
    Solanalib.Contracts.Model Profile (Value × UInt64) (Except ProgramError.Value UInt64)
      Sysvar.Panic Sysvar.Panic where
  requires := fun _ _ => True
  post := fun before args outcome => outcome = try_minimum_balance before args

def try_minimum_balance_run := Callback.ofFunction try_minimum_balance

theorem try_minimum_balance_reference :
    try_minimum_balance_contract.Holds try_minimum_balance_run := by
  intro before args outcome _ step
  exact step.symm

theorem try_minimum_balance_hasExecution :
    try_minimum_balance_contract.HasExecution try_minimum_balance_run :=
  ⟨.release, (⟨3480, Sysvar.thresholdTwo⟩, 0),
    .returned (.ok 890880) .release, True.intro, rfl⟩

theorem try_minimum_balance_satisfiable : try_minimum_balance_contract.Satisfiable :=
  try_minimum_balance_hasExecution.satisfiable

end Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate

namespace Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate

open Solanalib.Contracts.Model Solanalib.Specs.Core

abbrev Value := Sysvar.Rent111

def try_minimum_balance (_ : Unit) (args : Value × UInt64) :
    Except ProgramError.Value UInt64 × Unit := (Sysvar.rent111Try args.1 args.2, ())

def try_minimum_balance_contract :
    Solanalib.Contracts.Model Unit (Value × UInt64) (Except ProgramError.Value UInt64) :=
  .returning (fun _ _ => True)
    (fun before args value after => after = before ∧ value = Sysvar.rent111Try args.1 args.2)

theorem try_minimum_balance_reference :
    try_minimum_balance_contract.RealizedBy try_minimum_balance := by
  intro before args _
  cases before
  exact ⟨rfl, rfl⟩

theorem try_minimum_balance_satisfiable : try_minimum_balance_contract.Satisfiable :=
  ⟨(), (⟨6960⟩, 0), True.intro⟩

theorem try_minimum_balance_hasExecution :
    try_minimum_balance_contract.HasExecution (returnsOf try_minimum_balance) :=
  ⟨(), (⟨6960⟩, 0), .returned (.ok 890880) (), True.intro, rfl⟩

end Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate
