/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Specs.Core.SysvarRentArithmetic

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaRent.Rent

open Solanalib.Contracts.Model Solanalib.Specs.Core

abbrev Value := Sysvar.Rent300
abbrev Profile := Sysvar.ArithmeticProfile

def minimum_balance (profile : Profile) (args : Value × UInt64) :
    Outcome Profile UInt64 Sysvar.Panic Sysvar.Panic :=
  Sysvar.arithmeticOutcome profile.panicStrategy profile
    (Sysvar.rent300Minimum profile args.1 args.2)

def minimum_balance_contract :
    Solanalib.Contracts.Model Profile (Value × UInt64) UInt64 Sysvar.Panic Sysvar.Panic where
  requires := fun _ _ => True
  post := fun before args outcome => outcome = minimum_balance before args

def minimum_balance_run := Callback.ofFunction minimum_balance

theorem minimum_balance_reference : minimum_balance_contract.Holds minimum_balance_run := by
  intro before args outcome _ step
  exact step.symm

theorem minimum_balance_hasExecution :
    minimum_balance_contract.HasExecution minimum_balance_run :=
  ⟨.release, (Sysvar.defaultRent300, 0), .returned 890880 .release, True.intro, rfl⟩

theorem minimum_balance_satisfiable : minimum_balance_contract.Satisfiable :=
  minimum_balance_hasExecution.satisfiable

end Solanalib.Specs.SolanaRent.Rent
