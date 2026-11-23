/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaRent.Rent

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaRent.Rent

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The comparison is reached only after minimum_balance returns. Its exact
integer overflow, binary64 rounding and saturating cast behavior are retained. -/
def is_exempt (profile : Profile) (args : Value × UInt64 × UInt64) :
    Outcome Profile Bool Sysvar.Panic Sysvar.Panic :=
  Outcome.map (fun minimum => decide (minimum ≤ args.2.1))
    (minimum_balance profile (args.1, args.2.2))

def is_exempt_contract :
    Solanalib.Contracts.Model Profile (Value × UInt64 × UInt64) Bool Sysvar.Panic Sysvar.Panic where
  requires := fun _ _ => True
  post := fun before args outcome => outcome = is_exempt before args

def is_exempt_run := Callback.ofFunction is_exempt

theorem is_exempt_reference : is_exempt_contract.Holds is_exempt_run := by
  intro before args outcome _ step
  exact step.symm

theorem is_exempt_hasExecution : is_exempt_contract.HasExecution is_exempt_run :=
  ⟨.release, (Sysvar.defaultRent300, 890880, 0), .returned true .release, True.intro, rfl⟩

theorem is_exempt_satisfiable : is_exempt_contract.Satisfiable :=
  is_exempt_hasExecution.satisfiable

theorem is_exempt_of_minimum (profile : Profile) (rent : Value) (balance length minimum : UInt64)
    (computed : minimum_balance profile (rent, length) = .returned minimum profile) :
    is_exempt profile (rent, balance, length) =
      .returned (decide (minimum ≤ balance)) profile := by
  simp only [is_exempt, computed, Outcome.map]

end Solanalib.Specs.SolanaRent.Rent
