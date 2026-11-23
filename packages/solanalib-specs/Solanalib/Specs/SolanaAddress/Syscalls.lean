/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressSyscallSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaAddress.Address

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Address

/-- Supporting selected-Solana try_find wrapper. Provider admission requires
initialized output on each actual status-zero reply. -/
def try_find_program_address_solana_contract : Family := Syscall.tryFamily
def try_find_program_address_solana_run : FamilyRun try_find_program_address_solana_contract :=
  Syscall.tryFamilyRun
def try_find_program_address_solana_sample : try_find_program_address_solana_contract.Index :=
  Syscall.sampleTypes

theorem try_find_program_address_solana_reference :
    FamilyReference try_find_program_address_solana_contract try_find_program_address_solana_run :=
  Syscall.tryFamilyReference

theorem try_find_program_address_solana_satisfiable :
    FamilySatisfiable try_find_program_address_solana_contract
      try_find_program_address_solana_sample :=
  ⟨(3 : Nat), Syscall.sampleTryCall, Syscall.sample_initialized 3 Syscall.sampleInputs⟩

theorem try_find_program_address_solana_has_execution :
    FamilyHasExecution try_find_program_address_solana_contract try_find_program_address_solana_run
      try_find_program_address_solana_sample :=
  ⟨(3 : Nat), Syscall.sampleTryCall, .returned (some (.zero, 254)) (10 : Nat),
    Syscall.sample_initialized 3 Syscall.sampleInputs, Syscall.sampleTry_execution⟩

/-- The admitted wrapper has a finite exit exactly when its actual syscall
does. This does not supply a finite syscall execution. -/
theorem try_find_program_address_solana_hasOutcome_iff
    (types : Syscall.Types) (before : types.State) (args : Syscall.TryCall types)
    (ready : (try_find_program_address_solana_contract.contract types).requires before args) :
    (∃ outcome, try_find_program_address_solana_run types before args outcome) ↔
      ∃ exit, args.syscall before (Syscall.pdaRequest args.inputs) exit :=
  Syscall.tryRun_hasOutcome_iff args.syscall before args.inputs ready

/-- Primary selected-Solana find wrapper. It composes the actual try_find
syscall path and the local non-returning panic site, retaining their state. -/
def find_program_address_solana_contract : Family := Syscall.findFamily
def find_program_address_solana_run : FamilyRun find_program_address_solana_contract :=
  Syscall.findFamilyRun
def find_program_address_solana_sample : find_program_address_solana_contract.Index :=
  Syscall.sampleTypes

theorem find_program_address_solana_reference :
    FamilyReference find_program_address_solana_contract find_program_address_solana_run :=
  Syscall.findFamilyReference

theorem find_program_address_solana_satisfiable :
    FamilySatisfiable find_program_address_solana_contract find_program_address_solana_sample :=
  ⟨(3 : Nat), Syscall.sampleFindCall, Syscall.sample_initialized 3 Syscall.sampleInputs⟩

theorem find_program_address_solana_has_execution :
    FamilyHasExecution find_program_address_solana_contract find_program_address_solana_run
      find_program_address_solana_sample :=
  ⟨(3 : Nat), Syscall.sampleFindCall, .returned (.zero, 254) (10 : Nat),
    Syscall.sample_initialized 3 Syscall.sampleInputs, Syscall.sampleFind_execution⟩

/-- Primary Address curve predicate on Solana: selector zero, exact address
bytes, null output destination, and all actual finite syscall outcomes. -/
def is_on_curve_solana_contract : Family := Syscall.curveFamily
def is_on_curve_solana_run : FamilyRun is_on_curve_solana_contract := Syscall.curveFamilyRun
def is_on_curve_solana_sample : is_on_curve_solana_contract.Index := Syscall.sampleTypes

theorem is_on_curve_solana_reference :
    FamilyReference is_on_curve_solana_contract is_on_curve_solana_run :=
  Syscall.curveFamilyReference

theorem is_on_curve_solana_satisfiable :
    FamilySatisfiable is_on_curve_solana_contract is_on_curve_solana_sample :=
  ⟨(3 : Nat), Syscall.sampleCurveCall, trivial⟩

theorem is_on_curve_solana_has_execution :
    FamilyHasExecution is_on_curve_solana_contract is_on_curve_solana_run is_on_curve_solana_sample
      :=
  ⟨(3 : Nat), Syscall.sampleCurveCall, .returned true (8 : Nat),
    trivial, Syscall.sampleCurve_execution⟩

end Solanalib.Specs.SolanaAddress.Address
