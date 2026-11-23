/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OpaqueCpiWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Opaque invocation signature bindings. Exact reviewed releases and build
conditions are recorded per function in the applicability registry. Runtime
and source-memory interpretation are explicit assumptions; no invocation
implementation or callee body is traversed by these contracts. -/

namespace Solanalib.Specs.Pinocchio.cpi

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

/-- The complete on-chain invocation contract at the actual opaque signature. -/
def invoke_signed_unchecked_contract : Family := unitFamily

/-- The registered runtime reference, retaining its explicit callee contract. -/
def invoke_signed_unchecked_run : FamilyRun invoke_signed_unchecked_contract := unitRun

/-- Closed reference correctness at every runtime/callee index. -/
theorem invoke_signed_unchecked_reference : FamilyReference invoke_signed_unchecked_contract
  invoke_signed_unchecked_run :=
  unitReference

/-- Closed mock-callee sample, used only for consistency witnesses. -/
def invoke_signed_unchecked_sample : invoke_signed_unchecked_contract.Index := Witness.index

/-- A finite normal reference execution at that same exact sample. -/
theorem invoke_signed_unchecked_has_execution :
    FamilyHasExecution invoke_signed_unchecked_contract invoke_signed_unchecked_run
      invoke_signed_unchecked_sample :=
  Witness.unitHasExecution

/-- The sample has an admissible input. -/
theorem invoke_signed_unchecked_satisfiable :
    FamilySatisfiable invoke_signed_unchecked_contract invoke_signed_unchecked_sample :=
  Witness.unitSatisfiable

end Solanalib.Specs.Pinocchio.cpi

namespace Solanalib.Specs.Pinocchio.syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

/-- The complete on-chain invocation contract at the actual opaque signature. -/
def sol_invoke_signed_c_contract : Family := rawFamily

/-- The registered runtime reference, retaining its explicit callee contract. -/
def sol_invoke_signed_c_run : FamilyRun sol_invoke_signed_c_contract := rawFamilyRun

/-- Closed reference correctness at every runtime/callee index. -/
theorem sol_invoke_signed_c_reference : FamilyReference sol_invoke_signed_c_contract
  sol_invoke_signed_c_run :=
  rawReference

/-- Closed mock-callee sample, used only for consistency witnesses. -/
def sol_invoke_signed_c_sample : sol_invoke_signed_c_contract.Index := Witness.index

/-- A finite normal reference execution at that same exact sample. -/
theorem sol_invoke_signed_c_has_execution :
    FamilyHasExecution sol_invoke_signed_c_contract sol_invoke_signed_c_run
      sol_invoke_signed_c_sample :=
  Witness.rawHasExecution

/-- The sample has an admissible input. -/
theorem sol_invoke_signed_c_satisfiable :
    FamilySatisfiable sol_invoke_signed_c_contract sol_invoke_signed_c_sample :=
  Witness.rawSatisfiable

end Solanalib.Specs.Pinocchio.syscalls
