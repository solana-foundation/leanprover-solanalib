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

namespace Solanalib.Specs.SolanaDefineSyscall.definitions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

/-- The complete on-chain invocation contract at the actual opaque signature. -/
def sol_invoke_signed_rust_contract : Family := rawFamily

/-- The registered runtime reference, retaining its explicit callee contract. -/
def sol_invoke_signed_rust_run : FamilyRun sol_invoke_signed_rust_contract := rawFamilyRun

/-- Closed reference correctness at every runtime/callee index. -/
theorem sol_invoke_signed_rust_reference : FamilyReference sol_invoke_signed_rust_contract
  sol_invoke_signed_rust_run :=
  rawReference

/-- Closed mock-callee sample, used only for consistency witnesses. -/
def sol_invoke_signed_rust_sample : sol_invoke_signed_rust_contract.Index := Witness.index

/-- A finite normal reference execution at that same exact sample. -/
theorem sol_invoke_signed_rust_has_execution :
    FamilyHasExecution sol_invoke_signed_rust_contract sol_invoke_signed_rust_run
      sol_invoke_signed_rust_sample :=
  Witness.rawHasExecution

/-- The sample has an admissible input. -/
theorem sol_invoke_signed_rust_satisfiable :
    FamilySatisfiable sol_invoke_signed_rust_contract sol_invoke_signed_rust_sample :=
  Witness.rawSatisfiable

end Solanalib.Specs.SolanaDefineSyscall.definitions
