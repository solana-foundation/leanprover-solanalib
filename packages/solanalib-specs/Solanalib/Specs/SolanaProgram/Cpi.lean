/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OpaqueCpiSdkOwnedWitness
public import Solanalib.Specs.Core.OpaqueCpiWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Opaque invocation signature bindings. Exact reviewed releases and build
conditions are recorded per function in the applicability registry. Runtime
and source-memory interpretation are explicit assumptions; no invocation
implementation or callee body is traversed by these contracts. -/

namespace Solanalib.Specs.SolanaProgram.program

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

/-- The complete on-chain invocation contract at the actual opaque signature. -/
def invoke_signed_contract : Family := Sdk.Owned.signedFamily

/-- The registered runtime reference, retaining its explicit callee contract. -/
def invoke_signed_run : FamilyRun invoke_signed_contract := Sdk.Owned.signedRun

/-- Closed reference correctness at every runtime/callee index. -/
theorem invoke_signed_reference : FamilyReference invoke_signed_contract invoke_signed_run :=
  Sdk.Owned.signedReference

/-- Closed mock-callee sample, used only for consistency witnesses. -/
def invoke_signed_sample : invoke_signed_contract.Index := OwnedWitness.index

/-- A finite normal reference execution at that same exact sample. -/
theorem invoke_signed_has_execution :
    FamilyHasExecution invoke_signed_contract invoke_signed_run invoke_signed_sample :=
  OwnedWitness.signedHasExecution

/-- The sample has an admissible input. -/
theorem invoke_signed_satisfiable :
    FamilySatisfiable invoke_signed_contract invoke_signed_sample :=
  OwnedWitness.signedSatisfiable

end Solanalib.Specs.SolanaProgram.program

namespace Solanalib.Specs.SolanaProgram.program

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

/-- The complete on-chain invocation contract at the actual opaque signature. -/
def invoke_contract : Family := Sdk.Owned.unsignedFamily

/-- The registered runtime reference, retaining its explicit callee contract. -/
def invoke_run : FamilyRun invoke_contract := Sdk.Owned.unsignedRun

/-- Closed reference correctness at every runtime/callee index. -/
theorem invoke_reference : FamilyReference invoke_contract invoke_run :=
  Sdk.Owned.unsignedReference

/-- Closed mock-callee sample, used only for consistency witnesses. -/
def invoke_sample : invoke_contract.Index := OwnedWitness.index

/-- A finite normal reference execution at that same exact sample. -/
theorem invoke_has_execution :
    FamilyHasExecution invoke_contract invoke_run invoke_sample :=
  OwnedWitness.unsignedHasExecution

/-- The sample has an admissible input. -/
theorem invoke_satisfiable :
    FamilySatisfiable invoke_contract invoke_sample :=
  OwnedWitness.unsignedSatisfiable

end Solanalib.Specs.SolanaProgram.program

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.syscalls.definitions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

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

end Solanalib.Specs.SolanaProgram.syscalls.definitions

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.program

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

/-- Decoded-request contract, used at the opaque source signature only under
the separate conditional legacy transport. -/
def invoke_forwarded_inputs_contract : Family := Sdk.unsignedFamily

/-- The registered runtime reference, retaining its explicit callee contract. -/
def invoke_forwarded_inputs_run : FamilyRun invoke_forwarded_inputs_contract := Sdk.unsignedRun

/-- Closed reference correctness at every runtime/callee index. -/
theorem invoke_forwarded_inputs_reference : FamilyReference invoke_forwarded_inputs_contract
  invoke_forwarded_inputs_run :=
  Sdk.unsignedReference

/-- Closed mock-callee sample, used only for consistency witnesses. -/
def invoke_forwarded_inputs_sample : invoke_forwarded_inputs_contract.Index := Witness.index

/-- A finite normal reference execution at that same exact sample. -/
theorem invoke_forwarded_inputs_has_execution :
    FamilyHasExecution invoke_forwarded_inputs_contract invoke_forwarded_inputs_run
      invoke_forwarded_inputs_sample :=
  Witness.unsignedHasExecution

/-- The sample has an admissible input. -/
theorem invoke_forwarded_inputs_satisfiable :
    FamilySatisfiable invoke_forwarded_inputs_contract invoke_forwarded_inputs_sample :=
  Witness.unsignedSatisfiable

/-- Decoded-request contract, used at the opaque source signature only under
the separate conditional legacy transport. -/
def invoke_signed_forwarded_inputs_contract : Family := Sdk.signedFamily

/-- The registered runtime reference, retaining its explicit callee contract. -/
def invoke_signed_forwarded_inputs_run : FamilyRun invoke_signed_forwarded_inputs_contract :=
  Sdk.signedRun

/-- Closed reference correctness at every runtime/callee index. -/
theorem invoke_signed_forwarded_inputs_reference : FamilyReference
  invoke_signed_forwarded_inputs_contract invoke_signed_forwarded_inputs_run :=
  Sdk.signedReference

/-- Closed mock-callee sample, used only for consistency witnesses. -/
def invoke_signed_forwarded_inputs_sample : invoke_signed_forwarded_inputs_contract.Index :=
  Witness.index

/-- A finite normal reference execution at that same exact sample. -/
theorem invoke_signed_forwarded_inputs_has_execution :
    FamilyHasExecution invoke_signed_forwarded_inputs_contract invoke_signed_forwarded_inputs_run
      invoke_signed_forwarded_inputs_sample :=
  Witness.signedHasExecution

/-- The sample has an admissible input. -/
theorem invoke_signed_forwarded_inputs_satisfiable :
    FamilySatisfiable invoke_signed_forwarded_inputs_contract invoke_signed_forwarded_inputs_sample
      :=
  Witness.signedSatisfiable

end Solanalib.Specs.SolanaProgram.program
