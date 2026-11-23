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

namespace Solanalib.Specs.SolanaInvoke

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

/-- The complete on-chain invocation contract at the actual opaque signature. -/
def invoke_signed_contract : Family := Sdk.signedFamily

/-- The registered runtime reference, retaining its explicit callee contract. -/
def invoke_signed_run : FamilyRun invoke_signed_contract := Sdk.signedRun

/-- Closed reference correctness at every runtime/callee index. -/
theorem invoke_signed_reference : FamilyReference invoke_signed_contract invoke_signed_run :=
  Sdk.signedReference

/-- Closed mock-callee sample, used only for consistency witnesses. -/
def invoke_signed_sample : invoke_signed_contract.Index := Witness.index

/-- A finite normal reference execution at that same exact sample. -/
theorem invoke_signed_has_execution :
    FamilyHasExecution invoke_signed_contract invoke_signed_run invoke_signed_sample :=
  Witness.signedHasExecution

/-- The sample has an admissible input. -/
theorem invoke_signed_satisfiable :
    FamilySatisfiable invoke_signed_contract invoke_signed_sample :=
  Witness.signedSatisfiable

end Solanalib.Specs.SolanaInvoke

namespace Solanalib.Specs.SolanaInvoke

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

/-- The complete on-chain invocation contract at the actual opaque signature. -/
def invoke_contract : Family := Sdk.unsignedFamily

/-- The registered runtime reference, retaining its explicit callee contract. -/
def invoke_run : FamilyRun invoke_contract := Sdk.unsignedRun

/-- Closed reference correctness at every runtime/callee index. -/
theorem invoke_reference : FamilyReference invoke_contract invoke_run :=
  Sdk.unsignedReference

/-- Closed mock-callee sample, used only for consistency witnesses. -/
def invoke_sample : invoke_contract.Index := Witness.index

/-- A finite normal reference execution at that same exact sample. -/
theorem invoke_has_execution :
    FamilyHasExecution invoke_contract invoke_run invoke_sample :=
  Witness.unsignedHasExecution

/-- The sample has an admissible input. -/
theorem invoke_satisfiable :
    FamilySatisfiable invoke_contract invoke_sample :=
  Witness.unsignedSatisfiable

end Solanalib.Specs.SolanaInvoke
