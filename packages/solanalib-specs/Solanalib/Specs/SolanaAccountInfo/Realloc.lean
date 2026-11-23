/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoResize

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaAccountInfo.AccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Realloc retains its explicit zero-init flag. Nonzeroing shrink/regrow
preserves the original backing bytes, unlike the resize convenience method. -/
def realloc_contract := AccountInfoSdk.resizeContract
def realloc_run := AccountInfoSdk.resizeReference
theorem realloc_reference : realloc_contract.Holds realloc_run := AccountInfoSdk.resize_holds
theorem realloc_has_execution : realloc_contract.HasExecution realloc_run := by
  obtain ⟨outcome, step⟩ := AccountInfoSdk.resize_exists _ _ AccountInfoSdk.sample_resizeReady
  exact ⟨AccountInfoSdk.sample, AccountInfoSdk.sampleResizeArgs, outcome,
    AccountInfoSdk.sample_resizeReady, step⟩
theorem realloc_satisfiable : realloc_contract.Satisfiable := realloc_has_execution.satisfiable

end Solanalib.Specs.SolanaAccountInfo.AccountInfo
