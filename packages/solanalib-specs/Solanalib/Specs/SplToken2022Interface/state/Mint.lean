/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenState

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplToken2022Interface.state.Mint

open Solanalib.Specs.Core.Token

/-- Every field of this concrete Mint is Copy. The derived Clone preserves
the complete value without allocation or a generic user clone callback. -/
def clone_contract : Solanalib.Contracts.Model Mint Unit Mint :=
  .returning (fun _ _ => True) fun before _ value after => value = before ∧ after = before

/-- Exact mathematical value-copy reference. -/
def cloneReference (mint : Mint) (_ : Unit) : Mint × Mint := (mint, mint)

/-- The copied record realizes the complete unchanged-state contract. -/
theorem clone_reference : clone_contract.RealizedBy cloneReference := by
  intro before args _
  exact ⟨rfl, rfl⟩

/-- An initialized, nonzero-supply Mint inhabits the contract. -/
theorem clone_satisfiable : clone_contract.Satisfiable :=
  ⟨⟨none, 1, 9, true, none⟩, (), trivial⟩

end Solanalib.Specs.SplToken2022Interface.state.Mint
