/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenStateExtra

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplTokenMetadataInterface.state.TokenMetadata

open Solanalib.Specs.Core.Token

/-- The default metadata has absent authority, zero mint and all four owned
collections empty. It does not allocate or validate a usable mint. -/
def default_contract : Solanalib.Contracts.Model Unit Unit Metadata :=
  .returning (fun _ _ => True) fun _ _ value _ => value = Metadata.default

/-- Exact empty owned-value observation; physical String/Vec representations and their zero-capacity
ownership require separate source-binding proofs. -/
def defaultReference (_ : Unit) (_ : Unit) : Metadata × Unit := (Metadata.default, ())

/-- The reference realizes the full default value. -/
theorem default_reference : default_contract.RealizedBy defaultReference := by
  intro before args _
  rfl

/-- Default has no input requirement. -/
theorem default_satisfiable : default_contract.Satisfiable := ⟨(), (), trivial⟩

end Solanalib.Specs.SplTokenMetadataInterface.state.TokenMetadata
