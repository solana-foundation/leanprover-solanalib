/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Specs.Core.Hash

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaHash.Hash

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The hash wrapper has the exact 32-byte source representation at value level. -/
abbrev Value := Solanalib.Specs.Core.Hash.Value

/-- Copying to an array preserves all bytes and does not change caller state. -/
abbrev to_bytes_contract := Solanalib.Specs.Core.Hash.toBytesContract

/-- The total mathematical array copy. -/
abbrev to_bytes_model := Solanalib.Specs.Core.Hash.toBytesModel

theorem to_bytes_reference : to_bytes_contract.RealizedBy to_bytes_model :=
  Solanalib.Specs.Core.Hash.toBytesReference

theorem to_bytes_satisfiable : to_bytes_contract.Satisfiable :=
  Solanalib.Specs.Core.Hash.toBytesSatisfiable

end Solanalib.Specs.SolanaHash.Hash
