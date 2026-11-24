/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Specs.Core.Unaligned

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaZeroCopy.unaligned.U64

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Compute the bounded little-endian value without changing state. -/
abbrev into_u64_model := Unaligned.intoU64Model

/-- The exact eight-byte value equation, without a physical alignment premise. -/
abbrev into_u64_contract := Unaligned.intoU64Contract

theorem into_u64_reference : into_u64_contract.RealizedBy into_u64_model :=
  Unaligned.intoU64Reference

theorem into_u64_satisfiable : into_u64_contract.Satisfiable :=
  Unaligned.intoU64Satisfiable

end Solanalib.Specs.SolanaZeroCopy.unaligned.U64
