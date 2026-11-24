/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.SdkValue

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaZeroCopy.unaligned.U16

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Decode exactly two little-endian bytes without a pointer alignment premise. -/
abbrev into_u16_contract := SdkValue.intoU16Contract

/-- Exact total value reference. -/
abbrev into_u16_model := SdkValue.intoU16Model

theorem into_u16_reference : into_u16_contract.RealizedBy into_u16_model :=
  SdkValue.intoU16Reference

theorem into_u16_satisfiable : into_u16_contract.Satisfiable :=
  SdkValue.intoU16Satisfiable


end Solanalib.Specs.SolanaZeroCopy.unaligned.U16
