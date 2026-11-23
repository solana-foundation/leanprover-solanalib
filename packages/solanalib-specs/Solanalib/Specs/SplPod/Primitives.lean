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

namespace Solanalib.Specs.SplPod.primitives

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace PodU16

/-- Decode the two-byte PodU16 in little-endian order. -/
abbrev into_u16_contract := SdkValue.intoU16Contract

/-- Exact total value reference. -/
abbrev into_u16_model := SdkValue.intoU16Model

theorem into_u16_reference : into_u16_contract.RealizedBy into_u16_model :=
  SdkValue.intoU16Reference

theorem into_u16_satisfiable : into_u16_contract.Satisfiable :=
  SdkValue.intoU16Satisfiable

end PodU16

namespace PodU64

/-- Decode the eight-byte PodU64 in little-endian order. -/
abbrev into_u64_contract := Unaligned.intoU64Contract

/-- Exact total value reference. -/
abbrev into_u64_model := Unaligned.intoU64Model

theorem into_u64_reference : into_u64_contract.RealizedBy into_u64_model :=
  Unaligned.intoU64Reference

theorem into_u64_satisfiable : into_u64_contract.Satisfiable :=
  Unaligned.intoU64Satisfiable

end PodU64

end Solanalib.Specs.SplPod.primitives
