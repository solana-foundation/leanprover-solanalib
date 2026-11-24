/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaZeroCopy

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaZeroCopy

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem little_endian_not_native_alignment :
    Unaligned.toUInt64 ⟨[1, 2, 3, 4, 5, 6, 7, 8], rfl⟩ = 0x0807060504030201 := by
  decide

theorem maximum_value :
    Unaligned.toUInt64 ⟨List.replicate 8 255, by simp⟩ = 0xffffffffffffffff := by
  decide

theorem round_trip_all_values (value : UInt64) :
    Unaligned.toUInt64 (Unaligned.ofUInt64 value) = value :=
  Unaligned.toUInt64_ofUInt64 value

end SolanalibTest.Specs.SolanaZeroCopy
