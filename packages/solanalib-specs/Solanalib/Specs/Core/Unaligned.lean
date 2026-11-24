/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Basic
public import Solanalib.Specs.Core

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Unaligned

/-- The unaligned wrapper has exactly eight bytes; no pointer alignment is
assumed or repaired when its mathematical value is decoded. -/
abbrev U64 := { bytes : Solanalib.Runtime.Bytes // bytes.length = 8 }

/-- Decode the eight bytes of the wrapper in little-endian order. -/
def toUInt64 (value : U64) : UInt64 := UInt64.ofNat (Solanalib.Runtime.leNat value.val)

/-- Encode a bounded value for mathematical round-trip statements and fixtures. -/
def ofUInt64 (value : UInt64) : U64 :=
  ⟨Solanalib.Runtime.u64le value.toNat, by simp [Solanalib.Runtime.u64le]⟩

theorem decoded_in_range (value : U64) : Solanalib.Runtime.leNat value.val < 2^64 := by
  have bound := Solanalib.Runtime.leNat_lt value.val
  rw [value.property] at bound
  exact bound

theorem toUInt64_ofUInt64 (value : UInt64) : toUInt64 (ofUInt64 value) = value := by
  simp only [toUInt64, ofUInt64, Solanalib.Runtime.u64le, Solanalib.Runtime.leNat_leBytes]
  have bound : value.toNat < 256^8 := value.toNat_lt
  rw [Nat.mod_eq_of_lt bound]
  exact UInt64.ofNat_toNat

/-- The complete little-endian value contract shared by the reviewed U64 wrappers. -/
def intoU64Contract : Solanalib.Contracts.Model Unit U64 UInt64 :=
  .returning (fun _ _ => True)
    (fun before value result after => after = before ∧
      result.toNat = Solanalib.Runtime.leNat value.val)

/-- Decode the bounded eight-byte value without changing state. -/
def intoU64Model (before : Unit) (value : U64) : UInt64 × Unit :=
  (toUInt64 value, before)

theorem intoU64Reference : intoU64Contract.RealizedBy intoU64Model := by
  intro before value _
  refine ⟨rfl, ?_⟩
  exact Nat.mod_eq_of_lt (decoded_in_range value)

theorem intoU64Satisfiable : intoU64Contract.Satisfiable :=
  ⟨(), ofUInt64 0, trivial⟩

end Solanalib.Specs.Core.Unaligned
