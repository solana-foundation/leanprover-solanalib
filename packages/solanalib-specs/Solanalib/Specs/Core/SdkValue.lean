/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Unaligned
public import Solanalib.Runtime.Ids

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.SdkValue

/-- Exactly two stored bytes, independent of source pointer alignment. -/
abbrev U16 := { bytes : Solanalib.Runtime.Bytes // bytes.length = 2 }

/-- The little-endian value of a two-byte SDK wrapper. -/
def toUInt16 (value : U16) : UInt16 := UInt16.ofNat (Solanalib.Runtime.leNat value.val)

/-- A mathematical two-byte encoding, also used by the closed witnesses. -/
def ofUInt16 (value : UInt16) : U16 :=
  ⟨Solanalib.Runtime.u16le value.toNat, by simp [Solanalib.Runtime.u16le]⟩

/-- Decoding two actual bytes cannot overflow a sixteen-bit result. -/
theorem u16_in_range (value : U16) : Solanalib.Runtime.leNat value.val < 2^16 := by
  have bound := Solanalib.Runtime.leNat_lt value.val
  rw [value.property] at bound
  exact bound

/-- Encoding then decoding retains every bit of a bounded integer. -/
theorem toUInt16_ofUInt16 (value : UInt16) : toUInt16 (ofUInt16 value) = value := by
  simp only [toUInt16, ofUInt16, Solanalib.Runtime.u16le, Solanalib.Runtime.leNat_leBytes]
  rw [Nat.mod_eq_of_lt (show value.toNat < 256^2 from value.toNat_lt)]
  exact UInt16.ofNat_toNat

/-- A two-byte wrapper conversion returns its exact little-endian value. -/
def intoU16Contract : Solanalib.Contracts.Model Unit U16 UInt16 :=
  .returning (fun _ _ => True)
    (fun before value result after => after = before ∧
      result.toNat = Solanalib.Runtime.leNat value.val)

/-- Total two-byte conversion with no state effects. -/
def intoU16Model (before : Unit) (value : U16) : UInt16 × Unit :=
  (toUInt16 value, before)

theorem intoU16Reference : intoU16Contract.RealizedBy intoU16Model := by
  intro before value _
  exact ⟨rfl, Nat.mod_eq_of_lt (u16_in_range value)⟩

theorem intoU16Satisfiable : intoU16Contract.Satisfiable :=
  ⟨(), ofUInt16 0, trivial⟩

/-- A zero key is the absent optional key; every other key is retained exactly. -/
def optionalKey (key : Solanalib.Runtime.Pubkey) : Option Solanalib.Runtime.Pubkey :=
  if key = Solanalib.Runtime.Ids.systemProgram then none else some key

/-- No nonzero key, including keys with zero prefixes, is discarded. -/
theorem optionalKey_some (key : Solanalib.Runtime.Pubkey) (nonzero : key ≠
  Solanalib.Runtime.Ids.systemProgram) :
    optionalKey key = some key := by simp [optionalKey, nonzero]

/-- The returned optional value uses exactly the all-zero sentinel. -/
def optionalKeyContract : Solanalib.Contracts.Model Unit Solanalib.Runtime.Pubkey (Option
  Solanalib.Runtime.Pubkey) :=
  .returning (fun _ _ => True)
    (fun before key result after => after = before ∧ result = optionalKey key)

/-- Total optional-key interpretation; this does not assert a source ABI. -/
def optionalKeyModel (before : Unit) (key : Solanalib.Runtime.Pubkey) : Option
  Solanalib.Runtime.Pubkey × Unit :=
  (optionalKey key, before)

theorem optionalKeyReference : optionalKeyContract.RealizedBy optionalKeyModel :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem optionalKeySatisfiable : optionalKeyContract.Satisfiable :=
  ⟨(), Solanalib.Runtime.Ids.systemProgram, trivial⟩

/-- A constant key function preserves its exact canonical key and state. -/
def idContract (key : Solanalib.Runtime.Pubkey) : Solanalib.Contracts.Model Unit Unit
  Solanalib.Runtime.Pubkey :=
  .returning (fun _ _ => True)
    (fun before _ result after => result = key ∧ after = before)

/-- A mathematical constant-key reference, shared by the four SDK functions. -/
def idModel (key : Solanalib.Runtime.Pubkey) (before : Unit) (_ : Unit) : Solanalib.Runtime.Pubkey
  × Unit :=
  (key, before)

theorem idReference (key : Solanalib.Runtime.Pubkey) : (idContract key).RealizedBy (idModel key) :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem idSatisfiable (key : Solanalib.Runtime.Pubkey) : (idContract key).Satisfiable :=
  ⟨(), (), trivial⟩

end Solanalib.Specs.Core.SdkValue
