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

namespace Solanalib.Specs.Core.Hash

/-- A source hash is exactly 32 bytes. This type supplies no cryptographic law
and does not identify hash values with account addresses. -/
structure Value where
  /-- The bytes in their existing order. -/
  bytes : Solanalib.Runtime.Bytes
  /-- The complete source array width. -/
  length_eq : bytes.length = 32
  deriving DecidableEq

/-- The exact array returned by the SDK, with no padding or truncation. -/
abbrev Array32 := { bytes : Solanalib.Runtime.Bytes // bytes.length = 32 }

/-- Construct the hash wrapper around an already sized array. -/
def ofArray (array : Array32) : Value := ⟨array.val, array.property⟩

/-- Copy the array of the source hash in its existing byte order. -/
def toArray (hash : Value) : Array32 := ⟨hash.bytes, hash.length_eq⟩

@[simp] theorem ofArray_toArray (hash : Value) : ofArray (toArray hash) = hash := by
  cases hash
  rfl

@[simp] theorem toArray_ofArray (array : Array32) : toArray (ofArray array) = array := by
  cases array
  rfl

/-- Equal copied arrays identify equal mathematical hash values. -/
theorem toArray_injective : Function.Injective toArray := by
  intro left right same
  simpa only [ofArray_toArray] using congrArg ofArray same

/-- An inhabited hash value for model consistency witnesses; it is not claimed
to be the SHA-256 digest of any particular message. -/
def zero : Value := ⟨List.replicate 32 0, by simp⟩

/-- The complete value-copy contract shared by the individually reviewed versions. -/
def toBytesContract : Solanalib.Contracts.Model Unit Value Array32 :=
  .returning (fun _ _ => True)
    (fun before hash array after => array.val = hash.bytes ∧ after = before)

/-- The total mathematical array copy, preserving the observed state. -/
def toBytesModel (before : Unit) (hash : Value) : Array32 × Unit :=
  (toArray hash, before)

theorem toBytesReference : toBytesContract.RealizedBy toBytesModel := by
  intro before hash _
  exact ⟨rfl, rfl⟩

theorem toBytesSatisfiable : toBytesContract.Satisfiable :=
  ⟨(), zero, trivial⟩

end Solanalib.Specs.Core.Hash
