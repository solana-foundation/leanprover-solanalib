/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Runtime.Error

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- Token byte strings use the canonical runtime byte representation. -/
abbrev Bytes := Solanalib.Runtime.Bytes

/-- Named program errors use their canonical runtime names. Token-specific
errors are explicit `Custom` codes; this alias introduces no callee behavior. -/
abbrev Error := Solanalib.Runtime.InstrError

/-- `TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`. -/
def legacyProgramId : Solanalib.Runtime.Pubkey :=
  .ofNat 0x06ddf6e1d765a193d9cbe146ceeb79ac1cb485ed5f5b37913a8cf5857eff00a9

/-- `TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb`. -/
def token2022ProgramId : Solanalib.Runtime.Pubkey :=
  .ofNat 0x06ddf6e1ee758fde18425dbce46ccddab61afc4d83b90d27febdf928d8a18bfc

/-- The serialized base account size shared by the selected token interfaces. -/
def accountLength : Nat := 165

/-- The serialized base mint size shared by the selected token interfaces. -/
def mintLength : Nat := 82

/-- The multisig size excluded from token-2022 extensible layouts. -/
def multisigLength : Nat := 355

/-- A full-range little-endian read. Missing bytes fail rather than being
silently padded or decoded from a truncated slice. -/
def readNat (bytes : Bytes) (offset length : Nat) : Option Nat :=
  if offset + length ≤ bytes.length then
    some (Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes offset length))
  else none

/-- A full 32-byte public-key read. The range test makes `ofBytes`' padding
behavior irrelevant on every successful result. -/
def readKey (bytes : Bytes) (offset : Nat) : Option Solanalib.Runtime.Pubkey :=
  if offset + 32 ≤ bytes.length then
    some (.ofBytes (Solanalib.Runtime.slice bytes offset 32))
  else none

/-- Successful integer reads retain their complete source range. -/
theorem readNat_eq_some_iff {bytes : Bytes} {offset length value : Nat} :
    readNat bytes offset length = some value ↔
      offset + length ≤ bytes.length ∧
        value = Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes offset length) := by
  by_cases range : offset + length ≤ bytes.length <;> simp [readNat, range, eq_comm]

/-- The decoded width is justified by the actual checked range. -/
theorem readNat_lt {bytes : Bytes} {offset length value : Nat}
    (read : readNat bytes offset length = some value) : value < 256^length := by
  obtain ⟨range, rfl⟩ := readNat_eq_some_iff.mp read
  have bound := Solanalib.Runtime.leNat_lt (Solanalib.Runtime.slice bytes offset length)
  simpa only [Solanalib.Runtime.length_slice_of_le range] using bound

/-- Successful key reads expose all 32 supplied bytes. -/
theorem readKey_eq_some_iff {bytes : Bytes} {offset : Nat} {key : Solanalib.Runtime.Pubkey} :
    readKey bytes offset = some key ↔
      offset + 32 ≤ bytes.length ∧
        key = .ofBytes (Solanalib.Runtime.slice bytes offset 32) := by
  by_cases range : offset + 32 ≤ bytes.length <;> simp [readKey, range, eq_comm]

/-- The three token account states. The raw account reader of Pinocchio does not
validate this enum; its later state projection may therefore panic. -/
inductive AccountState where
  /-- The source discriminant 0. -/
  | uninitialized
  /-- The source discriminant 1. -/
  | initialized
  /-- The source discriminant 2. -/
  | frozen
  deriving DecidableEq, Repr

/-- Checked enum conversion shared by SPL decoding and the state
projection of Pinocchio. Each caller supplies its own error or panic behavior. -/
def decodeAccountState (byte : UInt8) : Option AccountState :=
  if byte = 0 then some .uninitialized
  else if byte = 1 then some .initialized
  else if byte = 2 then some .frozen
  else none

/-- Every admitted state byte has its exact source discriminant. -/
theorem decodeAccountState_some_iff {byte : UInt8} {state : AccountState} :
    decodeAccountState byte = some state ↔
      (byte = 0 ∧ state = .uninitialized) ∨
      (byte = 1 ∧ state = .initialized) ∨
      (byte = 2 ∧ state = .frozen) := by
  by_cases zero : byte = 0
  · subst byte
    simp [decodeAccountState, eq_comm]
  by_cases one : byte = 1
  · subst byte
    simp [decodeAccountState, eq_comm]
  by_cases two : byte = 2
  · subst byte
    simp [decodeAccountState, eq_comm]
  simp [decodeAccountState, zero, one, two]

end Solanalib.Specs.Core.Token
