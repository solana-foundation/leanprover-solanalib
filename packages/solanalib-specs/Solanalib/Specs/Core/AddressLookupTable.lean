/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Bytemuck

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AddressLookupTable

/-- All fields of the bincode metadata, including the observable padding. -/
structure Meta where
  deactivationSlot : UInt64
  lastExtendedSlot : UInt64
  lastExtendedSlotStartIndex : UInt8
  authority : Option Solanalib.Runtime.Pubkey
  padding : UInt16
  deriving DecidableEq, Repr

inductive Error where
  | invalidAccountData
  | uninitializedAccount
  deriving DecidableEq, Repr

/-- The addresses are borrowed from the input, at byte offset 56. The byte
view keeps the exact alias address and contents; source lifetimes, permissions
and target representation are separate Rust-binding obligations. -/
structure Value where
  metadata : Meta
  addresses : Bytemuck.SliceRef
  deriving DecidableEq, Repr

/-- Read a fixed-width field only when the entire field is available. -/
def field (bytes : Solanalib.Runtime.Bytes) (offset width : Nat) : Option Solanalib.Runtime.Bytes :=
  if offset + width ≤ bytes.length then some ((bytes.drop offset).take width) else none

/-- the fixed-width little-endian metadata decoder of Bincode. Its option tag is
one byte; None places the two padding bytes at 22, Some places them at 54.
Trailing data is accepted by `bincode::deserialize`. -/
def decodeMeta (bytes : Solanalib.Runtime.Bytes) : Option Meta := do
  let deactivation ← field bytes 4 8
  let extended ← field bytes 12 8
  let start ← field bytes 20 1
  let tag ← bytes[21]?
  let (authority, paddingOffset) ←
    if tag = 0 then some (none, 22)
    else if tag = 1 then do
      let key ← field bytes 22 32
      some (some (Solanalib.Runtime.Pubkey.ofBytes key), 54)
    else none
  let padding ← field bytes paddingOffset 2
  pure ⟨UInt64.ofNat (Solanalib.Runtime.leNat deactivation), UInt64.ofNat (Solanalib.Runtime.leNat
    extended),
    UInt8.ofNat (Solanalib.Runtime.leNat start), authority, UInt16.ofNat (Solanalib.Runtime.leNat
      padding)⟩

/-- Pubkey has size 32 and alignment 1 at both reviewed releases. No stronger
alignment is imposed because the source cast does not impose one. -/
def pubkeyLayout : Bytemuck.Layout := ⟨32, 1, ⟨0, rfl⟩, rfl⟩

/-- Decode the enum first, then reject Uninitialized, then take the suffix,
then cast it. The published 256-address limit is not enforced by this method. -/
def deserialize (input : Bytemuck.SliceRef) : Except Error Value :=
  match field input.bytes 0 4 with
  | none => .error .invalidAccountData
  | some tag =>
    if Solanalib.Runtime.leNat tag = 0 then .error .uninitializedAccount
    else if Solanalib.Runtime.leNat tag ≠ 1 then .error .invalidAccountData
    else match decodeMeta input.bytes with
    | none => .error .invalidAccountData
    | some metadata =>
      if 56 > input.bytes.length then .error .invalidAccountData
      else
        let suffix : Bytemuck.SliceRef := ⟨input.address + 56, input.bytes.drop 56⟩
        match Bytemuck.tryCastSlice .u8 pubkeyLayout suffix.address suffix.bytes.length with
        | .error _ => .error .invalidAccountData
        | .ok _ => .ok ⟨metadata, suffix⟩

/-- Success exposes the exact borrowed suffix, including its address. -/
theorem success_alias (input : Bytemuck.SliceRef) (table : Value)
    (success : deserialize input = .ok table) :
    table.addresses = ⟨input.address + 56, input.bytes.drop 56⟩ := by
  unfold deserialize at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  dsimp only at success
  split at success <;> cases success
  rfl

/-- A four-byte Uninitialized tag is sufficient; the 56-byte check is later. -/
theorem uninitialized_short (address : Nat) :
    deserialize ⟨address, [0, 0, 0, 0]⟩ = .error .uninitializedAccount := rfl

/-- Serialize metadata for boundary examples. The zero tail is outside the
bincode value when authority is None, and is intentionally ignored by decode. -/
def encodeMeta (metadata : Meta) : Solanalib.Runtime.Bytes :=
  Solanalib.Runtime.leBytes 4 1 ++ Solanalib.Runtime.leBytes 8 metadata.deactivationSlot.toNat ++
    Solanalib.Runtime.leBytes 8 metadata.lastExtendedSlot.toNat ++
      [metadata.lastExtendedSlotStartIndex] ++
    (match metadata.authority with | none => [0] | some key => [1] ++ key.bytes) ++
    Solanalib.Runtime.leBytes 2 metadata.padding.toNat

def defaultMeta : Meta := ⟨UInt64.ofNat (2^64 - 1), 0, 0, none, 0⟩

def sampleInput : Bytemuck.SliceRef :=
  ⟨17, encodeMeta defaultMeta ++ List.replicate 32 0 ++ List.replicate 32 7⟩

end Solanalib.Specs.Core.AddressLookupTable
