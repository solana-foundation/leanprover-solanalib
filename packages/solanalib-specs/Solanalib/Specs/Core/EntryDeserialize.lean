/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Basic
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.EntryDeserialize

/-- The aligned loader format reserves this many bytes after the data of each unique account. -/
def growth : Nat := 10240

/-- Both reviewed implementations use eight-byte alignment even on hosts with wider u128. -/
def align8 (offset : Nat) : Nat := offset + (8 - offset % 8) % 8

/-- A bounded byte range. Absence describes an invalid serialized input, not a Rust error. -/
def slice? (bytes : Solanalib.Runtime.Bytes) (offset size : Nat) : Option Solanalib.Runtime.Bytes :=
  if offset + size ≤ bytes.length then some ((bytes.drop offset).take size) else none

/-- Little-endian decoding at the exact field width of the source. -/
def word? (bytes : Solanalib.Runtime.Bytes) (offset width : Nat) : Option Nat :=
  (slice? bytes offset width).map Solanalib.Runtime.leNat

/-- The initial bytes and locations of a unique account. The four-byte field is raw:
the SDK overwrites it with the original length; Pinocchio leaves its resize delta alone.
`offset` identifies storage, so equal keys in two unique entries remain distinct. -/
structure Account where
  offset : Nat
  signer : UInt8
  writable : UInt8
  executable : UInt8
  reserved : UInt32
  key : Solanalib.Runtime.Pubkey
  owner : Solanalib.Runtime.Pubkey
  lamports : UInt64
  data : Solanalib.Runtime.Bytes
  spare : Solanalib.Runtime.Bytes
  padding : Solanalib.Runtime.Bytes
  rentEpoch : UInt64
  deriving DecidableEq, Repr

def Account.keyOffset (account : Account) : Nat := account.offset + 8
def Account.ownerOffset (account : Account) : Nat := account.offset + 40
def Account.lamportsOffset (account : Account) : Nat := account.offset + 72
def Account.lengthOffset (account : Account) : Nat := account.offset + 80
def Account.dataOffset (account : Account) : Nat := account.offset + 88
def Account.rentOffset (account : Account) : Nat :=
  align8 (account.dataOffset + account.data.length + growth)

/-- A serialized slot and its resolved account. A duplicate carries the exact earlier slot
index, including a duplicate of a duplicate, and aliases the storage identity of that slot. -/
structure Slot where
  offset : Nat
  duplicate : Option Nat
  duplicatePadding : Solanalib.Runtime.Bytes
  account : Account
  deriving DecidableEq, Repr

/-- The parsed views into one input buffer. Suffix bytes after the program key are allowed
and remain part of the owned buffer, but neither implementation reads them. -/
structure Parsed where
  slots : List Slot
  instructionLengthOffset : Nat
  instructionData : Solanalib.Runtime.Bytes
  programOffset : Nat
  programId : Solanalib.Runtime.Pubkey
  endOffset : Nat
  deriving DecidableEq, Repr

def Parsed.accounts (parsed : Parsed) : List Account := parsed.slots.map (·.account)

/-- Unique accounts in source order; duplicate slots do not allocate new cells. -/
def Parsed.unique (parsed : Parsed) : List Account :=
  parsed.slots.filterMap fun slot => if slot.duplicate.isNone then some slot.account else none

def Parsed.instructionOffset (parsed : Parsed) : Nat := parsed.instructionLengthOffset + 8

/-- Decode one unique entry, preserving the full realloc reserve and alignment padding.
The 10 MiB bound is the account-data limit of the loader, and is stronger than pointer-width
or u32 representability. It is an input-format boundary, not a theorem about arbitrary buffers. -/
def account? (bytes : Solanalib.Runtime.Bytes) (offset : Nat) : Option (Account × Nat) := do
  let _ ← slice? bytes offset 88
  let length ← word? bytes (offset + 80) 8
  if length > 10485760 then none else do
    let rentOffset := align8 (offset + 88 + length + growth)
    let _ ← slice? bytes offset (rentOffset + 8 - offset)
    let data ← slice? bytes (offset + 88) length
    let spare ← slice? bytes (offset + 88 + length) growth
    let padding ← slice? bytes (offset + 88 + length + growth)
      (rentOffset - (offset + 88 + length + growth))
    let key ← slice? bytes (offset + 8) 32
    let owner ← slice? bytes (offset + 40) 32
    let reserved ← word? bytes (offset + 4) 4
    let lamports ← word? bytes (offset + 72) 8
    let rentEpoch ← word? bytes rentOffset 8
    pure (⟨offset, bytes[offset + 1]!, bytes[offset + 2]!, bytes[offset + 3]!,
      UInt32.ofNat reserved, Solanalib.Runtime.Pubkey.ofBytes key, Solanalib.Runtime.Pubkey.ofBytes
        owner,
      UInt64.ofNat lamports, data, spare, padding, UInt64.ofNat rentEpoch⟩, rentOffset + 8)

/-- The mathematical parser validates backward duplicate indices before resolving them.
Neither unsafe source implementation supplies these checks to its caller. -/
def slots? (bytes : Solanalib.Runtime.Bytes) : Nat → Nat → List Slot → Option (List Slot × Nat)
  | 0, offset, slots => some (slots, offset)
  | count + 1, offset, slots => do
    let _ ← slice? bytes offset 8
    let marker := bytes[offset]!
    if marker = 255 then
      let (account, next) ← account? bytes offset
      slots? bytes count next (slots ++ [⟨offset, none, [], account⟩])
    else
      let previous ← slots[marker.toNat]?
      let padding ← slice? bytes (offset + 1) 7
      slots? bytes count (offset + 8)
        (slots ++ [⟨offset, some marker.toNat, padding, previous.account⟩])

/-- Decode the reviewed aligned loader format. Bad byte ranges or duplicate references
are inadmissible, not modeled `Err` or panic results. Account-count restrictions belong
to the selected source API: the SDK does not inherit the 254-account limit of Pinocchio. -/
def parse (bytes : Solanalib.Runtime.Bytes) : Option Parsed := do
  let count ← word? bytes 0 8
  let (slots, offset) ← slots? bytes count 8 []
  let length ← word? bytes offset 8
  let instructionData ← slice? bytes (offset + 8) length
  let programOffset := offset + 8 + length
  let program ← slice? bytes programOffset 32
  pure ⟨slots, offset, instructionData, programOffset,
    Solanalib.Runtime.Pubkey.ofBytes program, programOffset + 32⟩

/-- Replace an existing range; length preservation is used by the source binding. -/
def overwrite (bytes : Solanalib.Runtime.Bytes) (offset : Nat) (replacement :
  Solanalib.Runtime.Bytes) :
    Solanalib.Runtime.Bytes := bytes.take offset ++ replacement ++ bytes.drop (offset +
      replacement.length)

/-- The only writes into the input buffer performed by the SDK deserializer. -/
def recordOriginalLengths (bytes : Solanalib.Runtime.Bytes) (accounts : List Account) :
  Solanalib.Runtime.Bytes :=
  accounts.foldl (fun current account =>
    overwrite current (account.offset + 4) (Solanalib.Runtime.leBytes 4 account.data.length)) bytes

/-- Pointer-returning fields shared by the two source APIs. Values remain paired with their
buffer offsets, which prevents a matching byte snapshot from forgetting reference identity. -/
structure Views where
  programOffset : Nat
  programId : Solanalib.Runtime.Pubkey
  instructionOffset : Nat
  instructionData : Solanalib.Runtime.Bytes
  deriving DecidableEq, Repr

def Parsed.views (parsed : Parsed) : Views :=
  ⟨parsed.programOffset, parsed.programId, parsed.instructionOffset, parsed.instructionData⟩

/-- An empty, nonempty-buffer witness: the count, instruction length and program key
still require real initialized bytes. -/
def emptyBytes : Solanalib.Runtime.Bytes := List.replicate 48 0

theorem parse_empty : parse emptyBytes = some ⟨[], 8, [], 16, .zero, 48⟩ := by decide

theorem overwrite_length (bytes replacement : Solanalib.Runtime.Bytes) (offset : Nat)
    (fits : offset + replacement.length ≤ bytes.length) :
    (overwrite bytes offset replacement).length = bytes.length := by
  simp only [overwrite, List.length_append, List.length_take, List.length_drop]
  rw [Nat.min_eq_left (by omega)]
  omega

end Solanalib.Specs.Core.EntryDeserialize
