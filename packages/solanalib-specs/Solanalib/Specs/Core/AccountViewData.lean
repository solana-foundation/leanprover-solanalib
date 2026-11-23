/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewObservation

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- Common account contents, independent of a handle or guard. `backing` keeps
the allocated bytes, including the suffix outside the logical data length.
`ownerEpoch` records invalidation of owner references. The entry length and
signed length delta let version-specific extensions share this account
representation; header-only operations preserve those fields. -/
structure Account where
  /-- Address and access-flag observations supplied by the account input. -/
  metadata : Solanalib.Runtime.AccountMeta
  /-- The current owner address stored in the account header. -/
  owner : Solanalib.Runtime.Pubkey
  /-- The current working balance, bounded separately by the representation invariant. -/
  lamports : Nat
  /-- The currently exposed logical data length. -/
  dataLen : Nat
  /-- The original logical length recorded at invocation entry. -/
  entryLen : Nat
  /-- All allocated data bytes, including the currently hidden suffix. -/
  backing : Solanalib.Runtime.Bytes
  /-- A signed length delta, unchanged by header-only operations. -/
  resizeDelta : Int
  /-- The owner-reference generation, advanced by a modeled close. -/
  ownerEpoch : Nat
  deriving DecidableEq, Repr

/-- A contiguous view of account data. Typed Rust references are interpreted
by a separate decoder over this byte range; the range carries no snapshot. -/
structure Slice where
  /-- The byte offset in the allocated data of the account. -/
  offset : Nat
  /-- The number of bytes in this view. -/
  length : Nat
  deriving DecidableEq, Repr

/-- A view remains inside the currently exposed account data. -/
def Slice.ValidFor (view : Slice) (account : Account) : Prop :=
  view.offset + view.length ≤ account.dataLen

/-- The complete logical data range at acquisition. -/
def Account.whole (account : Account) : Slice := ⟨0, account.dataLen⟩

/-- The currently exposed bytes. Bytes beyond `dataLen` remain in `backing`. -/
def Account.bytes (account : Account) : Solanalib.Runtime.Bytes :=
  account.backing.take account.dataLen

/-- Read a view from the current contents, rather than an acquisition snapshot. -/
def Account.read (account : Account) (view : Slice) : Solanalib.Runtime.Bytes :=
  Solanalib.Runtime.slice account.backing view.offset view.length

/-- Integer and byte-range conditions of the common account model. These are
representation conditions, not writable, owner or signer authorization. -/
def Account.Valid (account : Account) : Prop :=
  account.lamports < Solanalib.Runtime.U64_LIMIT ∧ account.dataLen < Solanalib.Runtime.U64_LIMIT ∧
    account.entryLen < Solanalib.Runtime.U64_LIMIT ∧ account.dataLen ≤ account.backing.length

/-- Local balance replacement. Runtime authorization and conservation do not
belong to this SDK mutation. -/
def Account.setLamports (account : Account) (value : Nat) : Account :=
  { account with lamports := value }

/-- A write through a mutable data view changes those bytes immediately. The
caller supplies an equally sized byte sequence and a valid range. -/
def Account.write (account : Account) (view : Slice) (bytes : Solanalib.Runtime.Bytes) : Account :=
  { account with backing := Solanalib.Runtime.writeAt account.backing view.offset bytes }

/-- A source-independent empty account, used only as a total-reference fallback
and as a witness of satisfiable mathematical preconditions. -/
def Account.empty : Account :=
  ⟨⟨.zero, false, false, false⟩, .zero, 0, 0, 0, [], 0, 0⟩

instance : Inhabited Account := ⟨Account.empty⟩

/-- The entire logical range always fits the exposed length. -/
theorem Account.whole_valid (account : Account) : account.whole.ValidFor account := by
  simp [whole, Slice.ValidFor]

/-- Reading the complete view is exactly the logical byte observation. -/
theorem Account.read_whole (account : Account) : account.read account.whole = account.bytes := by
  simp [read, whole, bytes, Solanalib.Runtime.slice]

/-- A valid logical observation has its recorded length. -/
theorem Account.bytes_length {account : Account} (inside : account.dataLen ≤
  account.backing.length) :
    account.bytes.length = account.dataLen := by
  simp [bytes, List.length_take, Nat.min_eq_left inside]

/-- Reads of valid views return exactly the view length. -/
theorem Account.read_length {account : Account} (capacity : account.dataLen ≤
  account.backing.length)
    {view : Slice} (inside : view.ValidFor account) :
    (account.read view).length = view.length :=
  Solanalib.Runtime.length_slice_of_le (Nat.le_trans inside capacity)

/-- A same-size guarded write preserves the complete account representation. -/
theorem Account.write_valid {account : Account} (valid : account.Valid)
    {view : Slice} (inside : view.ValidFor account) {bytes : Solanalib.Runtime.Bytes}
    (sameSize : bytes.length = view.length) : (account.write view bytes).Valid := by
  have bound : view.offset + bytes.length ≤ account.backing.length := by
    rw [sameSize]
    exact Nat.le_trans inside valid.2.2.2
  exact ⟨valid.1, valid.2.1, valid.2.2.1, by
    simpa [write, Solanalib.Runtime.length_writeAt bound] using valid.2.2.2⟩

/-- Reading a just-written mutable view sees the new bytes immediately. -/
theorem Account.read_write {account : Account} (capacity : account.dataLen ≤ account.backing.length)
    {view : Slice} (inside : view.ValidFor account) {bytes : Solanalib.Runtime.Bytes}
    (sameSize : bytes.length = view.length) :
    (account.write view bytes).read view = bytes := by
  have bound : view.offset + bytes.length ≤ account.backing.length := by
    rw [sameSize]
    exact Nat.le_trans inside capacity
  simpa [write, read, sameSize] using Solanalib.Runtime.slice_writeAt_self bound

/-- A bounded local balance update preserves the account representation. -/
theorem Account.setLamports_valid {account : Account}
    (contents : account.dataLen < Solanalib.Runtime.U64_LIMIT ∧ account.entryLen <
      Solanalib.Runtime.U64_LIMIT ∧
      account.dataLen ≤ account.backing.length)
    {value : Nat} (bound : value < Solanalib.Runtime.U64_LIMIT) :
    (account.setLamports value).Valid := ⟨bound, contents⟩


/-- Header-only close invalidates owner references and retains physical data,
the entry length and any signed length delta in the shared representation. -/
def Account.closeHeader (account : Account) : Account :=
  { account with
    owner := .zero
    lamports := 0
    dataLen := 0
    ownerEpoch := account.ownerEpoch + 1 }

/-- Header-only close leaves every allocated data byte untouched. -/
theorem Account.closeHeader_backing (account : Account) :
    account.closeHeader.backing = account.backing := rfl

/-- Header-only close exposes empty logical data even when backing bytes remain. -/
theorem Account.closeHeader_bytes (account : Account) : account.closeHeader.bytes = [] := by
  simp [closeHeader, bytes]

/-- Header-only close preserves the finite account representation. -/
theorem Account.closeHeader_valid {account : Account} (entry : account.entryLen <
  Solanalib.Runtime.U64_LIMIT) :
    account.closeHeader.Valid :=
  ⟨by change 0 < Solanalib.Runtime.U64_LIMIT; decide,
    by change 0 < Solanalib.Runtime.U64_LIMIT; decide, entry, Nat.zero_le _⟩

/-- The closed fallback satisfies the common account representation. -/
theorem Account.empty_valid_core : Account.empty.Valid := by
  simp [Valid, empty, Solanalib.Runtime.U64_LIMIT]

end Solanalib.Specs.Core.AccountView
