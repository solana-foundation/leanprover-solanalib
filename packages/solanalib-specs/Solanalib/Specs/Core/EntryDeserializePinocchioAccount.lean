/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.EntryDeserializePinocchio
public import Solanalib.Specs.Core.PinocchioAccount

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.EntryDeserialize.PinocchioAccounts

/-- Interpret the unchanged four-byte header as the signed i32 resize delta of the source. -/
def signedDelta (word : UInt32) : Int :=
  if word.toNat < 2^31 then word.toNat else (word.toNat : Int) - 2^32

/-- Install the exact initial data and hidden reserve in the common account vocabulary.
The source does not write its delta; a normal loader header has zero, and hence entryLen
equals dataLen. Nonzero headers retain the signed value and derive the historical length;
subsequent resize admission separately checks that this history is consistent. -/
def input (account : Account) : PinocchioAccount.Input :=
  ⟨account.key, account.owner, account.signer, account.writable, account.executable,
    account.lamports, ⟨account.data ++ account.spare, account.data.length,
      ((account.data.length : Int) - signedDelta account.reserved).toNat,
      signedDelta account.reserved⟩⟩

structure World where
  accounts : PinocchioAccount.State
  headers : List Nat
  handles : List PinocchioAccount.Handle
  deriving DecidableEq, Repr

def empty : World := ⟨PinocchioAccount.State.empty, [], []⟩

/-- The header table stores physical offsets once per unique account. A duplicate reads the
same earlier handle, even if that earlier slot was itself a duplicate. This installation is
an initial interpretation of one fresh input allocation, not a reset of a live borrow world. -/
def step (before : World) (slot : Slot) : Option World :=
  match slot.duplicate with
  | some earlier => do
    let handle ← before.handles[earlier]?
    pure { before with handles := before.handles ++ [handle] }
  | none =>
    let (handle, accounts) := before.accounts.insert (input slot.account)
    some ⟨accounts, before.headers ++ [slot.account.offset], before.handles ++ [handle]⟩

def install (parsed : Parsed) : Option World := parsed.slots.foldlM step empty

/-- A duplicate preserves the common field cells and the header-offset map, adding only
another alias of the precise earlier account handle. -/
theorem duplicate (before : World) (slot : Slot) (earlier : Nat)
    (isDuplicate : slot.duplicate = some earlier) (handle : PinocchioAccount.Handle)
    (present : before.handles[earlier]? = some handle) :
    step before slot = some { before with handles := before.handles ++ [handle] } := by
  simp [step, isDuplicate, present]

theorem input_data (account : Account) :
    (input account).data.bytes = account.data := by
  simp [input, PinocchioAccount.Data.bytes]

theorem loader_entry_length (account : Account) (zero : account.reserved = 0) :
    (input account).data.entryLen = account.data.length ∧
      (input account).data.resizeDelta = 0 := by
  simp [input, signedDelta, zero]

theorem install_empty : install ⟨[], 8, [], 16, .zero, 48⟩ = some empty := rfl

end Solanalib.Specs.Core.EntryDeserialize.PinocchioAccounts
