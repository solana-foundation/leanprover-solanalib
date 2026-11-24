/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountView
public import Solanalib.Specs.Core.SysvarRent

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Sysvar

/-- The handle denotes a current account. Only the reached unchecked rate read
needs eight bytes; an earlier borrow or address error needs no data extent. -/
def Rent111ReadReady (state : AccountView.State) (handle : AccountView.Handle) : Prop :=
  state.HasAccount handle ∧
    (AccountView.isBorrowedMut state handle = false →
      (state.account handle).metadata.address = Solanalib.Runtime.Ids.sysvarRent →
      8 ≤ (state.account handle).bytes.length)

/-- Ordered errors or a complete eight-byte rate read from the selected cell.
The source load is unaligned; pointer alignment is not an admission condition. -/
def Rent111ReadResult (state : AccountView.State) (handle : AccountView.Handle)
    (result : Except ProgramError.Value Rent111) : Prop :=
  ∃ cell, state.lookupCell handle = some cell ∧
    if AccountView.isBorrowedMut state handle then result = .error .accountBorrowFailed
    else if cell.value.metadata.address ≠ Solanalib.Runtime.Ids.sysvarRent then
      result = .error .invalidArgument
    else (cell.value.bytes.take 8).length = 8 ∧
      result = .ok ⟨UInt64.ofNat (Solanalib.Runtime.leNat (cell.value.bytes.take 8))⟩

/-- Pinocchio 0.11.1 tests the exclusive lease before the key, copies the
little-endian rate, and never acquires a shared guard. Source correspondence
must establish the selected little-endian target. The source-facing contract
requires `Rent111ReadReady` to exclude the raw short-data fallback. -/
def rent111FromAccount (state : AccountView.State) (handle : AccountView.Handle) :
    Except ProgramError.Value Rent111 × AccountView.State :=
  if AccountView.isBorrowedMut state handle then (.error .accountBorrowFailed, state)
  else if (state.account handle).metadata.address ≠ Solanalib.Runtime.Ids.sysvarRent then
    (.error .invalidArgument, state)
  else (.ok ⟨UInt64.ofNat (Solanalib.Runtime.leNat ((state.account handle).bytes.take 8))⟩, state)

theorem rent111FromAccount_preserves_state (state : AccountView.State)
    (handle : AccountView.Handle) : (rent111FromAccount state handle).2 = state := by
  unfold rent111FromAccount
  split
  · rfl
  · split <;> rfl

/-- Admission gives a real cell on every branch and a complete rate read on
success, while preserving the earlier borrow of the source and address errors. -/
theorem rent111FromAccount_read {state : AccountView.State} {handle : AccountView.Handle}
    (ready : Rent111ReadReady state handle) :
    Rent111ReadResult state handle (rent111FromAccount state handle).1 := by
  obtain ⟨⟨cell, present⟩, extent⟩ := ready
  have account := AccountView.State.account_of_lookup present
  refine ⟨cell, present, ?_⟩
  cases borrowed : AccountView.isBorrowedMut state handle with
  | true => simp [rent111FromAccount, borrowed]
  | false =>
    by_cases address : cell.value.metadata.address = Solanalib.Runtime.Ids.sysvarRent
    · have length := extent borrowed (by simpa only [account] using address)
      rw [account] at length
      simp only [rent111FromAccount, borrowed, account, address, ne_eq,
        not_true_eq_false, Bool.false_eq_true, ite_false]
      simp [List.length_take, Nat.min_eq_left length]
    · simp [rent111FromAccount, borrowed, account, address]

theorem rent111FromAccount_exclusive_first (state : AccountView.State)
    (handle : AccountView.Handle) (exclusive : AccountView.isBorrowedMut state handle = true) :
    rent111FromAccount state handle = (.error .accountBorrowFailed, state) := by
  simp only [rent111FromAccount, exclusive, ite_true]

namespace Witness

/-- A finite model world for closed source-facing examples. -/
def singleAccount (account : AccountView.Account) : AccountView.State :=
  ⟨[⟨account, Borrow.Policy.accountView⟩], []⟩

def handle : AccountView.Handle := ⟨0⟩
def guard : AccountView.Guard := ⟨0, 0⟩

def singleGuard (account : AccountView.Account) (mode : Borrow.Mode) : AccountView.State :=
  { singleAccount account with slots := [some ⟨handle, mode, 0, account.whole⟩] }

def rentAccount : AccountView.Account :=
  { AccountView.Account.empty with
    metadata := ⟨Solanalib.Runtime.Ids.sysvarRent, false, false, false⟩
    dataLen := 8
    entryLen := 8
    backing := (Rent111.mk 6960).encode }

theorem rentAccount_ready : Rent111ReadReady (singleAccount rentAccount) handle := by
  refine ⟨⟨⟨rentAccount, Borrow.Policy.accountView⟩, rfl⟩, ?_⟩
  intro _ _
  decide

end Witness

end Solanalib.Specs.Core.Sysvar
