/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.PinocchioSystem.Request

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.PinocchioSystem

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.CpiRequest
open Solanalib.Specs.Core.CpiRequest.Checked
open Solanalib.Specs.PinocchioSystem.instructions

/-- A nontrivial u64 tests every little-endian byte of Allocate. -/
def allocateArgs : allocate.Allocate.Args allocate.Allocate.invoke_signed_sample :=
  { allocate.Allocate.sampleArgs with space := 0x0102030405060708 }

/-- Data, metadata, original handle and nested seeds agree with local preparation. -/
theorem allocate_exact_request :
    (allocate.Allocate.request (0 : Nat) allocateArgs).instruction.data =
      [8, 0, 0, 0, 8, 7, 6, 5, 4, 3, 2, 1] ∧
    (allocate.Allocate.request (0 : Nat) allocateArgs).instruction.metas = [⟨.ofNat 3, 1, 1⟩] ∧
    (allocate.Allocate.request (0 : Nat) allocateArgs).accounts = [⟨3⟩] ∧
    (allocate.Allocate.request (0 : Nat) allocateArgs).signers = [[], [[], [8, 9]]] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Owner serialization uses a nonzero public key. -/
def assignArgs : assign.Assign.Args assign.Assign.invoke_signed_sample :=
  { assign.Assign.sampleArgs with owner := Solanalib.Runtime.Pubkey.ofNat 9 }

/-- Assign retains every owner byte, current key and nested seed group. -/
theorem assign_exact_owner_bytes_and_signers :
    (assign.Assign.request (0 : Nat) assignArgs).instruction.data = [1, 0, 0, 0] ++
      assignArgs.owner.bytes ∧
    (assign.Assign.request (0 : Nat) assignArgs).instruction.metas = [⟨.ofNat 3, 1, 1⟩] ∧
    (assign.Assign.request (0 : Nat) assignArgs).signers = [[], [[], [8, 9]]] := ⟨rfl, rfl, rfl⟩

/-- Aliased source and destination retain separate flags and positions. -/
theorem transfer_keeps_duplicate_accounts_and_unsigned_call :
    (transfer.Transfer.request (0 : Nat) transfer.Transfer.sampleArgs).accounts = [⟨3⟩, ⟨3⟩] ∧
    (transfer.Transfer.request (0 : Nat) transfer.Transfer.sampleArgs).signers = [] ∧
    (transfer.Transfer.request (0 : Nat) transfer.Transfer.sampleArgs).instruction.metas =
      [⟨.ofNat 3, 1, 1⟩, ⟨.ofNat 3, 0, 1⟩] ∧
    (transfer.Transfer.request (0 : Nat) transfer.Transfer.sampleArgs).instruction.data =
      [2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0] := ⟨rfl, rfl, rfl, rfl⟩

/-- A real successful acquisition creates the lease that blocks writable CPI. -/
def borrowedPool : AccountView.State :=
  (AccountView.acquire samplePool ⟨3⟩ .shared).2

/-- The negative fixture comes from an actual acquisition of an existing cell. -/
theorem shared_borrow_is_acquired :
    AccountView.acquire samplePool ⟨3⟩ .shared = (.ok ⟨0, 0⟩, borrowedPool) ∧
    AccountView.isBorrowed borrowedPool ⟨3⟩ = true := ⟨rfl, rfl⟩

/-- The state counter is separate from the shared account pool. -/
def borrowedTypes : HeaderTypes where
  toTypes := ⟨Nat, fun _ => borrowedPool, Nat, Nat⟩
  rawHeader := fun _ => normalizedHeader borrowedPool

/-- An impossible invocation isolates a local checked rejection. -/
def impossibleInvoke : Syscall Nat Nat Nat := fun _ _ _ => False

/-- Allocate cannot reach its invocation with this live shared lease. -/
def blockedAllocate : allocate.Allocate.Args borrowedTypes where
  account := ⟨3⟩
  space := 5
  signers := [[], [[8]]]
  invoke := impossibleInvoke

/-- The only outcome is the unchanged-state borrow error, even with no invocation exit. -/
theorem allocate_live_borrow_rejects (outcome : Outcome Nat (Except Checked.Error Unit) Nat Nat) :
    allocate.Allocate.invoke_signed_run borrowedTypes (0 : Nat) blockedAllocate outcome ↔
      outcome = .returned (.error .AccountBorrowFailed) 0 := by
  apply (directV2_iff _ _ _ _ _ _).trans
  simp [allocate.Allocate.request, blockedAllocate, borrowedTypes, borrowedPool,
    prepareDirectV2, checkDirectV2, Instruction.systemAllocate, signed,
    Instruction.make, Instruction.accountMeta, AccountView.isBorrowed,
    AccountView.acquire, AccountView.borrowResult, Borrow.acquire,
    samplePool, Borrow.State.lookupCell, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Borrow.State.issue, Borrow.Policy.accountView]
  rfl

/-- Assign uses the same live account, rather than a copied borrow state. -/
def blockedAssign : assign.Assign.Args borrowedTypes where
  account := ⟨3⟩
  owner := .ofNat 9
  signers := []
  invoke := impossibleInvoke

/-- The checked borrow error from Assign propagates unchanged through its tail call. -/
theorem assign_live_borrow_rejects (outcome : Outcome Nat (Except Checked.Error Unit) Nat Nat) :
    assign.Assign.invoke_signed_run borrowedTypes (0 : Nat) blockedAssign outcome ↔
      outcome = .returned (.error .AccountBorrowFailed) 0 := by
  apply (directV2_iff _ _ _ _ _ _).trans
  simp [assign.Assign.request, blockedAssign, borrowedTypes, borrowedPool,
    prepareDirectV2, checkDirectV2, Instruction.systemAssign, signed,
    Instruction.make, Instruction.accountMeta, AccountView.isBorrowed,
    AccountView.acquire, AccountView.borrowResult, Borrow.acquire,
    samplePool, Borrow.State.lookupCell, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Borrow.State.issue, Borrow.Policy.accountView]
  rfl

/-- A free source precedes the borrowed destination, exercising the second position. -/
def blockedTransfer : transfer.Transfer.Args borrowedTypes where
  fromAccount := ⟨2⟩
  toAccount := ⟨3⟩
  lamports := 5
  invoke := impossibleInvoke

/-- The second-position failure prevents invocation after the first account was prepared. -/
theorem transfer_destination_borrow_rejects
    (outcome : Outcome Nat (Except Checked.Error Unit) Nat Nat) :
    transfer.Transfer.invoke_run borrowedTypes (0 : Nat) blockedTransfer outcome ↔
      outcome = .returned (.error .AccountBorrowFailed) 0 := by
  apply (directV2_iff _ _ _ _ _ _).trans
  simp [transfer.Transfer.request, blockedTransfer, borrowedTypes, borrowedPool,
    prepareDirectV2, checkDirectV2, Instruction.systemTransfer, unsigned,
    Instruction.make, Instruction.accountMeta, AccountView.isBorrowed,
    AccountView.acquire, AccountView.borrowResult, Borrow.acquire, Except.map,
    samplePool, Borrow.State.lookupCell, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Borrow.State.issue, Borrow.Policy.accountView]
  rfl

/-- Allocate actually traverses preparation and reaches the unit-returning callback. -/
theorem allocate_normal_completion_changes_state :
    allocate.Allocate.invoke_signed_run sampleHeaderTypes (0 : Nat) allocateArgs
      (.returned (.ok ()) (1 : Nat)) := by
  apply (directV2_iff _ _ _ _ _ _).2
  simp [allocate.Allocate.request, allocateArgs, allocate.Allocate.sampleArgs,
    allocate.Allocate.invoke_signed_sample, sampleHeaderTypes, sampleTypes, samplePool,
      sampleProvider,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Instruction.systemAllocate,
    signed, Instruction.make, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

/-- Assign reaches the same unit-returning boundary after checking its current account. -/
theorem assign_normal_completion_changes_state :
    assign.Assign.invoke_signed_run sampleHeaderTypes (0 : Nat) assignArgs
      (.returned (.ok ()) (1 : Nat)) := by
  apply (directV2_iff _ _ _ _ _ _).2
  simp [assign.Assign.request, assignArgs, assign.Assign.sampleArgs,
    assign.Assign.invoke_signed_sample, sampleHeaderTypes, sampleTypes, samplePool, sampleProvider,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Instruction.systemAssign,
    signed, Instruction.make, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

/-- Both alias occurrences reach the callback as two initialized descriptors. -/
theorem transfer_normal_completion_counts_both_aliases :
    transfer.Transfer.invoke_run sampleHeaderTypes (0 : Nat) transfer.Transfer.sampleArgs
      (.returned (.ok ()) (2 : Nat)) := by
  apply (directV2_iff _ _ _ _ _ _).2
  simp [transfer.Transfer.request, transfer.Transfer.sampleArgs,
    transfer.Transfer.invoke_sample, sampleHeaderTypes, sampleTypes, samplePool, sampleProvider,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Instruction.systemTransfer,
    unsigned, Instruction.make, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

/-- A terminal boundary exit is distinct from an ordinary SDK error. -/
def terminalTransfer : transfer.Transfer.Args sampleHeaderTypes :=
  { transfer.Transfer.sampleArgs with
    invoke := fun _ _ outcome => outcome = .terminated (19 : Nat) }

/-- The wrapper preserves terminal reasons after its own successful checks. -/
theorem transfer_forwards_terminal_reason :
    transfer.Transfer.invoke_run sampleHeaderTypes (0 : Nat) terminalTransfer (.terminated (19 :
      Nat)) := by
  apply (directV2_iff _ _ _ _ _ _).2
  simp [transfer.Transfer.request, terminalTransfer, transfer.Transfer.sampleArgs,
    transfer.Transfer.invoke_sample, sampleHeaderTypes, sampleTypes, samplePool,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Instruction.systemTransfer,
    unsigned, Instruction.make, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

end SolanalibTest.Specs.PinocchioSystem
