/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.PinocchioToken2022.Instructions

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.PinocchioToken2022.Instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token.Request
open Solanalib.Specs.PinocchioToken2022.instructions
open Solanalib.Specs.Core.CpiRequest.Checked (directV2_iff prepareDirectV2 checkDirectV2
  invokePrepared invokePrepared_no_error Descriptor Syscall)

/-- The local wrapper does not authenticate the supplied token program. -/
theorem arbitrary_program_is_passed :
    (transferRequest CpiRequest.Checked.samplePool sampleTransfer []).instruction.programId =
      .zero := rfl

/-- Source and destination aliases are still two ordered arguments. -/
theorem repeated_account_values_are_retained :
    (transferRequest CpiRequest.Checked.samplePool sampleTransfer []).accounts =
      [⟨3⟩, ⟨5⟩, ⟨3⟩, ⟨9⟩] := rfl

/-- The amount, decimals and asymmetric flags agree with fixed local preparation. -/
theorem transfer_wire_and_flags :
    (transferRequest CpiRequest.Checked.samplePool sampleTransfer []).instruction.data =
      [12, 1, 2, 0, 0, 0, 0, 0, 0, 6] ∧
    (transferRequest CpiRequest.Checked.samplePool sampleTransfer []).instruction.metas.map
      (fun item => (item.signerByte, item.writableByte)) =
      [(0, 1), (0, 0), (0, 1), (1, 0)] := ⟨rfl, rfl⟩

/-- Close retains its exact discriminator, flags and three source identities. -/
theorem close_wire_and_flags :
    (closeRequest CpiRequest.Checked.samplePool sampleClose []).instruction.data = [9] ∧
    (closeRequest CpiRequest.Checked.samplePool sampleClose []).instruction.metas.map
      (fun item => (item.signerByte, item.writableByte)) = [(0, 1), (0, 1), (1, 0)] ∧
    (closeRequest CpiRequest.Checked.samplePool sampleClose []).accounts = [⟨3⟩, ⟨3⟩, ⟨9⟩] :=
  ⟨rfl, rfl, rfl⟩

/-- Empty groups and seeds remain nested and ordered. -/
theorem signed_seed_tree_preserved :
    (transferRequest CpiRequest.Checked.samplePool sampleTransfer [[], [[], [7, 8]]]).signers =
      [[], [[], [7, 8]]] := rfl

/-- A normal unchecked unit return becomes Ok and retains the changed callback state. -/
theorem invocation_normal_completion_effects :
    transfer_checked.TransferChecked.invoke_signed_reference sampleTypes (2 : Nat)
      sampleSignedTransfer
      (.returned (.ok ()) (6 : Nat)) := by
  unfold transfer_checked.TransferChecked.invoke_signed_reference
  apply (directV2_iff _ _ _ _ _ _).2
  simp [transferRequest, sampleSignedTransfer, sampleTransfer, sampleTypes, sampleProvider,
    CpiRequest.Checked.sampleHeaderTypes, CpiRequest.Checked.sampleTypes,
      CpiRequest.Checked.samplePool,
    CpiRequest.Checked.sampleProvider, prepareDirectV2, checkDirectV2, invokePrepared,
    Callback.map, Outcome.map, Except.map, AccountView.isBorrowed,
    Borrow.State.lease, Borrow.State.sharedCount, Borrow.State.exclusiveCount,
    Borrow.State.count, Token.Instruction.transferCheckedInstruction,
    Token.Instruction.authorityMetas, Instruction.accountMeta, CpiRequest.signed]
  exact ⟨_, rfl, rfl⟩

/-- An unwind records both the exact signer-group count and the descriptor count. -/
def unwindCall : SignedTransferCall sampleTypes := {
  sampleSignedTransfer with
  invoke := fun (before : Nat) request outcome =>
    outcome = .unwound request.signers.length (before + request.accounts.length) }

/-- All four checked descriptors precede the opaque unwind. -/
theorem invocation_unwind_effects :
    transfer_checked.TransferChecked.invoke_signed_reference sampleTypes (2 : Nat) unwindCall
      (.unwound (2 : Nat) (6 : Nat)) := by
  unfold transfer_checked.TransferChecked.invoke_signed_reference
  apply (directV2_iff _ _ _ _ _ _).2
  simp [transferRequest, unwindCall, sampleSignedTransfer, sampleTransfer, sampleTypes,
    CpiRequest.Checked.sampleHeaderTypes, CpiRequest.Checked.sampleTypes,
      CpiRequest.Checked.samplePool,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Token.Instruction.transferCheckedInstruction,
    Token.Instruction.authorityMetas, Instruction.accountMeta, CpiRequest.signed]
  exact ⟨_, rfl, rfl⟩

/-- A terminal boundary exit exposes no fabricated final state. -/
def terminalCall : SignedCloseCall sampleTypes := {
  sampleSignedClose with
  invoke := fun _ request outcome => outcome = .terminated request.accounts.length }

/-- The three-position close path preserves the terminal reason. -/
theorem invocation_terminal :
    close_account.CloseAccount.invoke_signed_reference sampleTypes (2 : Nat) terminalCall
      (.terminated (3 : Nat)) := by
  unfold close_account.CloseAccount.invoke_signed_reference
  apply (directV2_iff _ _ _ _ _ _).2
  simp [closeRequest, terminalCall, sampleSignedClose, sampleClose, sampleTypes,
    CpiRequest.Checked.sampleHeaderTypes, CpiRequest.Checked.sampleTypes,
      CpiRequest.Checked.samplePool,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Token.Instruction.authorityInstruction,
    Token.Instruction.authorityMetas, Instruction.accountMeta, CpiRequest.signed]
  exact ⟨_, rfl, rfl⟩

/-- The callback observes the signers actually sent by the unsigned wrapper. -/
def unsignedCall : UnsignedTransferCall sampleTypes := {
  sampleUnsignedTransfer with
  invoke := fun (before : Nat) request outcome =>
    outcome = .returned () (before + request.signers.length) }

/-- The checked unsigned path sends exactly zero signer groups. -/
theorem unsigned_has_no_signer_seeds :
    transfer_checked.TransferChecked.invoke_reference sampleTypes (2 : Nat) unsignedCall (.returned
      (.ok ()) (2 : Nat)) := by
  unfold transfer_checked.TransferChecked.invoke_reference
  apply (directV2_iff _ _ _ _ _ _).2
  simp [transferRequest, unsignedCall, sampleUnsignedTransfer, sampleTransfer, sampleTypes,
    CpiRequest.Checked.sampleHeaderTypes, CpiRequest.Checked.sampleTypes,
      CpiRequest.Checked.samplePool,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Token.Instruction.transferCheckedInstruction,
    Token.Instruction.authorityMetas, Instruction.accountMeta, CpiRequest.signed]
  exact ⟨_, rfl, rfl⟩

/-- Acquisition creates a live shared lease on the source/destination alias. -/
def borrowedPool : AccountView.State :=
  (AccountView.acquire CpiRequest.Checked.samplePool ⟨3⟩ .shared).2

/-- The rejection fixture uses an existing cell and a successfully acquired guard. -/
theorem source_shared_borrow_is_acquired :
    AccountView.acquire CpiRequest.Checked.samplePool ⟨3⟩ .shared =
      (.ok ⟨0, 0⟩, borrowedPool) ∧
    AccountView.isBorrowed borrowedPool ⟨3⟩ = true := ⟨rfl, rfl⟩

/-- Checks always observe the same current borrowed pool. -/
def borrowedTypes : Types where
  toTypes := ⟨Nat, fun _ => borrowedPool, Nat, Nat⟩
  rawHeader := fun _ => CpiRequest.Checked.normalizedHeader borrowedPool

/-- An impossible invocation makes the origin of the preflight error explicit. -/
def blockedTransfer : SignedTransferCall borrowedTypes where
  transfer := sampleTransfer
  signers := [[], [[7]]]
  invoke := fun _ _ _ => False

/-- A source borrow blocks TransferChecked before any invocation can occur. -/
theorem transfer_source_borrow_rejects
    (outcome : Outcome Nat (Except CpiRequest.Checked.Error Unit) Nat Nat) :
    transfer_checked.TransferChecked.invoke_signed_reference borrowedTypes (0 : Nat)
      blockedTransfer outcome ↔
      outcome = .returned (.error .AccountBorrowFailed) 0 := by
  unfold transfer_checked.TransferChecked.invoke_signed_reference
  apply (directV2_iff _ _ _ _ _ _).trans
  simp [transferRequest, blockedTransfer, sampleTransfer, borrowedTypes, borrowedPool,
    prepareDirectV2, checkDirectV2, Token.Instruction.transferCheckedInstruction,
    Token.Instruction.authorityMetas, Instruction.accountMeta, CpiRequest.signed,
    AccountView.isBorrowed, AccountView.acquire, AccountView.borrowResult, Borrow.acquire,
    CpiRequest.Checked.samplePool, Borrow.State.lookupCell, Borrow.State.lease,
    Borrow.State.sharedCount, Borrow.State.exclusiveCount, Borrow.State.count,
    Borrow.State.issue, Borrow.Policy.accountView]
  rfl

/-- Wider mathematical integers do not represent Rust u64/u8 arguments. -/
def wideTransfer : Transfer :=
  { sampleTransfer with amount := Solanalib.Runtime.U64_LIMIT, decimals := 256 }

/-- The existing encoder keeps its explicit byte conversion outside the Rust
integer domain; no new overflow result is added to the mathematical model. -/
theorem wide_transfer_encoding :
    ¬ (wideTransfer.amount < Solanalib.Runtime.U64_LIMIT ∧ wideTransfer.decimals < 256) ∧
    (transferRequest CpiRequest.Checked.samplePool wideTransfer []).instruction.data =
      [12, 0, 0, 0, 0, 0, 0, 0, 0, 0] := ⟨by decide, rfl⟩

/-- A real writable lease is still checked when mathematical scalars exceed
the source domain. The opaque callback remains impossible in this fixture. -/
def wideBlockedTransfer : SignedTransferCall borrowedTypes :=
  { blockedTransfer with transfer := wideTransfer }

/-- Signed-family admission no longer hides the already defined local borrow
error behind an unrelated scalar-width condition. -/
theorem wide_signed_transfer_borrow_error :
    (transfer_checked.TransferChecked.invoke_signed_contract.contract borrowedTypes).requires
      (0 : Nat) wideBlockedTransfer ∧
    transfer_checked.TransferChecked.invoke_signed_reference borrowedTypes (0 : Nat)
      wideBlockedTransfer
      (.returned (.error .AccountBorrowFailed) (0 : Nat)) := by
  refine ⟨True.intro, ?_⟩
  unfold transfer_checked.TransferChecked.invoke_signed_reference
  apply (directV2_iff _ _ _ _ _ _).2
  simp [transferRequest, wideBlockedTransfer, wideTransfer, blockedTransfer, sampleTransfer,
    borrowedTypes, borrowedPool, prepareDirectV2, checkDirectV2,
    Token.Instruction.transferCheckedInstruction, Token.Instruction.authorityMetas,
    Instruction.accountMeta, CpiRequest.signed, AccountView.isBorrowed, AccountView.acquire,
    AccountView.borrowResult, Borrow.acquire, CpiRequest.Checked.samplePool,
    Borrow.State.lookupCell, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Borrow.State.issue, Borrow.Policy.accountView]
  rfl

/-- The unsigned wrapper retains the same checked error with empty signer
seeds. Broadening mathematical admission does not skip the current lease check. -/
theorem wide_unsigned_transfer_borrow_error :
    let call : UnsignedTransferCall borrowedTypes := ⟨wideTransfer, fun _ _ _ => False⟩
    (transfer_checked.TransferChecked.invoke_contract.contract borrowedTypes).requires (0 : Nat)
      call ∧
    transfer_checked.TransferChecked.invoke_reference borrowedTypes (0 : Nat) call
      (.returned (.error .AccountBorrowFailed) (0 : Nat)) := by
  refine ⟨True.intro, ?_⟩
  unfold transfer_checked.TransferChecked.invoke_reference
  apply (directV2_iff _ _ _ _ _ _).2
  simp [transferRequest, wideTransfer, sampleTransfer, borrowedTypes, borrowedPool,
    prepareDirectV2, checkDirectV2, Token.Instruction.transferCheckedInstruction,
    Token.Instruction.authorityMetas, Instruction.accountMeta, CpiRequest.signed,
    AccountView.isBorrowed, AccountView.acquire, AccountView.borrowResult, Borrow.acquire,
    CpiRequest.Checked.samplePool, Borrow.State.lookupCell, Borrow.State.lease,
    Borrow.State.sharedCount, Borrow.State.exclusiveCount, Borrow.State.count,
    Borrow.State.issue, Borrow.Policy.accountView]
  rfl

/-- The first close account is free; the second account has the shared lease. -/
def blockedClose : SignedCloseCall borrowedTypes where
  close := { sampleClose with account := ⟨2⟩ }
  signers := []
  invoke := fun _ _ _ => False

/-- The close path rejects its second position and propagates that exact local error. -/
theorem close_destination_borrow_rejects
    (outcome : Outcome Nat (Except CpiRequest.Checked.Error Unit) Nat Nat) :
    close_account.CloseAccount.invoke_signed_reference borrowedTypes (0 : Nat) blockedClose outcome
      ↔
      outcome = .returned (.error .AccountBorrowFailed) 0 := by
  unfold close_account.CloseAccount.invoke_signed_reference
  apply (directV2_iff _ _ _ _ _ _).trans
  simp [closeRequest, blockedClose, sampleClose, borrowedTypes, borrowedPool,
    prepareDirectV2, checkDirectV2, Token.Instruction.authorityInstruction,
    Token.Instruction.authorityMetas, Instruction.accountMeta, CpiRequest.signed, Except.map,
    AccountView.isBorrowed, AccountView.acquire, AccountView.borrowResult, Borrow.acquire,
    CpiRequest.Checked.samplePool, Borrow.State.lookupCell, Borrow.State.lease,
    Borrow.State.sharedCount, Borrow.State.exclusiveCount, Borrow.State.count,
    Borrow.State.issue, Borrow.Policy.accountView]
  rfl

/-- Both readonly identities have independently acquired exclusive leases. -/
def readonlyPool : AccountView.State :=
  let mint := (AccountView.acquire CpiRequest.Checked.samplePool ⟨5⟩ .exclusive).2
  (AccountView.acquire mint ⟨9⟩ .exclusive).2

/-- The second acquisition succeeds while the first guard remains live. -/
theorem readonly_exclusive_borrows_are_acquired :
    AccountView.acquire (AccountView.acquire CpiRequest.Checked.samplePool ⟨5⟩ .exclusive).2
      ⟨9⟩ .exclusive = (.ok ⟨1, 0⟩, readonlyPool) ∧
    AccountView.isBorrowedMut readonlyPool ⟨5⟩ = true ∧
    AccountView.isBorrowedMut readonlyPool ⟨9⟩ = true := ⟨rfl, rfl, rfl⟩

/-- The v2 checked path observes both leases without acquiring another guard. -/
def readonlyTypes : Types where
  toTypes := ⟨Nat, fun _ => readonlyPool, Nat, Nat⟩
  rawHeader := fun _ => CpiRequest.Checked.normalizedHeader readonlyPool

/-- The mint is readonly and the authority is a readonly signer. -/
def readonlyCall : SignedTransferCall readonlyTypes where
  transfer := sampleTransfer
  signers := []
  invoke := sampleProvider

/-- Both readonly positions skip borrow admission in v2, including the signer position. -/
theorem readonly_exclusive_leases_reach_invocation :
    transfer_checked.TransferChecked.invoke_signed_reference readonlyTypes (2 : Nat) readonlyCall
      (.returned (.ok ()) (6 : Nat)) := by
  unfold transfer_checked.TransferChecked.invoke_signed_reference
  apply (directV2_iff _ _ _ _ _ _).2
  simp [transferRequest, readonlyCall, sampleTransfer, readonlyTypes, readonlyPool, sampleProvider,
    CpiRequest.Checked.sampleProvider, prepareDirectV2, checkDirectV2, invokePrepared,
    Callback.map, Outcome.map, Except.map, Token.Instruction.transferCheckedInstruction,
    Token.Instruction.authorityMetas, Instruction.accountMeta, CpiRequest.signed,
    AccountView.isBorrowed, AccountView.acquire, AccountView.borrowResult, Borrow.acquire,
    CpiRequest.Checked.samplePool, Borrow.State.lookupCell, Borrow.State.lease,
    Borrow.State.sharedCount, Borrow.State.exclusiveCount, Borrow.State.count, Borrow.State.issue]
  exact ⟨_, rfl, rfl⟩

/-- Every possible unchecked provider is constrained to its actual Unit return type. -/
theorem normal_invocation_cannot_inject_sdk_error (invoke : Syscall Nat Nat Nat)
    (failure : CpiRequest.Checked.Error) (after : Nat) :
    ¬ transfer_checked.TransferChecked.invoke_signed_reference sampleTypes (2 : Nat)
      { sampleSignedTransfer with invoke := invoke } (.returned (.error failure) after) := by
  intro execution
  unfold transfer_checked.TransferChecked.invoke_signed_reference at execution
  have checked := (directV2_iff _ _ _ _ _ _).1 execution
  simp [transferRequest, sampleSignedTransfer, sampleTransfer, sampleTypes,
    CpiRequest.Checked.sampleHeaderTypes, CpiRequest.Checked.sampleTypes,
      CpiRequest.Checked.samplePool,
    prepareDirectV2, checkDirectV2, Except.map, AccountView.isBorrowed,
    Borrow.State.lease, Borrow.State.sharedCount, Borrow.State.exclusiveCount,
    Borrow.State.count, Token.Instruction.transferCheckedInstruction,
    Token.Instruction.authorityMetas, Instruction.accountMeta, CpiRequest.signed] at checked
  exact invokePrepared_no_error _ _ _ _ _ _ _ checked

/-- Source and destination share a current two-byte account with true source flags. -/
def descriptorPool : AccountView.State :=
  (Borrow.modifyCell CpiRequest.Checked.samplePool ⟨3⟩ fun account =>
    { account with
      dataLen := 2
      entryLen := 2
      backing := [7, 8]
      metadata := { account.metadata with signer := true, executable := true } }).2

/-- The fixture supplies raw noncanonical flags and nonzero padding explicitly.
Both writable bytes 2 and 1 have the same true Boolean observation. -/
def descriptorHeader (account : AccountView.Handle) : CpiRequest.Checked.RawHeader :=
  if account = ⟨3⟩ then ⟨2, 2, 2, 173⟩
  else if account = ⟨5⟩ then ⟨0, 1, 0, 19⟩
  else CpiRequest.Checked.normalizedHeader descriptorPool account

/-- The concrete headers distinguish raw bytes that Boolean normalization would merge. -/
theorem raw_header_bytes_are_distinct :
    (descriptorHeader ⟨3⟩).isWritable = 2 ∧
    (descriptorHeader ⟨5⟩).isWritable = 1 ∧
    (descriptorPool.account ⟨3⟩).metadata.writable = true ∧
    (descriptorPool.account ⟨5⟩).metadata.writable = true ∧
    (descriptorHeader ⟨3⟩).padding = 173 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The callback records exactly the descriptor list it received as the final state. -/
def descriptorTypes : Types where
  toTypes := ⟨List Descriptor, fun _ => descriptorPool, Nat, Nat⟩
  rawHeader := fun _ => descriptorHeader

/-- This provider returns the real prepared list, without a presumed final-state equality. -/
def descriptorCall : SignedTransferCall descriptorTypes where
  transfer := sampleTransfer
  signers := [[], [[7, 8]]]
  invoke := fun _ request outcome => outcome = .returned () request.accounts

/-- Descriptor initialization retains aliases and exact raw flags, padding and lengths;
readonly instruction metadata does not replace the original account flag bytes. -/
theorem initialized_descriptors_record_current_accounts :
    transfer_checked.TransferChecked.invoke_signed_reference descriptorTypes ([] : List Descriptor)
      descriptorCall
      (.returned (.ok ())
        ([⟨⟨3⟩, 2, 0, 2, 2, 2, some 173⟩, ⟨⟨5⟩, 0, 0, 0, 1, 0, some 19⟩,
          ⟨⟨3⟩, 2, 0, 2, 2, 2, some 173⟩,
          ⟨⟨9⟩, 0, 0, 0, 1, 0, some 0⟩] : List Descriptor)) := by
  unfold transfer_checked.TransferChecked.invoke_signed_reference
  apply (directV2_iff _ _ _ _ _ _).2
  simp [transferRequest, descriptorCall, sampleTransfer, descriptorTypes, descriptorPool,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    Token.Instruction.transferCheckedInstruction, Token.Instruction.authorityMetas,
    Instruction.accountMeta, CpiRequest.signed, AccountView.isBorrowed,
    CpiRequest.Checked.samplePool, Borrow.modifyCell, Borrow.replaceCell, Borrow.State.lookupCell,
    Borrow.State.lease, Borrow.State.sharedCount, Borrow.State.exclusiveCount, Borrow.State.count]
  exact ⟨_, rfl, rfl⟩

end SolanalibTest.Specs.PinocchioToken2022.Instructions
