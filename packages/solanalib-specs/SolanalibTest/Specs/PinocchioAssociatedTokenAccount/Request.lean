/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.PinocchioAssociatedTokenAccount.Request

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.PinocchioAssociatedTokenAccount

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.CpiRequest
open Solanalib.Specs.Core.CpiRequest.Checked
open Solanalib.Specs.PinocchioAssociatedTokenAccount.instructions.create_idempotent.CreateIdempotent

/-- The funding/wallet alias remains in both source positions. -/
theorem exact_account_order_retains_alias :
    (request (0 : Nat) sampleArgs).accounts = [⟨3⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩] := rfl

/-- Fixed flags, discriminator and empty signer tree are source preparation facts. -/
theorem exact_flags_data_and_empty_signers :
    (request (0 : Nat) sampleArgs).instruction.metas.map
      (fun item => (item.signerByte, item.writableByte)) =
      [(1, 1), (0, 1), (0, 0), (0, 0), (0, 0), (0, 0)] ∧
    (request (0 : Nat) sampleArgs).instruction.data = [1] ∧
    (request (0 : Nat) sampleArgs).signers = [] := ⟨rfl, rfl, rfl⟩

/-- The actual current System and Token account keys differ from the standard IDs. -/
def programPool : AccountView.State :=
  let first := (Borrow.modifyCell samplePool ⟨5⟩ fun account =>
    { account with metadata := { account.metadata with address := .ofNat 17 } }).2
  (Borrow.modifyCell first ⟨6⟩ fun account =>
    { account with metadata := { account.metadata with address := .ofNat 19 } }).2

/-- Current program-account keys are supplied through the state interpretation. -/
def programTypes : HeaderTypes where
  toTypes := ⟨Nat, fun _ => programPool, Nat, Nat⟩
  rawHeader := fun _ => normalizedHeader programPool

/-- The wrapper still receives actual source handles, without independent key fields. -/
def suppliedPrograms : Args programTypes where
  fundingAccount := ⟨3⟩
  account := ⟨2⟩
  wallet := ⟨3⟩
  mint := ⟨4⟩
  systemProgram := ⟨5⟩
  tokenProgram := ⟨6⟩
  invoke := sampleProvider

/-- The wrapper preserves the supplied current program addresses without authentication. -/
theorem supplied_program_addresses_are_preserved :
    ((request (0 : Nat) suppliedPrograms).instruction.metas.drop 4).map (·.key) =
      [Solanalib.Runtime.Pubkey.ofNat 17, Solanalib.Runtime.Pubkey.ofNat 19] := rfl

/-- Six descriptors reach normal opaque completion, retaining its actual changed state. -/
theorem normal_completion_retains_provider_state :
    invoke_run sampleHeaderTypes (2 : Nat) sampleArgs (.returned (.ok ()) (8 : Nat)) := by
  apply (directV2_iff _ _ _ _ _ _).2
  simp [request, sampleArgs, invoke_sample, sampleHeaderTypes, sampleTypes, samplePool,
    sampleProvider,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Instruction.associatedTokenCreateIdempotent,
    unsigned, Instruction.make, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

/-- An opaque unwind is preserved after successful checked preparation. -/
def unwindArgs : Args invoke_sample :=
  { sampleArgs with invoke := fun _ _ outcome => outcome = .unwound (23 : Nat) (7 : Nat) }

/-- Unwinding retains the actual state of the callback, with no invented wrapper cleanup. -/
theorem unwind_retains_provider_state :
    invoke_run sampleHeaderTypes (0 : Nat) unwindArgs (.unwound (23 : Nat) (7 : Nat)) := by
  apply (directV2_iff _ _ _ _ _ _).2
  simp [request, unwindArgs, sampleArgs, invoke_sample, sampleHeaderTypes, sampleTypes, samplePool,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Instruction.associatedTokenCreateIdempotent,
    unsigned, Instruction.make, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

/-- The writable associated-account position has an actual exclusive guard. -/
def borrowedPool : AccountView.State :=
  (AccountView.acquire samplePool ⟨2⟩ .exclusive).2

/-- The rejection fixture derives from successful acquisition of an existing account. -/
theorem associated_exclusive_borrow_is_acquired :
    AccountView.acquire samplePool ⟨2⟩ .exclusive = (.ok ⟨0, 0⟩, borrowedPool) ∧
    AccountView.isBorrowedMut borrowedPool ⟨2⟩ = true := ⟨rfl, rfl⟩

/-- The current borrowed account pool is exposed at every checked observation. -/
def borrowedTypes : HeaderTypes where
  toTypes := ⟨Nat, fun _ => borrowedPool, Nat, Nat⟩
  rawHeader := fun _ => normalizedHeader borrowedPool

/-- No callback execution is possible; any observed error must be local. -/
def blockedArgs : Args borrowedTypes where
  fundingAccount := ⟨3⟩
  account := ⟨2⟩
  wallet := ⟨3⟩
  mint := ⟨4⟩
  systemProgram := ⟨5⟩
  tokenProgram := ⟨6⟩
  invoke := fun _ _ _ => False

/-- The second writable position fails after funding preparation and before invocation. -/
theorem associated_borrow_rejects_before_invocation
    (outcome : Outcome Nat (Except Checked.Error Unit) Nat Nat) :
    invoke_run borrowedTypes (0 : Nat) blockedArgs outcome ↔
      outcome = .returned (.error .AccountBorrowFailed) 0 := by
  apply (directV2_iff _ _ _ _ _ _).trans
  simp [request, blockedArgs, borrowedTypes, borrowedPool,
    prepareDirectV2, checkDirectV2, Instruction.associatedTokenCreateIdempotent, unsigned,
    Instruction.make, Instruction.accountMeta, AccountView.isBorrowed,
    AccountView.acquire, AccountView.borrowResult, Borrow.acquire, Except.map,
    samplePool, Borrow.State.lookupCell, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Borrow.State.issue]
  rfl

/-- Use a separate readonly wallet identity, so its lease cannot alias a writable position. -/
def readonlyPool : AccountView.State :=
  (AccountView.acquire samplePool ⟨8⟩ .exclusive).2

/-- The readonly fixture also comes from a real, live exclusive acquisition. -/
theorem readonly_exclusive_borrow_is_acquired :
    AccountView.acquire samplePool ⟨8⟩ .exclusive = (.ok ⟨0, 0⟩, readonlyPool) ∧
    AccountView.isBorrowedMut readonlyPool ⟨8⟩ = true := ⟨rfl, rfl⟩

/-- All local checks observe the same readonly-wallet lease. -/
def readonlyTypes : HeaderTypes where
  toTypes := ⟨Nat, fun _ => readonlyPool, Nat, Nat⟩
  rawHeader := fun _ => normalizedHeader readonlyPool

/-- The selected v2 array helper skips borrow admission for this readonly wallet. -/
def readonlyArgs : Args readonlyTypes where
  fundingAccount := ⟨3⟩
  account := ⟨2⟩
  wallet := ⟨8⟩
  mint := ⟨4⟩
  systemProgram := ⟨5⟩
  tokenProgram := ⟨6⟩
  invoke := sampleProvider

/-- This complete successful run distinguishes the selected v2 behavior from v1. -/
theorem readonly_exclusive_lease_reaches_invocation :
    invoke_run readonlyTypes (2 : Nat) readonlyArgs (.returned (.ok ()) (8 : Nat)) := by
  apply (directV2_iff _ _ _ _ _ _).2
  simp [request, readonlyArgs, readonlyTypes, readonlyPool, sampleProvider,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    Instruction.associatedTokenCreateIdempotent, unsigned,
    Instruction.make, Instruction.accountMeta, AccountView.isBorrowed,
    AccountView.acquire, AccountView.borrowResult, Borrow.acquire,
    samplePool, Borrow.State.lookupCell, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Borrow.State.issue]
  exact ⟨_, rfl, rfl⟩

end SolanalibTest.Specs.PinocchioAssociatedTokenAccount
