/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaAccountView

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaAccountView.AccountView

open Solanalib.Specs.SolanaAccountView.AccountView.Observation

/-- A client learns the new balance from the setter and getter contracts alone. -/
theorem set_then_read {operations : Operations} (spec : Spec operations)
    (before : State) (value : Nat) (valid : value < _root_.Solanalib.Runtime.U64_LIMIT) :
    (operations.lamports (operations.setLamports before value).2 ()).1 = value := by
  have changed := spec.setLamports before value valid
  have read := spec.lamports (operations.setLamports before value).2 () trivial
  change (operations.setLamports before value).2 = before.setLamports value at changed
  rw [read.2, changed]
  rfl

/-- A write to the balance preserves the signer flag and data length observed by
two other API calls. The proof does not unfold any implementation. -/
theorem set_preserves_header {operations : Operations} (spec : Spec operations)
    (before : State) (value : Nat) (valid : value < _root_.Solanalib.Runtime.U64_LIMIT) :
    (operations.isSigner (operations.setLamports before value).2 ()).1 = before.metadata.signer ∧
    (operations.dataLen (operations.setLamports before value).2 ()).1 = before.account.dataLen := by
  have changed := spec.setLamports before value valid
  have signer := spec.isSigner (operations.setLamports before value).2 () trivial
  have length := spec.dataLen (operations.setLamports before value).2 () trivial
  change (operations.setLamports before value).2 = before.setLamports value at changed
  rw [signer.2, length.2, changed]
  exact ⟨rfl, rfl⟩

def available : State where
  metadata := ⟨.zero, true, true, false⟩
  account := ⟨.zero, 40, 3, 3, .free, some [10, 20, 30]⟩

theorem available_valid : available.Valid :=
  ⟨by decide, by decide, [10, 20, 30], rfl, rfl⟩

def saturated : State :=
  { available with account := { available.account with lease := .shared 254 } }

theorem saturated_valid : saturated.Valid :=
  ⟨by decide, by decide, by decide, by decide, [10, 20, 30], rfl, rfl⟩

/-- The caller can satisfy the precondition at the exact shared-guard limit,
and the specification forces AccountBorrowFailed without changing the state. -/
theorem saturated_borrow_fails {operations : Operations} (spec : Spec operations) :
    operations.tryBorrow saturated () = (.error .accountBorrowFailed, saturated) := by
  have contract := spec.tryBorrow saturated () saturated_valid
  cases result : operations.tryBorrow saturated () with
  | mk outcome after =>
    rw [result] at contract
    cases outcome with
    | ok bytes =>
      simp [try_borrow_contract, saturated, _root_.Solanalib.Runtime.Lease.addShared] at contract
    | error error =>
      cases error
      exact congrArg (Prod.mk (Except.error BorrowError.accountBorrowFailed : BorrowResult))
        contract.2

/-- A concrete normal shared acquisition witnesses a satisfiable success case. -/
theorem shared_success :
    (reference.tryBorrow available ()).1 = .ok [10, 20, 30] ∧
    (reference.tryBorrow available ()).2.account.lease = .shared 1 := ⟨rfl, rfl⟩

/-- The mutable guard owns the bytes while the account view hides them. -/
theorem mutable_success :
    (reference.tryBorrowMut available ()).1 = .ok [10, 20, 30] ∧
    (reference.tryBorrowMut available ()).2.account.lease = .exclusive ∧
    (reference.tryBorrowMut available ()).2.account.data = none := ⟨rfl, rfl, rfl⟩

/-- Every interpretation satisfying `Spec` must successfully borrow this free
account; the client uses the contract, without unfolding an implementation. -/
theorem shared_success_of_spec {operations : Operations} (spec : Spec operations) :
    operations.tryBorrow available () = (.ok [10, 20, 30], available.withLease (.shared 1)) := by
  have contract := spec.tryBorrow available () available_valid
  cases result : operations.tryBorrow available () with
  | mk outcome after =>
    rw [result] at contract
    cases outcome with
    | ok bytes =>
      simp [try_borrow_contract, available, _root_.Solanalib.Runtime.Lease.addShared] at contract
      rcases contract with ⟨rfl, rfl⟩
      rfl
    | error error =>
      cases error
      simp [try_borrow_contract, available, canBorrow] at contract

/-- Every interpretation satisfying `Spec` must return the bytes and hide them
from this free account when a mutable borrow is requested. -/
theorem mutable_success_of_spec {operations : Operations} (spec : Spec operations) :
    operations.tryBorrowMut available () = (.ok [10, 20, 30], available.withLease .exclusive) := by
  have contract := spec.tryBorrowMut available () available_valid
  cases result : operations.tryBorrowMut available () with
  | mk outcome after =>
    rw [result] at contract
    cases outcome with
    | ok bytes =>
      simp [try_borrow_mut_contract, available] at contract
      rcases contract with ⟨rfl, rfl⟩
      rfl
    | error error =>
      cases error
      simp [try_borrow_mut_contract, available, canBorrowMut] at contract

end SolanalibTest.Specs.SolanaAccountView.AccountView
