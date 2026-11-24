/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewProjection

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Six single-account observation contracts. Acquisition returns byte observations;
AccountView.Pool provides the complete pool and identified-guard API. State and
reference operations use the shared observation model. The Spec fields expose
the contract statements for client proofs. -/

namespace Solanalib.Specs.SolanaAccountView.AccountView.Observation

export Solanalib.Specs.Core.AccountViewObservation
  (State BorrowError BorrowResult canBorrow canBorrowMut Operations)

namespace State

export Solanalib.Specs.Core.AccountViewObservation.State
  (mk metadata account Valid setLamports withLease)

end State

namespace BorrowError

export Solanalib.Specs.Core.AccountViewObservation.BorrowError (accountBorrowFailed)

end BorrowError

namespace Operations

export Solanalib.Specs.Core.AccountViewObservation.Operations
  (mk setLamports lamports dataLen isSigner tryBorrow tryBorrowMut)

end Operations

/-- A bounded balance replacement in the single-account observation. -/
def set_lamports_contract : Solanalib.Contracts.Model State Nat Unit :=
  .returning
    (fun _ value => value < _root_.Solanalib.Runtime.U64_LIMIT)
    (fun before value _ after => after = before.setLamports value)

/-- Read the projected balance without changing the observation. -/
def lamports_contract : Solanalib.Contracts.Model State Unit Nat :=
  .returning
    (fun _ _ => True)
    (fun before _ value after => after = before ∧ value = before.account.lamports)

/-- Read the projected logical data length without changing the observation. -/
def data_len_contract : Solanalib.Contracts.Model State Unit Nat :=
  .returning
    (fun _ _ => True)
    (fun before _ value after => after = before ∧ value = before.account.dataLen)

/-- Read the signer observation without conferring authority. -/
def is_signer_contract : Solanalib.Contracts.Model State Unit Bool :=
  .returning
    (fun _ _ => True)
    (fun before _ value after => after = before ∧ value = before.metadata.signer)

/-- Shared acquisition returns current bytes and increments the observed lease.
Failure preserves the observation. The result does not retain a guard identity. -/
def try_borrow_contract : Solanalib.Contracts.Model State Unit BorrowResult :=
  .returning
    (fun before _ => before.Valid)
    (fun before _ result after =>
      match result with
      | .ok bytes => ∃ lease, before.account.lease.addShared = some lease ∧
          before.account.data = some bytes ∧ after = before.withLease lease
      | .error .accountBorrowFailed => ¬ canBorrow before.account.lease ∧ after = before)

/-- The byte projection of mutable acquisition, hiding data while exclusive.
Failure preserves the observation. Later guard use belongs to the pool API. -/
def try_borrow_mut_contract : Solanalib.Contracts.Model State Unit BorrowResult :=
  .returning
    (fun before _ => before.Valid)
    (fun before _ result after =>
      match result with
      | .ok bytes => before.account.lease = .free ∧ before.account.data = some bytes ∧
          after = before.withLease .exclusive
      | .error .accountBorrowFailed => ¬ canBorrowMut before.account.lease ∧ after = before)

/-- Six contracts for supplied single-account operations.
Each field states that an operation realizes its public observation contract. -/
structure Spec (operations : Operations) : Prop where
  /-- The supplied update realizes the bounded balance contract. -/
  setLamports : set_lamports_contract.RealizedBy operations.setLamports
  /-- The supplied getter realizes the balance observation contract. -/
  lamports : lamports_contract.RealizedBy operations.lamports
  /-- The supplied getter realizes the logical-length observation contract. -/
  dataLen : data_len_contract.RealizedBy operations.dataLen
  /-- The supplied getter realizes the signer observation contract. -/
  isSigner : is_signer_contract.RealizedBy operations.isSigner
  /-- The supplied shared acquisition realizes its byte projection contract. -/
  tryBorrow : try_borrow_contract.RealizedBy operations.tryBorrow
  /-- The supplied mutable acquisition realizes its byte projection contract. -/
  tryBorrowMut : try_borrow_mut_contract.RealizedBy operations.tryBorrowMut

/-- The reference bundle, interpreted by the shared observation model. -/
def reference : Operations :=
  Solanalib.Specs.Core.AccountViewObservation.reference

/-- The reference satisfies all six public contracts through the shared observation proofs. -/
theorem reference_satisfies : Spec reference where
  setLamports := Solanalib.Specs.Core.AccountViewObservation.set_lamports_reference
  lamports := Solanalib.Specs.Core.AccountViewObservation.lamports_reference
  dataLen := Solanalib.Specs.Core.AccountViewObservation.data_len_reference
  isSigner := Solanalib.Specs.Core.AccountViewObservation.is_signer_reference
  tryBorrow := Solanalib.Specs.Core.AccountViewObservation.try_borrow_reference
  tryBorrowMut := Solanalib.Specs.Core.AccountViewObservation.try_borrow_mut_reference

/-- The setter reference realizes its public observation contract. -/
theorem set_lamports_reference : set_lamports_contract.RealizedBy reference.setLamports :=
  reference_satisfies.setLamports

/-- The balance reference realizes its public observation contract. -/
theorem lamports_reference : lamports_contract.RealizedBy reference.lamports :=
  reference_satisfies.lamports

/-- The length reference realizes its public observation contract. -/
theorem data_len_reference : data_len_contract.RealizedBy reference.dataLen :=
  reference_satisfies.dataLen

/-- The signer reference realizes its public observation contract. -/
theorem is_signer_reference : is_signer_contract.RealizedBy reference.isSigner :=
  reference_satisfies.isSigner

/-- The shared-acquisition reference realizes its byte projection. -/
theorem try_borrow_reference : try_borrow_contract.RealizedBy reference.tryBorrow :=
  reference_satisfies.tryBorrow

/-- The mutable-acquisition reference realizes its byte projection. -/
theorem try_borrow_mut_reference : try_borrow_mut_contract.RealizedBy reference.tryBorrowMut :=
  reference_satisfies.tryBorrowMut

/-- The bounded balance setter retains a closed inhabited precondition. -/
theorem set_lamports_satisfiable : set_lamports_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountViewObservation.set_lamports_satisfiable

/-- The balance getter retains a closed inhabited precondition. -/
theorem lamports_satisfiable : lamports_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountViewObservation.lamports_satisfiable

/-- The length getter retains a closed inhabited precondition. -/
theorem data_len_satisfiable : data_len_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountViewObservation.data_len_satisfiable

/-- The signer getter retains a closed inhabited precondition. -/
theorem is_signer_satisfiable : is_signer_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountViewObservation.is_signer_satisfiable

/-- Shared acquisition retains a closed inhabited precondition. -/
theorem try_borrow_satisfiable : try_borrow_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountViewObservation.try_borrow_satisfiable

/-- Mutable acquisition retains a closed inhabited precondition. -/
theorem try_borrow_mut_satisfiable : try_borrow_mut_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountViewObservation.try_borrow_mut_satisfiable

end Solanalib.Specs.SolanaAccountView.AccountView.Observation
