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

namespace SolanalibTest.Specs.SolanaAccountView.SingleAccount

open Solanalib.Specs.SolanaAccountView.AccountView.Observation

/-! These compile checks exercise the single-account API, including
its fully qualified constructors and fields. The lifecycle tests separately
exercise AccountView.Pool and the identified guard families. -/

example : Solanalib.Contracts.Model State Nat Unit := set_lamports_contract
example : Solanalib.Contracts.Model State Unit Nat := lamports_contract
example : Solanalib.Contracts.Model State Unit Nat := data_len_contract
example : Solanalib.Contracts.Model State Unit Bool := is_signer_contract
example : Solanalib.Contracts.Model State Unit BorrowResult := try_borrow_contract
example : Solanalib.Contracts.Model State Unit BorrowResult := try_borrow_mut_contract

example (state : State) : Solanalib.Runtime.AccountMeta := state.metadata
example (state : State) : Solanalib.Runtime.PartialCell := state.account
example : Spec reference := reference_satisfies
example : set_lamports_contract.RealizedBy reference.setLamports := set_lamports_reference
example : lamports_contract.RealizedBy reference.lamports := lamports_reference
example : data_len_contract.RealizedBy reference.dataLen := data_len_reference
example : is_signer_contract.RealizedBy reference.isSigner := is_signer_reference
example : try_borrow_contract.RealizedBy reference.tryBorrow := try_borrow_reference
example : try_borrow_mut_contract.RealizedBy reference.tryBorrowMut := try_borrow_mut_reference

example : State → Prop := Solanalib.Specs.SolanaAccountView.AccountView.Observation.State.Valid
example : State → Nat → State :=
  Solanalib.Specs.SolanaAccountView.AccountView.Observation.State.setLamports
example : State → Solanalib.Runtime.Lease → State :=
  Solanalib.Specs.SolanaAccountView.AccountView.Observation.State.withLease
example : Solanalib.Runtime.AccountMeta → Solanalib.Runtime.PartialCell → State :=
  Solanalib.Specs.SolanaAccountView.AccountView.Observation.State.mk
example : BorrowError :=
  Solanalib.Specs.SolanaAccountView.AccountView.Observation.BorrowError.accountBorrowFailed
example (operations : Operations) : State → Nat → Unit × State :=
  Solanalib.Specs.SolanaAccountView.AccountView.Observation.Operations.setLamports operations
example (operations : Operations) (spec : Spec operations) :
    set_lamports_contract.RealizedBy operations.setLamports :=
  Solanalib.Specs.SolanaAccountView.AccountView.Observation.Spec.setLamports spec

/-- Every single-account contract has exactly the shared observation semantics. -/
theorem contracts_equal_shared :
    set_lamports_contract = Solanalib.Specs.Core.AccountViewObservation.set_lamports_contract ∧
    lamports_contract = Solanalib.Specs.Core.AccountViewObservation.lamports_contract ∧
    data_len_contract = Solanalib.Specs.Core.AccountViewObservation.data_len_contract ∧
    is_signer_contract = Solanalib.Specs.Core.AccountViewObservation.is_signer_contract ∧
    try_borrow_contract = Solanalib.Specs.Core.AccountViewObservation.try_borrow_contract ∧
    try_borrow_mut_contract = Solanalib.Specs.Core.AccountViewObservation.try_borrow_mut_contract :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The single-account operation bundle and the shared observation bundle coincide. -/
theorem reference_equal_shared :
    reference = Solanalib.Specs.Core.AccountViewObservation.reference := rfl

/-- The single-account and shared specifications are equivalent for every supplied bundle. -/
theorem spec_iff_shared (operations : Operations) :
    Spec operations ↔ Solanalib.Specs.Core.AccountViewObservation.Spec operations := by
  constructor <;> intro spec
  · exact ⟨spec.setLamports, spec.lamports, spec.dataLen, spec.isSigner,
      spec.tryBorrow, spec.tryBorrowMut⟩
  · exact ⟨spec.setLamports, spec.lamports, spec.dataLen, spec.isSigner,
      spec.tryBorrow, spec.tryBorrowMut⟩

/-- An implementation may leave out-of-range mathematical inputs unchanged:
the setter contract only constrains values representable by `u64`. -/
def boundedSetter (before : State) (value : Nat) : Unit × State :=
  if value < Solanalib.Runtime.U64_LIMIT then ((), before.setLamports value) else ((), before)

/-- This alternate implementation detects an accidental strengthening of the
published setter contract to all natural numbers. -/
theorem boundedSetter_realizes : set_lamports_contract.RealizedBy boundedSetter := by
  intro before value bounded
  change value < Solanalib.Runtime.U64_LIMIT at bounded
  simp [boundedSetter, bounded, set_lamports_contract]

/-- A bounded write followed by a shared acquisition remains in the domain of
the next AccountView call, for every implementation satisfying the contracts. -/
theorem write_then_shared_valid {operations : Operations} (spec : Spec operations)
    {before : State} {value : Nat} (valid : before.Valid)
    (bounded : value < Solanalib.Runtime.U64_LIMIT) :
    (operations.tryBorrow (operations.setLamports before value).2 ()).2.Valid := by
  have shared := (spec_iff_shared operations).mp spec
  exact shared.tryBorrow_valid (shared.setLamports_valid valid bounded)

end SolanalibTest.Specs.SolanaAccountView.SingleAccount
