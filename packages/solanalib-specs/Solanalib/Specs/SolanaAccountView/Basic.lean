/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewRevisionWitness
public import Solanalib.Specs.Core.AccountViewWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaAccountView

open Solanalib.Specs.Core.AccountView

/-! Mathematical models for AccountView 1.0.0. The mutating Rust receiver is
shared (&self); that source distinction does not imply global uniqueness of the
pointed-to account. Handles and guards retain their common pool identities. -/

namespace AccountView.Pool

export Solanalib.Specs.Core.AccountView
  (Account State Handle Guard Mode Error Slice AddressRef OwnerRef DataRef Ready GuardReady)

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def lamports_contract : Solanalib.Contracts.Model State Handle Nat :=
  Solanalib.Specs.Core.AccountView.lamports_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def lamports_model : State → Handle → Nat × State :=
  Solanalib.Specs.Core.AccountView.observation Account.lamports

/-- The complete reference realizes the declared model contract of this version. -/
theorem lamports_reference : lamports_contract.RealizedBy lamports_model :=
  Solanalib.Specs.Core.AccountView.observation_reference Account.lamports

/-- The model precondition has a closed inhabited witness. -/
theorem lamports_satisfiable : lamports_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.observation_satisfiable Account.lamports

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def data_len_contract : Solanalib.Contracts.Model State Handle Nat :=
  Solanalib.Specs.Core.AccountView.data_len_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def data_len_model : State → Handle → Nat × State :=
  Solanalib.Specs.Core.AccountView.observation Account.dataLen

/-- The complete reference realizes the declared model contract of this version. -/
theorem data_len_reference : data_len_contract.RealizedBy data_len_model :=
  Solanalib.Specs.Core.AccountView.observation_reference Account.dataLen

/-- The model precondition has a closed inhabited witness. -/
theorem data_len_satisfiable : data_len_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.observation_satisfiable Account.dataLen

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def is_data_empty_contract : Solanalib.Contracts.Model State Handle Bool :=
  Solanalib.Specs.Core.AccountView.is_data_empty_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def is_data_empty_model : State → Handle → Bool × State :=
  Solanalib.Specs.Core.AccountView.observation (fun account => account.dataLen == 0)

/-- The complete reference realizes the declared model contract of this version. -/
theorem is_data_empty_reference : is_data_empty_contract.RealizedBy is_data_empty_model :=
  Solanalib.Specs.Core.AccountView.observation_reference (fun account => account.dataLen == 0)

/-- The model precondition has a closed inhabited witness. -/
theorem is_data_empty_satisfiable : is_data_empty_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.observation_satisfiable (fun account => account.dataLen == 0)

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def is_signer_contract : Solanalib.Contracts.Model State Handle Bool :=
  Solanalib.Specs.Core.AccountView.is_signer_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def is_signer_model : State → Handle → Bool × State :=
  Solanalib.Specs.Core.AccountView.observation (fun account => account.metadata.signer)

/-- The complete reference realizes the declared model contract of this version. -/
theorem is_signer_reference : is_signer_contract.RealizedBy is_signer_model :=
  Solanalib.Specs.Core.AccountView.observation_reference (fun account => account.metadata.signer)

/-- The model precondition has a closed inhabited witness. -/
theorem is_signer_satisfiable : is_signer_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.observation_satisfiable (fun account => account.metadata.signer)

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def is_writable_contract : Solanalib.Contracts.Model State Handle Bool :=
  Solanalib.Specs.Core.AccountView.is_writable_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def is_writable_model : State → Handle → Bool × State :=
  Solanalib.Specs.Core.AccountView.observation (fun account => account.metadata.writable)

/-- The complete reference realizes the declared model contract of this version. -/
theorem is_writable_reference : is_writable_contract.RealizedBy is_writable_model :=
  Solanalib.Specs.Core.AccountView.observation_reference (fun account => account.metadata.writable)

/-- The model precondition has a closed inhabited witness. -/
theorem is_writable_satisfiable : is_writable_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.observation_satisfiable (fun account =>
    account.metadata.writable)

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def clone_contract : Solanalib.Contracts.Model State Handle Handle :=
  Solanalib.Specs.Core.AccountView.clone_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def clone_model : State → Handle → Handle × State :=
  fun before handle => (handle, before)

/-- The complete reference realizes the declared model contract of this version. -/
theorem clone_reference : clone_contract.RealizedBy clone_model :=
  Solanalib.Specs.Core.AccountView.clone_reference

/-- The model precondition has a closed inhabited witness. -/
theorem clone_satisfiable : clone_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.clone_satisfiable

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def address_contract : Solanalib.Contracts.Model State Handle AddressRef :=
  Solanalib.Specs.Core.AccountView.address_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def address_model : State → Handle → AddressRef × State :=
  fun before handle => (⟨handle⟩, before)

/-- The complete reference realizes the declared model contract of this version. -/
theorem address_reference : address_contract.RealizedBy address_model :=
  Solanalib.Specs.Core.AccountView.address_reference

/-- The model precondition has a closed inhabited witness. -/
theorem address_satisfiable : address_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.address_satisfiable

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def owner_contract : Solanalib.Contracts.Model State Handle OwnerRef :=
  Solanalib.Specs.Core.AccountView.owner_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def owner_model : State → Handle → OwnerRef × State :=
  fun before handle => (⟨handle, (before.account handle).ownerEpoch⟩, before)

/-- The complete reference realizes the declared model contract of this version. -/
theorem owner_reference : owner_contract.RealizedBy owner_model :=
  Solanalib.Specs.Core.AccountView.owner_reference

/-- The model precondition has a closed inhabited witness. -/
theorem owner_satisfiable : owner_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.owner_satisfiable

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def owned_by_contract : Solanalib.Contracts.Model State (Handle × Solanalib.Runtime.Pubkey) Bool :=
  Solanalib.Specs.Core.AccountView.owned_by_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def owned_by_model : State → (Handle × Solanalib.Runtime.Pubkey) → Bool × State :=
  fun before args => (decide ((before.account args.1).owner = args.2), before)

/-- The complete reference realizes the declared model contract of this version. -/
theorem owned_by_reference : owned_by_contract.RealizedBy owned_by_model :=
  Solanalib.Specs.Core.AccountView.owned_by_reference

/-- The model precondition has a closed inhabited witness. -/
theorem owned_by_satisfiable : owned_by_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.owned_by_satisfiable

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def set_lamports_contract : Solanalib.Contracts.Model State (Handle × Nat) Unit :=
  Solanalib.Specs.Core.AccountView.set_lamports_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def set_lamports_model : State → (Handle × Nat) → Unit × State :=
  Solanalib.Specs.Core.AccountView.setLamports

/-- The complete reference realizes the declared model contract of this version. -/
theorem set_lamports_reference : set_lamports_contract.RealizedBy set_lamports_model :=
  Solanalib.Specs.Core.AccountView.set_lamports_reference

/-- The model precondition has a closed inhabited witness. -/
theorem set_lamports_satisfiable : set_lamports_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.set_lamports_satisfiable

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def try_borrow_contract : Solanalib.Contracts.Model State Handle (Except Error Guard) :=
  Solanalib.Specs.Core.AccountView.try_borrow_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def try_borrow_model : State → Handle → (Except Error Guard) × State :=
  fun before handle => Solanalib.Specs.Core.AccountView.acquire before handle .shared

/-- The complete reference realizes the declared model contract of this version. -/
theorem try_borrow_reference : try_borrow_contract.RealizedBy try_borrow_model :=
  Solanalib.Specs.Core.AccountView.borrow_reference .shared

/-- The model precondition has a closed inhabited witness. -/
theorem try_borrow_satisfiable : try_borrow_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.borrow_satisfiable .shared

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def try_borrow_mut_contract : Solanalib.Contracts.Model State Handle (Except Error Guard) :=
  Solanalib.Specs.Core.AccountView.try_borrow_mut_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def try_borrow_mut_model : State → Handle → (Except Error Guard) × State :=
  fun before handle => Solanalib.Specs.Core.AccountView.acquire before handle .exclusive

/-- The complete reference realizes the declared model contract of this version. -/
theorem try_borrow_mut_reference : try_borrow_mut_contract.RealizedBy try_borrow_mut_model :=
  Solanalib.Specs.Core.AccountView.borrow_reference .exclusive

/-- The model precondition has a closed inhabited witness. -/
theorem try_borrow_mut_satisfiable : try_borrow_mut_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.borrow_satisfiable .exclusive

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def resize_contract : Solanalib.Contracts.Model State (Handle × Nat) (Except Error Unit) :=
  Solanalib.Specs.Core.AccountView.resize_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def resize_model : State → (Handle × Nat) → (Except Error Unit) × State :=
  Solanalib.Specs.Core.AccountView.resize

/-- The complete reference realizes the declared model contract of this version. -/
theorem resize_reference : resize_contract.RealizedBy resize_model :=
  Solanalib.Specs.Core.AccountView.resize_reference

/-- The model precondition has a closed inhabited witness. -/
theorem resize_satisfiable : resize_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.resize_satisfiable

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def close_with_resize_delta_contract : Solanalib.Contracts.Model State Handle (Except Error Unit) :=
  Solanalib.Specs.Core.AccountView.close_contract .v1

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def close_with_resize_delta_model : State → Handle → (Except Error Unit) × State :=
  Solanalib.Specs.Core.AccountView.close .v1

/-- The complete reference realizes the declared model contract of this version. -/
theorem close_with_resize_delta_reference : close_with_resize_delta_contract.RealizedBy
  close_with_resize_delta_model :=
  Solanalib.Specs.Core.AccountView.close_reference .v1

/-- The model precondition has a closed inhabited witness. -/
theorem close_with_resize_delta_satisfiable : close_with_resize_delta_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.close_satisfiable .v1

end AccountView.Pool

end Solanalib.Specs.SolanaAccountView

namespace Solanalib.Specs.SolanaAccountView

open Solanalib.Specs.Core.AccountView

/-! Complete pool models for AccountView 2.0.0. The mutating Rust receiver is
mutable (&mut self); that source distinction does not imply global uniqueness of the
pointed-to account. Handles and guards retain their common pool identities.
`AccountView.Observation` provides the single-account API. -/

namespace AccountView.Pool

export Solanalib.Specs.Core.AccountView
  (Account State Handle Guard Mode Error Slice AddressRef OwnerRef DataRef Ready GuardReady)

/-- The scalar reference has a finite execution at an existing account cell. -/
theorem lamports_hasExecution :
    lamports_contract.HasExecution (Solanalib.Contracts.Model.returnsOf lamports_model) :=
  (Solanalib.Contracts.Model.hasExecution_returnsOf_iff_satisfiable _ _).2 lamports_satisfiable

/-- The scalar reference has a finite execution at an existing account cell. -/
theorem data_len_hasExecution :
    data_len_contract.HasExecution (Solanalib.Contracts.Model.returnsOf data_len_model) :=
  (Solanalib.Contracts.Model.hasExecution_returnsOf_iff_satisfiable _ _).2 data_len_satisfiable

/-- The scalar reference has a finite execution at an existing account cell. -/
theorem is_signer_hasExecution :
    is_signer_contract.HasExecution (Solanalib.Contracts.Model.returnsOf is_signer_model) :=
  (Solanalib.Contracts.Model.hasExecution_returnsOf_iff_satisfiable _ _).2 is_signer_satisfiable

/-- The owner comparison has a finite execution at an existing account cell. -/
theorem owned_by_hasExecution :
    owned_by_contract.HasExecution (Solanalib.Contracts.Model.returnsOf owned_by_model) :=
  (Solanalib.Contracts.Model.hasExecution_returnsOf_iff_satisfiable _ _).2 owned_by_satisfiable

/-- The versioned mathematical contract; its account and guard semantics are shared. -/
def close_header_contract : Solanalib.Contracts.Model State Handle (Except Error Unit) :=
  Solanalib.Specs.Core.AccountView.closeHeader_contract

/-- A total mathematical reference interpretation, not a Rust implementation. -/
def close_header_model : State → Handle → (Except Error Unit) × State :=
  Solanalib.Specs.Core.AccountView.closeHeader

/-- The complete reference realizes the declared model contract of this version. -/
theorem close_header_reference : close_header_contract.RealizedBy close_header_model :=
  Solanalib.Specs.Core.AccountView.closeHeader_reference

/-- The model precondition has a closed inhabited witness. -/
theorem close_header_satisfiable : close_header_contract.Satisfiable :=
  Solanalib.Specs.Core.AccountView.closeHeader_satisfiable

end AccountView.Pool

end Solanalib.Specs.SolanaAccountView
