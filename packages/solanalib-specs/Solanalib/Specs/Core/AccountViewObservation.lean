/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Runtime.View
public import Solanalib.Runtime.StoreOps

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountViewObservation

/-- The observations of one AccountView. Metadata and mutable account fields
refer to the same account; hidden data remain owned by an exclusive borrower.
Pointer representation and permissions belong to the source binding. -/
structure State where
  /-- The address and access metadata in this single-account projection. -/
  metadata : _root_.Solanalib.Runtime.AccountMeta
  /-- The canonical partial account observation, including the current lease. -/
  account : _root_.Solanalib.Runtime.PartialCell
  deriving DecidableEq, Repr

/-- States represented by the AccountView API. The current bytes are observable
exactly when no exclusive data guard owns them. -/
def State.Valid (state : State) : Prop :=
  state.account.lamports < _root_.Solanalib.Runtime.U64_LIMIT ∧
  state.account.dataLen < _root_.Solanalib.Runtime.U64_LIMIT ∧
  match state.account.lease with
  | .free => ∃ bytes, state.account.data = some bytes ∧ bytes.length = state.account.dataLen
  | .shared count => 0 < count ∧ count ≤ 254 ∧
      ∃ bytes, state.account.data = some bytes ∧ bytes.length = state.account.dataLen
  | .exclusive => state.account.data = none

/-- A working-balance update. Authorization and conservation are runtime checks
at synchronization, not preconditions of AccountView::set_lamports. -/
def State.setLamports (state : State) (value : Nat) : State :=
  { state with account := { state.account with lamports := value } }

/-- A data-lease update changes only the lease and the availability of the
account-pool observation. -/
def State.withLease (state : State) (lease : _root_.Solanalib.Runtime.Lease) : State :=
  { state with
    account := { state.account with
      lease := lease
      data := if lease = .exclusive then none else state.account.data } }

/-- A bounded balance replacement in the compatibility observation. -/
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

/-- At most 254 shared guards can exist for an AccountView. -/
def canBorrow (lease : _root_.Solanalib.Runtime.Lease) : Prop :=
  match lease with
  | .free => True
  | .shared count => 0 < count ∧ count < 254
  | .exclusive => False

/-- Mutable acquisition is permitted exactly when the lease is free. -/
def canBorrowMut (lease : _root_.Solanalib.Runtime.Lease) : Prop := lease = .free

/-- The documented failure of a checked data borrow. -/
inductive BorrowError where
  /-- The projected acquisition was rejected by the borrow check. -/
  | accountBorrowFailed
  deriving DecidableEq, Repr

/-- The byte observation of the acquisition or documented borrow failure. -/
abbrev BorrowResult := Except BorrowError _root_.Solanalib.Runtime.Bytes

/-- A shared data acquisition includes both success and AccountBorrowFailed.
Success returns the current bytes and increments the canonical lease; failure
preserves the complete observation. -/
def try_borrow_contract : Solanalib.Contracts.Model State Unit BorrowResult :=
  .returning
    (fun before _ => before.Valid)
    (fun before _ result after =>
      match result with
      | .ok bytes => ∃ lease, before.account.lease.addShared = some lease ∧
          before.account.data = some bytes ∧ after = before.withLease lease
      | .error .accountBorrowFailed => ¬ canBorrow before.account.lease ∧ after = before)

/-- A mutable acquisition succeeds exactly with no outstanding guard. Its
returned bytes leave the account-pool observation while the guard is live.
Failure preserves the account and metadata. -/
def try_borrow_mut_contract : Solanalib.Contracts.Model State Unit BorrowResult :=
  .returning
    (fun before _ => before.Valid)
    (fun before _ result after =>
      match result with
      | .ok bytes => before.account.lease = .free ∧ before.account.data = some bytes ∧
          after = before.withLease .exclusive
      | .error .accountBorrowFailed => ¬ canBorrowMut before.account.lease ∧ after = before)

/-- The operations used by clients of the portable specification. -/
structure Operations where
  /-- The supplied mathematical balance update. -/
  setLamports : State → Nat → Unit × State
  /-- The supplied mathematical balance observation. -/
  lamports : State → Unit → Nat × State
  /-- The supplied mathematical logical-length observation. -/
  dataLen : State → Unit → Nat × State
  /-- The supplied mathematical signer observation. -/
  isSigner : State → Unit → Bool × State
  /-- The supplied shared-acquisition byte projection. -/
  tryBorrow : State → Unit → BorrowResult × State
  /-- The supplied mutable-acquisition byte projection. -/
  tryBorrowMut : State → Unit → BorrowResult × State

/-- One specification structure for the six selected AccountView observations.
Each field is a documented contract, not an implementation or source-table fact. -/
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

/-- A reference interpretation witnesses consistency of the portable contracts.
It uses the canonical lease transition; it is not a proof about a Rust body. -/
def reference : Operations where
  setLamports := fun before value => ((), before.setLamports value)
  lamports := fun before _ => (before.account.lamports, before)
  dataLen := fun before _ => (before.account.dataLen, before)
  isSigner := fun before _ => (before.metadata.signer, before)
  tryBorrow := fun before _ =>
    match before.account.lease.addShared, before.account.data with
    | some lease, some bytes => (.ok bytes, before.withLease lease)
    | _, _ => (.error .accountBorrowFailed, before)
  tryBorrowMut := fun before _ =>
    if before.account.lease = .free then
      match before.account.data with
      | some bytes => (.ok bytes, before.withLease .exclusive)
      | none => (.error .accountBorrowFailed, before)
    else (.error .accountBorrowFailed, before)

theorem reference_satisfies : Spec reference := by
  constructor
  · intro before value valid
    rfl
  · intro before args valid
    exact ⟨rfl, rfl⟩
  · intro before args valid
    exact ⟨rfl, rfl⟩
  · intro before args valid
    exact ⟨rfl, rfl⟩
  · intro before args valid
    change before.Valid at valid
    have data := valid.2.2
    cases lease : before.account.lease with
    | free =>
      simp only [lease] at data
      obtain ⟨bytes, present, length⟩ := data
      simp [reference, try_borrow_contract, _root_.Solanalib.Runtime.Lease.addShared, lease,
        present]
    | shared count =>
      simp only [lease] at data
      obtain ⟨positive, limit, bytes, present, length⟩ := data
      by_cases room : count < 254
      · simp [reference, try_borrow_contract, _root_.Solanalib.Runtime.Lease.addShared, lease,
        present, room]
      · simp [reference, try_borrow_contract, _root_.Solanalib.Runtime.Lease.addShared, lease,
        present, room,
          canBorrow]
    | exclusive =>
      simp [reference, try_borrow_contract, _root_.Solanalib.Runtime.Lease.addShared, lease,
        canBorrow]
  · intro before args valid
    change before.Valid at valid
    by_cases free : before.account.lease = .free
    · have data := valid.2.2
      simp only [free] at data
      obtain ⟨bytes, present, length⟩ := data
      simp [reference, try_borrow_mut_contract, free, present]
    · simp [reference, try_borrow_mut_contract, free, canBorrowMut]

theorem set_lamports_reference : set_lamports_contract.RealizedBy reference.setLamports :=
  reference_satisfies.setLamports

theorem lamports_reference : lamports_contract.RealizedBy reference.lamports :=
  reference_satisfies.lamports

theorem data_len_reference : data_len_contract.RealizedBy reference.dataLen :=
  reference_satisfies.dataLen

theorem is_signer_reference : is_signer_contract.RealizedBy reference.isSigner :=
  reference_satisfies.isSigner

theorem try_borrow_reference : try_borrow_contract.RealizedBy reference.tryBorrow :=
  reference_satisfies.tryBorrow

theorem try_borrow_mut_reference : try_borrow_mut_contract.RealizedBy reference.tryBorrowMut :=
  reference_satisfies.tryBorrowMut

/-- A concrete account observation used to witness the six preconditions. -/
private def witnessState : State where
  metadata := ⟨.zero, false, false, false⟩
  account := ⟨.zero, 0, 0, 0, .free, some []⟩

private theorem witnessState_valid : witnessState.Valid :=
  ⟨by decide, by decide, [], rfl, rfl⟩

/-- The bounded balance setter has an admissible input. -/
theorem set_lamports_satisfiable : set_lamports_contract.Satisfiable :=
  ⟨witnessState, 0, by change 0 < _root_.Solanalib.Runtime.U64_LIMIT; decide⟩

/-- The balance getter has an admissible input. -/
theorem lamports_satisfiable : lamports_contract.Satisfiable :=
  ⟨witnessState, (), trivial⟩

/-- The length getter has an admissible input. -/
theorem data_len_satisfiable : data_len_contract.Satisfiable :=
  ⟨witnessState, (), trivial⟩

/-- The signer getter has an admissible input. -/
theorem is_signer_satisfiable : is_signer_contract.Satisfiable :=
  ⟨witnessState, (), trivial⟩

/-- Shared acquisition has an admissible account observation. -/
theorem try_borrow_satisfiable : try_borrow_contract.Satisfiable :=
  ⟨witnessState, (), witnessState_valid⟩

/-- Mutable acquisition has an admissible account observation. -/
theorem try_borrow_mut_satisfiable : try_borrow_mut_contract.Satisfiable :=
  ⟨witnessState, (), witnessState_valid⟩

/-- Bounded balance replacement preserves the observations required by later
account operations, including their byte-length and lease invariants. -/
theorem State.setLamports_valid {before : State} {value : Nat}
    (valid : before.Valid) (bounded : value < _root_.Solanalib.Runtime.U64_LIMIT) :
    (before.setLamports value).Valid :=
  ⟨bounded, valid.2.1, valid.2.2⟩

/-- A successful canonical shared acquisition preserves the complete account
observation invariant, including the bounded positive shared count. -/
theorem State.withShared_valid {before : State} {next : _root_.Solanalib.Runtime.Lease}
    (valid : before.Valid) (acquired : before.account.lease.addShared = some next) :
    (before.withLease next).Valid := by
  cases lease : before.account.lease with
  | free =>
    have next_eq : next = .shared 1 := by
      simpa [_root_.Solanalib.Runtime.Lease.addShared, lease] using acquired.symm
    subst next
    have data : ∃ bytes, before.account.data = some bytes ∧
        bytes.length = before.account.dataLen := by
      simpa only [lease] using valid.2.2
    exact ⟨valid.1, valid.2.1, by decide, by decide, data⟩
  | shared count =>
    by_cases room : count < 254
    · have next_eq : next = .shared (count + 1) := by
        simpa [_root_.Solanalib.Runtime.Lease.addShared, lease, room] using acquired.symm
      subst next
      have data : 0 < count ∧ count ≤ 254 ∧
          ∃ bytes, before.account.data = some bytes ∧
            bytes.length = before.account.dataLen := by
        simpa only [lease] using valid.2.2
      exact ⟨valid.1, valid.2.1, by omega, by omega, data.2.2⟩
    · simp [_root_.Solanalib.Runtime.Lease.addShared, lease, room] at acquired
  | exclusive => simp [_root_.Solanalib.Runtime.Lease.addShared, lease] at acquired

/-- Transferring the bytes into an exclusive guard preserves the invariant:
the pool no longer exposes them while the guard is live. -/
theorem State.withExclusive_valid {before : State} (valid : before.Valid) :
    (before.withLease .exclusive).Valid :=
  ⟨valid.1, valid.2.1, rfl⟩

/-- Every implementation satisfying the bounded setter contract preserves
valid observations for subsequent calls. -/
theorem Spec.setLamports_valid {operations : Operations} (spec : Spec operations)
    {before : State} {value : Nat} (valid : before.Valid)
    (bounded : value < _root_.Solanalib.Runtime.U64_LIMIT) :
    (operations.setLamports before value).2.Valid := by
  have changed := spec.setLamports before value bounded
  change (operations.setLamports before value).2 = before.setLamports value at changed
  rw [changed]
  exact State.setLamports_valid valid bounded

/-- Both the success and failure branches of a conforming shared acquisition
preserve the domain required by subsequent AccountView calls. -/
theorem Spec.tryBorrow_valid {operations : Operations} (spec : Spec operations)
    {before : State} (valid : before.Valid) :
    (operations.tryBorrow before ()).2.Valid := by
  have contract := spec.tryBorrow before () valid
  cases executed : operations.tryBorrow before () with
  | mk outcome after =>
    rw [executed] at contract
    cases outcome with
    | ok bytes =>
      obtain ⟨next, acquired, _, same⟩ := contract
      change after.Valid
      change after = before.withLease next at same
      rw [same]
      exact State.withShared_valid valid acquired
    | error error =>
      cases error
      obtain ⟨_, same⟩ := contract
      change after.Valid
      change after = before at same
      simpa only [same] using valid

/-- Both the success and failure branches of a conforming mutable acquisition
preserve the domain required by subsequent AccountView calls. -/
theorem Spec.tryBorrowMut_valid {operations : Operations} (spec : Spec operations)
    {before : State} (valid : before.Valid) :
    (operations.tryBorrowMut before ()).2.Valid := by
  have contract := spec.tryBorrowMut before () valid
  cases executed : operations.tryBorrowMut before () with
  | mk outcome after =>
    rw [executed] at contract
    cases outcome with
    | ok bytes =>
      obtain ⟨_, _, same⟩ := contract
      change after.Valid
      change after = before.withLease .exclusive at same
      rw [same]
      exact State.withExclusive_valid valid
    | error error =>
      cases error
      obtain ⟨_, same⟩ := contract
      change after.Valid
      change after = before at same
      simpa only [same] using valid

end Solanalib.Specs.Core.AccountViewObservation
