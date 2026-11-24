/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewFacts

/-!
The six earlier contracts are retained as an explicitly lossy Observation API.
This module relates them to the complete cell/guard model. The acquisition
projection records the bytes at the acquisition instant; only the complete
guard token can be used to justify later dereference, mapping or release.
-/

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- The legacy lease is the exact observation of the identified registry. -/
@[simp] theorem observe_lease (state : State) (handle : Handle) :
    (observe state handle).account.lease = state.lease handle := rfl

/-- Exclusive bytes are hidden from the account-pool observation. -/
@[simp] theorem observe_data (state : State) (handle : Handle) :
    (observe state handle).account.data =
      if state.lease handle = .exclusive then none else some (state.account handle).bytes := rfl

/-- A registry-only transition with no prior exclusive lease agrees with the
legacy lease update, including hiding bytes on exclusive acquisition. -/
theorem observe_lease_change {before after : State} {handle : Handle}
    (cells : after.cells = before.cells) (available : before.lease handle ≠ .exclusive) :
    observe after handle = (observe before handle).withLease (after.lease handle) := by
  have account : after.account handle = before.account handle := by
    simp [State.account, Borrow.State.lookupCell, cells]
  by_cases hidden : after.lease handle = .exclusive
  · simp [observe, AccountViewObservation.State.withLease, hidden, account]
  · simp [observe, AccountViewObservation.State.withLease, hidden, available, account]

/-- A fresh shared guard gives the legacy shared-count update. -/
theorem observe_issue_shared (state : State) (handle : Handle) (view : Slice)
    (free : state.exclusiveCount handle = 0) :
    observe (state.issue handle .shared view).2 handle =
      (observe state handle).withLease (.shared (state.sharedCount handle + 1)) := by
  have available : state.lease handle ≠ .exclusive := by
    simp only [Borrow.State.lease, free, ite_true]
    cases state.sharedCount handle <;> simp
  rw [observe_lease_change (before := state) (after := (state.issue handle .shared view).2)
      (handle := handle) rfl available,
    Borrow.State.issue_shared_lease _ _ _ free]

/-- A fresh exclusive guard gives the legacy hidden-data observation. -/
theorem observe_issue_exclusive (state : State) (handle : Handle) (view : Slice)
    (exclusive : state.exclusiveCount handle = 0) (shared : state.sharedCount handle = 0) :
    observe (state.issue handle .exclusive view).2 handle =
      (observe state handle).withLease .exclusive := by
  have available : state.lease handle ≠ .exclusive := by
    simp [Borrow.State.lease, exclusive, shared]
  rw [observe_lease_change (before := state) (after := (state.issue handle .exclusive view).2)
    (handle := handle) rfl available]
  congr 1
  have old : state.count handle .exclusive = 0 := exclusive
  simp [Borrow.State.lease, Borrow.State.exclusiveCount, Borrow.State.issue_count, old]

/-- Forget an acquisition token while retaining its byte observation at that
instant. This intentionally carries no permission for later lifecycle use. -/
def acquisitionBytes (state : State) (handle : Handle) :
    Except Error Guard → AccountViewObservation.BorrowResult
  | .ok _ => .ok (state.account handle).bytes
  | .error _ => .error .accountBorrowFailed

/-- Successful complete acquisitions justify the byte value forgotten by the
legacy projection through the actual freshly returned guard. -/
theorem acquisitionBytes_current {before after : State} {handle : Handle}
    {mode : Mode} {guard : Guard}
    (step : acquire before handle mode = (.ok guard, after)) :
    guardRead after guard = .ok (before.account handle).bytes ∧
    acquisitionBytes before handle (.ok guard) = .ok (before.account handle).bytes :=
  ⟨acquire_reads step, rfl⟩

/-- Forgetting the shared guard identity recovers the shared-acquisition result and observation of
the six-operation reference, including saturation. -/
theorem shared_acquisition_projection {state : State} {handle : Handle}
    {cell : Borrow.Cell Account} (present : state.lookupCell handle = some cell)
    (policy : cell.policy = Borrow.Policy.accountView) :
    (acquisitionBytes state handle (acquire state handle .shared).1,
      observe (acquire state handle .shared).2 handle) =
    AccountViewObservation.reference.tryBorrow (observe state handle) () := by
  by_cases free : state.exclusiveCount handle = 0
  · cases count : state.sharedCount handle with
    | zero =>
      have lease : state.lease handle = .free := by
        simp [Borrow.State.lease, free, count]
      have step : acquire state handle .shared =
          (.ok ⟨state.slots.length, 0⟩,
            (state.issue handle .shared (state.account handle).whole).2) := by
        simp [acquire, Borrow.acquire, present, policy, free, count, Borrow.Policy.accountView,
          borrowResult, Except.mapError, Borrow.State.issue]
      rw [step]
      change ((.ok (state.account handle).bytes : AccountViewObservation.BorrowResult), _) = _
      rw [observe_issue_shared _ _ _ free]
      simp [AccountViewObservation.reference, lease, Solanalib.Runtime.Lease.addShared, count]
    | succ n =>
      have lease : state.lease handle = .shared (n + 1) := by
        simp [Borrow.State.lease, free, count]
      by_cases room : n + 1 < 254
      · have step : acquire state handle .shared =
            (.ok ⟨state.slots.length, 0⟩,
              (state.issue handle .shared (state.account handle).whole).2) := by
          have limit : ¬254 ≤ n + 1 := by omega
          simp [acquire, Borrow.acquire, present, policy, free, count, Borrow.Policy.accountView,
            limit, borrowResult, Except.mapError, Borrow.State.issue]
        rw [step]
        change ((.ok (state.account handle).bytes : AccountViewObservation.BorrowResult), _) = _
        rw [observe_issue_shared _ _ _ free]
        simp [AccountViewObservation.reference, lease, Solanalib.Runtime.Lease.addShared, room,
          count]
      · have limit : 254 ≤ n + 1 := by omega
        have step : acquire state handle .shared = (.error .accountBorrowFailed, state) := by
          simp [acquire, Borrow.acquire, present, policy, free, count, Borrow.Policy.accountView,
            limit, borrowResult, Except.mapError]
        rw [step]
        simp [acquisitionBytes, AccountViewObservation.reference, lease,
          Solanalib.Runtime.Lease.addShared, room]
  · have lease : state.lease handle = .exclusive := by simp [Borrow.State.lease, free]
    have step : acquire state handle .shared = (.error .accountBorrowFailed, state) := by
      simp [acquire, Borrow.acquire, present, free, borrowResult, Except.mapError]
    rw [step]
    simp [acquisitionBytes, AccountViewObservation.reference, lease,
      Solanalib.Runtime.Lease.addShared]

/-- Forgetting an exclusive guard gives exactly the old mutable-acquisition
result and its hidden pool bytes. The complete cell still contains those bytes. -/
theorem mutable_acquisition_projection {state : State} {handle : Handle}
    (account : state.HasAccount handle) :
    (acquisitionBytes state handle (acquire state handle .exclusive).1,
      observe (acquire state handle .exclusive).2 handle) =
    AccountViewObservation.reference.tryBorrowMut (observe state handle) () := by
  obtain ⟨cell, present⟩ := account
  by_cases free : state.exclusiveCount handle = 0 ∧ state.sharedCount handle = 0
  · have lease : state.lease handle = .free := by simp [Borrow.State.lease, free.1, free.2]
    have step : acquire state handle .exclusive =
        (.ok ⟨state.slots.length, 0⟩,
          (state.issue handle .exclusive (state.account handle).whole).2) := by
      simp [acquire, Borrow.acquire, present, free.1, free.2,
        borrowResult, Except.mapError, Borrow.State.issue]
    rw [step]
    change ((.ok (state.account handle).bytes : AccountViewObservation.BorrowResult), _) = _
    rw [observe_issue_exclusive _ _ _ free.1 free.2]
    simp [AccountViewObservation.reference, lease]
  · have busy : state.exclusiveCount handle ≠ 0 ∨ state.sharedCount handle ≠ 0 := by omega
    have lease : state.lease handle ≠ .free := by
      by_cases exclusive : state.exclusiveCount handle = 0
      · cases count : state.sharedCount handle <;> simp_all [Borrow.State.lease]
      · simp [Borrow.State.lease, exclusive]
    have step : acquire state handle .exclusive = (.error .accountBorrowFailed, state) := by
      simp [acquire, Borrow.acquire, present, busy, borrowResult, Except.mapError]
    rw [step]
    simp [acquisitionBytes, AccountViewObservation.reference, lease]

/-- The shared-byte postcondition follows from the complete pool projection.
This does not establish the separate validity precondition of the legacy contract. -/
theorem shared_observation_contract {state : State} {handle : Handle}
    {cell : Borrow.Cell Account} (present : state.lookupCell handle = some cell)
    (policy : cell.policy = Borrow.Policy.accountView) :
    AccountViewObservation.try_borrow_contract.ensures (observe state handle) ()
      (acquisitionBytes state handle (acquire state handle .shared).1)
      (observe (acquire state handle .shared).2 handle) := by
  have reference : AccountViewObservation.try_borrow_contract.ensures
      (observe state handle) ()
      (AccountViewObservation.reference.tryBorrow (observe state handle) ()).1
      (AccountViewObservation.reference.tryBorrow (observe state handle) ()).2 := by
    cases lease : state.lease handle with
    | free =>
      simp [AccountViewObservation.reference, AccountViewObservation.try_borrow_contract,
        lease, Solanalib.Runtime.Lease.addShared]
    | shared count =>
      by_cases room : count < 254 <;>
        simp [AccountViewObservation.reference, AccountViewObservation.try_borrow_contract,
          lease, Solanalib.Runtime.Lease.addShared, room, AccountViewObservation.canBorrow]
    | exclusive =>
      simp [AccountViewObservation.reference, AccountViewObservation.try_borrow_contract,
        lease, Solanalib.Runtime.Lease.addShared, AccountViewObservation.canBorrow]
  have same := shared_acquisition_projection present policy
  rw [← same] at reference
  exact reference

/-- The previous mutable-byte contract is also a projection, not an alternative
source model with a disconnected lease lifecycle. -/
theorem mutable_observation_contract {state : State} {handle : Handle}
    (account : state.HasAccount handle) :
    AccountViewObservation.try_borrow_mut_contract.ensures (observe state handle) ()
      (acquisitionBytes state handle (acquire state handle .exclusive).1)
      (observe (acquire state handle .exclusive).2 handle) := by
  have reference : AccountViewObservation.try_borrow_mut_contract.ensures
      (observe state handle) ()
      (AccountViewObservation.reference.tryBorrowMut (observe state handle) ()).1
      (AccountViewObservation.reference.tryBorrowMut (observe state handle) ()).2 := by
    by_cases free : state.lease handle = .free <;>
      simp [AccountViewObservation.reference, AccountViewObservation.try_borrow_mut_contract,
        free, AccountViewObservation.canBorrowMut]
  have same := mutable_acquisition_projection account
  rw [← same] at reference
  exact reference

end Solanalib.Specs.Core.AccountView
