/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorrowMapLaws

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borrow

universe u v

variable {Content : Type u} {View : Type v}

/-- Policy-parametric shared acquisition on the canonical lease vocabulary. -/
def Policy.addShared (policy : Policy) : Solanalib.Runtime.Lease → Option Solanalib.Runtime.Lease
  | .free => if 0 < policy.sharedLimit then some (.shared 1) else none
  | .shared count => if count < policy.sharedLimit then some (.shared (count + 1)) else none
  | .exclusive => none

/-- At the AccountView bound this is exactly the existing canonical transition. -/
theorem accountView_addShared (lease : Solanalib.Runtime.Lease) :
    Policy.accountView.addShared lease = lease.addShared := by
  cases lease <;> rfl

/-- Issuing a shared slot changes the canonical observation by exactly one lease. -/
theorem State.issue_shared_lease (state : State Content View) (handle : Handle) (view : View)
    (free : state.exclusiveCount handle = 0) :
    (state.issue handle .shared view).2.lease handle = .shared (state.sharedCount handle + 1) := by
  have noExclusive : state.count handle .exclusive = 0 := free
  simp [State.lease, State.exclusiveCount, State.sharedCount, State.issue_count, noExclusive]

/-- Forgetting only the fresh guard id yields precisely policy-parametric lease
acquisition. Errors and saturation agree, including a policy with no shared room. -/
theorem acquire_shared_observation {state : State Content View} {handle : Handle}
    {cell : Cell Content} (present : state.lookupCell handle = some cell) (view : View) :
    ((acquire state handle .shared view).1.toOption).map
        (fun _ => (acquire state handle .shared view).2.lease handle) =
      cell.policy.addShared (state.lease handle) := by
  by_cases free : state.exclusiveCount handle = 0
  · have lease : state.lease handle =
        match state.sharedCount handle with | 0 => .free | n + 1 => .shared (n + 1) := by
      simp only [State.lease, free, ite_true]
      rfl
    rw [lease]
    cases count : state.sharedCount handle with
    | zero =>
      by_cases room : 0 < cell.policy.sharedLimit
      · have unsaturated : ¬cell.policy.sharedLimit ≤ 0 := by omega
        simp [acquire, present, free, count, unsaturated, Policy.addShared, room, Except.toOption,
          State.issue_shared_lease state handle view free]
      · have saturated : cell.policy.sharedLimit ≤ 0 := by omega
        simp [acquire, present, free, count, saturated, Policy.addShared, room, Except.toOption]
    | succ n =>
      by_cases room : n + 1 < cell.policy.sharedLimit
      · have unsaturated : ¬cell.policy.sharedLimit ≤ n + 1 := by omega
        simp [acquire, present, free, count, unsaturated, Policy.addShared, room, Except.toOption,
          State.issue_shared_lease state handle view free]
      · have saturated : cell.policy.sharedLimit ≤ n + 1 := by omega
        simp [acquire, present, free, count, saturated, Policy.addShared, room, Except.toOption]
  · simp [acquire, present, free, State.lease, Policy.addShared, Except.toOption]

/-- The identified AccountView guard model reuses the canonical shared-borrow
transition without changing runtime model semantics. -/
theorem acquire_accountView_observation {state : State Content View} {handle : Handle}
    {cell : Cell Content} (present : state.lookupCell handle = some cell)
    (policy : cell.policy = Policy.accountView) (view : View) :
    ((acquire state handle .shared view).1.toOption).map
        (fun _ => (acquire state handle .shared view).2.lease handle) =
      (state.lease handle).addShared := by
  rw [acquire_shared_observation present view, policy, accountView_addShared]

/-- A valid exclusive holder is the only live lease on its identified cell. -/
theorem exclusive_sole {state : State Content View} {guard : Guard} {slot : Slot View}
    (valid : state.Valid) (live : state.resolve guard = some slot)
    (mode : slot.mode = .exclusive) :
    state.exclusiveCount slot.cell = 1 ∧ state.sharedCount slot.cell = 0 := by
  have found := (state.resolve_some_iff.mp live).1
  obtain ⟨cell, present⟩ := valid.1 guard.id slot found
  obtain ⟨bound, excludes, _⟩ := valid.2 slot.cell cell present
  have positive : 0 < state.exclusiveCount slot.cell := by
    simpa [State.exclusiveCount, mode] using State.slot_count_positive found
  have one : state.exclusiveCount slot.cell = 1 := by omega
  exact ⟨one, excludes one⟩

/-- Dropping a valid exclusive guard frees its lease and retains current contents. -/
theorem release_exclusive_free {state : State Content View} {guard : Guard} {slot : Slot View}
    (valid : state.Valid) (live : state.resolve guard = some slot)
    (mode : slot.mode = .exclusive) :
    (release state guard).2.lease slot.cell = .free := by
  obtain ⟨exclusive, shared⟩ := exclusive_sole valid live mode
  have ex : state.count slot.cell .exclusive = 1 := exclusive
  have sh : state.count slot.cell .shared = 0 := shared
  simp [State.lease, State.exclusiveCount, State.sharedCount, release_count live, mode, ex, sh]

end Solanalib.Specs.Core.Borrow
