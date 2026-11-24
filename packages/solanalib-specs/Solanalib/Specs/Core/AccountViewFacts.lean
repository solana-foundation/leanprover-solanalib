/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountView
public import Solanalib.Specs.Core.BorrowLifecycle

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

universe u

/-- Every existing cell inherits the account-pool representation and policy. -/
theorem PoolWellFormed.lookup {View : Type u} {state : Borrow.State Account View}
    (valid : PoolWellFormed state) {handle : Handle} {cell : Borrow.Cell Account}
    (present : state.lookupCell handle = some cell) :
    cell.policy = Borrow.Policy.accountView ∧ cell.value.Valid :=
  valid.2 cell (List.mem_of_getElem? present)

/-- A valid cell replacement preserves the complete account-pool invariant,
independently of the interpreted target descriptor type. -/
theorem PoolWellFormed.replace {View : Type u} {state : Borrow.State Account View}
    (valid : PoolWellFormed state) (handle : Handle) {value : Account}
    (contents : value.Valid) : PoolWellFormed (Borrow.replaceCell state handle value).2 := by
  refine ⟨Borrow.replaceCell_valid valid.1 _ _, ?_⟩
  intro next member
  cases present : state.lookupCell handle with
  | none => exact valid.2 next (by simpa [Borrow.replaceCell, present] using member)
  | some old =>
    simp only [Borrow.replaceCell, present] at member
    rcases List.mem_or_eq_of_mem_set member with prior | equal
    · exact valid.2 next prior
    · subst next
      exact ⟨(valid.lookup present).1, contents⟩

/-- Pure registry changes preserve the stored representation of every account. -/
theorem PoolWellFormed.sameCells {View : Type u}
    {before after : Borrow.State Account View} (valid : PoolWellFormed before)
    (protocol : after.Valid) (cells : after.cells = before.cells) : PoolWellFormed after :=
  ⟨protocol, fun cell member => valid.2 cell (by simpa [cells] using member)⟩

/-- Transferring a view preserves account contents, policy and lease validity. -/
theorem PoolWellFormed.transfer {View : Type u} {state : Borrow.State Account View}
    (valid : PoolWellFormed state) (guard : Guard) (view : View) :
    PoolWellFormed (Borrow.transfer state guard view).2 :=
  valid.sameCells (Borrow.transfer_valid valid.1 guard view) (Borrow.transfer_cells _ _ _)

/-- Guard release preserves all account contents and every remaining lease. -/
theorem PoolWellFormed.release {View : Type u} {state : Borrow.State Account View}
    (valid : PoolWellFormed state) (guard : Guard) :
    PoolWellFormed (Borrow.release state guard).2 :=
  valid.sameCells (Borrow.release_valid valid.1 guard) (Borrow.release_cells _ _)

/-- An existing account projection has the stored representation invariant. -/
theorem Ready.account_valid {state : State} {handle : Handle} (ready : Ready state handle) :
    (state.account handle).Valid := by
  obtain ⟨cell, present⟩ := ready.2
  rw [State.account_of_lookup present]
  exact (ready.1.lookup present).2

/-- Direct account modification updates exactly the selected identity. -/
theorem modify_lookup {state : State} {handle : Handle} {cell : Borrow.Cell Account}
    (present : state.lookupCell handle = some cell) (update : Account → Account) :
    (Borrow.modifyCell state handle update).2.lookupCell handle =
      some { cell with value := update cell.value } := by
  simpa only [Borrow.modifyCell, present] using Borrow.replaceCell_lookup present (update
    cell.value)

/-- Direct modification preserves the account-pool invariant when the new
contents are valid. Permission to make that modification is operation-specific. -/
theorem modify_wellFormed {state : State} {handle : Handle} (ready : Ready state handle)
    (update : Account → Account) (valid : (update (state.account handle)).Valid) :
    State.WellFormed (Borrow.modifyCell state handle update).2 := by
  obtain ⟨cell, present⟩ := ready.2
  rw [State.account_of_lookup present] at valid
  simpa only [State.WellFormed, Borrow.modifyCell, present] using ready.1.replace handle valid

/-- A cloned handle observes the same immediately updated balance. -/
theorem setLamports_alias {state : State} {handle : Handle} (ready : state.HasAccount handle)
    (value : Nat) :
    ((setLamports state (handle, value)).2.account handle.alias).lamports = value := by
  obtain ⟨cell, present⟩ := ready
  change (State.account
    (Borrow.modifyCell state handle (fun account => account.setLamports value)).2 handle).lamports
      = value
  rw [State.account_of_lookup (modify_lookup present _)]
  rfl

/-- Setting a bounded balance preserves the pool and all data-lease identities. -/
theorem setLamports_wellFormed {state : State} {handle : Handle}
    (ready : Ready state handle) {value : Nat} (bound : value < Solanalib.Runtime.U64_LIMIT) :
    (setLamports state (handle, value)).2.WellFormed :=
  modify_wellFormed ready _ (Account.setLamports_valid ready.account_valid.2 bound)

/-- A successful source acquisition is exactly a successful common acquisition;
mapping the errors of the protocol cannot fabricate a successful token. -/
theorem acquire_protocol_success {state after : State} {handle : Handle}
    {mode : Mode} {guard : Guard}
    (success : acquire state handle mode = (.ok guard, after)) :
    Borrow.acquire state handle mode (state.account handle).whole = (.ok guard, after) := by
  unfold acquire at success
  cases step : Borrow.acquire state handle mode (state.account handle).whole with
  | mk result next =>
    cases result <;> simp_all [borrowResult, Except.mapError]

/-- An acquired source guard denotes the current whole-data bytes. The guard,
rather than these bytes, is retained by the complete API for later use. -/
theorem acquire_reads {state after : State} {handle : Handle} {mode : Mode} {guard : Guard}
    (success : acquire state handle mode = (.ok guard, after)) :
    guardRead after guard = .ok (state.account handle).bytes := by
  have protocol := acquire_protocol_success success
  obtain ⟨_, _, cell, present⟩ := Borrow.acquire_success protocol
  have current := Borrow.acquire_current protocol present
  simp only [guardRead, current, Except.map]
  rw [State.account_of_lookup present, Account.read_whole]

/-- A successful acquisition returns a guard meeting the complete ordinary
data-reference precondition. -/
theorem acquire_guardReady {state after : State} {handle : Handle} {mode : Mode} {guard : Guard}
    (ready : state.WellFormed) (success : acquire state handle mode = (.ok guard, after)) :
    GuardReady after mode guard := by
  have protocol := acquire_protocol_success success
  obtain ⟨live, cells, cell, present⟩ := Borrow.acquire_success protocol
  have afterValid : after.Valid := by
    have preserved := Borrow.acquire_valid ready.1 handle mode (state.account handle).whole
    simpa only [protocol] using preserved
  refine ⟨ready.sameCells afterValid cells, _, cell, live, ?_, rfl, ?_⟩
  · simpa [Borrow.State.lookupCell, cells] using present
  · rw [State.account_of_lookup present]
    exact cell.value.whole_valid

/-- Same-size writes are immediately visible through the same mutable guard. -/
theorem writeReference_reads {state : State} {reference : DataRef} {slot : Borrow.Slot Slice}
    {cell : Borrow.Cell Account} (writable : reference.writable = true)
    (live : state.resolve reference.guard = some slot)
    (present : state.lookupCell slot.cell = some cell) (mode : slot.mode = .exclusive)
    (capacity : cell.value.dataLen ≤ cell.value.backing.length) (inside : slot.view.ValidFor
      cell.value)
    {bytes : Solanalib.Runtime.Bytes} (length : bytes.length = slot.view.length) :
    reference.read (writeReference state reference bytes).2 = .ok bytes := by
  simp only [DataRef.read, writeReference, writable, live, present, ite_true, guardRead]
  rw [Borrow.write_current live mode present]
  simp only [Except.map]
  rw [Account.read_write capacity inside length]

/-- Released tokens cannot observe old bytes, even when the backing still exists. -/
theorem read_released {state : State} {guard : Guard} {slot : Borrow.Slot Slice}
    (live : state.resolve guard = some slot) :
    guardRead (Borrow.release state guard).2 guard = .error .invalidGuard := by
  simp [guardRead, Borrow.current_after_release live, Except.map]

/-- The complete model can be forgotten to the legacy account-pool observation.
Exclusive bytes are hidden only in this projection; the current bytes remain in
the shared cell for the exclusive guard itself. -/
def observe (state : State) (handle : Handle) : AccountViewObservation.State :=
  let account := state.account handle
  ⟨account.metadata,
    ⟨account.owner, account.lamports, account.dataLen, account.entryLen,
      state.lease handle,
      if state.lease handle = .exclusive then none else some account.bytes⟩⟩

/-- Every admissible complete state has a valid legacy observation. -/
theorem observe_valid {state : State} {handle : Handle} (ready : Ready state handle) :
    (observe state handle).Valid := by
  obtain ⟨cell, present⟩ := ready.2
  have valid := ready.account_valid
  have policy := (ready.1.lookup present).1
  have bound := (ready.1.1.2 handle cell present).2.2
  rw [policy] at bound
  change state.sharedCount handle ≤ 254 at bound
  refine ⟨valid.1, valid.2.1, ?_⟩
  by_cases exclusive : state.exclusiveCount handle = 0
  · cases count : state.sharedCount handle with
    | zero =>
      have lease : (observe state handle).account.lease = .free := by
        simp [observe, Borrow.State.lease, exclusive, count]
      rw [lease]
      change ∃ bytes, (observe state handle).account.data = some bytes ∧
        bytes.length = (observe state handle).account.dataLen
      exact ⟨(state.account handle).bytes, by simp [observe, Borrow.State.lease, exclusive, count],
        Account.bytes_length valid.2.2.2⟩
    | succ n =>
      have lease : (observe state handle).account.lease = .shared (n + 1) := by
        simp [observe, Borrow.State.lease, exclusive, count]
      rw [lease]
      change 0 < n + 1 ∧ n + 1 ≤ 254 ∧
        ∃ bytes, (observe state handle).account.data = some bytes ∧
          bytes.length = (observe state handle).account.dataLen
      refine ⟨by omega, by omega, (state.account handle).bytes, ?_, Account.bytes_length
        valid.2.2.2⟩
      simp [observe, Borrow.State.lease, exclusive, count]
  · have lease : (observe state handle).account.lease = .exclusive := by
      simp [observe, Borrow.State.lease, exclusive]
    rw [lease]
    change (observe state handle).account.data = none
    simp [observe, Borrow.State.lease, exclusive]

/-- The three scalar preparation contracts are exact projections of the complete
account model. They cannot independently describe guard lifetimes. -/
theorem scalar_observations (state : State) (handle : Handle) :
    (observe state handle).account.lamports = (state.account handle).lamports ∧
    (observe state handle).account.dataLen = (state.account handle).dataLen ∧
    (observe state handle).metadata.signer = (state.account handle).metadata.signer :=
  ⟨rfl, rfl, rfl⟩

/-- The observation of the balance setter retains the old preparation API exactly. -/
theorem setLamports_observation {state : State} {handle : Handle}
    (ready : state.HasAccount handle) (value : Nat) :
    observe (setLamports state (handle, value)).2 handle =
      (observe state handle).setLamports value := by
  obtain ⟨cell, present⟩ := ready
  have found := modify_lookup present (fun account => account.setLamports value)
  have unchanged : (setLamports state (handle, value)).2.lease handle = state.lease handle := by
    simp only [setLamports, Borrow.modifyCell, present]
    simp [Borrow.State.lease, Borrow.State.exclusiveCount, Borrow.State.sharedCount,
      Borrow.State.count, Borrow.replaceCell_slots]
  simp only [observe, setLamports, State.account_of_lookup found, State.account_of_lookup present]
  change _ = _
  simp only [← show (setLamports state (handle, value)).2.lease handle = _ from unchanged]
  rfl

/-- Successful header-only close changes the header of the selected account. -/
theorem closeHeader_account {state : State} {handle : Handle} (ready : state.HasAccount handle)
    (free : isBorrowed state handle = false) :
    (closeHeader state handle).2.account handle = (state.account handle).closeHeader := by
  obtain ⟨cell, present⟩ := ready
  simp only [closeHeader, free, Bool.false_eq_true, ↓reduceIte]
  rw [State.account_of_lookup (modify_lookup present _), State.account_of_lookup present]

/-- Header-only close invalidates prior owner references after its lease check. -/
theorem owner_invalidated_by_closeHeader {state : State} {handle : Handle} {reference : OwnerRef}
    (alias : reference.account = handle)
    (valid : reference.Valid state) (free : isBorrowed state handle = false) :
    ¬ reference.Valid (closeHeader state handle).2 := by
  intro later
  have old := valid.2
  have next := later.2
  rw [alias] at old next
  rw [closeHeader_account (by simpa [alias] using valid.1) free] at next
  change (state.account handle).ownerEpoch + 1 = reference.epoch at next
  omega

end Solanalib.Specs.Core.AccountView
