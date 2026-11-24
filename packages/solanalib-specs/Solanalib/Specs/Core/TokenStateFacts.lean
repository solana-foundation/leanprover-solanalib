/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenStateBorrow
public import Solanalib.Specs.Core.BorrowFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- The shared acquisition of the parser changes only the guard registry. -/
theorem acquireData_cells (state : ViewState) (handle : Borrow.Handle)
    (account : AccountView.Account) :
    (acquireData state handle account).2.cells = state.cells := by
  have preserved : (Borrow.acquire state handle .shared account.whole).2.cells = state.cells := by
    cases present : state.lookupCell handle with
    | none => simp [Borrow.acquire, present]
    | some cell =>
      by_cases conflict : state.exclusiveCount handle ≠ 0
      · simp [Borrow.acquire, present, conflict]
      · by_cases saturated : cell.policy.sharedLimit ≤ state.sharedCount handle
        · simp [Borrow.acquire, present, conflict, saturated]
        · simp [Borrow.acquire, present, conflict, saturated, Borrow.State.issue]
  cases acquired : Borrow.acquire state handle .shared account.whole with
  | mk result after =>
    simpa only [acquireData, acquired] using preserved

/-- Narrowing a successfully borrowed view preserves every account and policy. -/
theorem mapView_cells (state : ViewState) (guard : Borrow.Guard) (kind : ViewKind) :
    (mapView state guard kind).2.cells = state.cells :=
  Borrow.transfer_cells state guard ⟨0, kind.length⟩

/-- Rejected extended data preserve every account and policy. -/
theorem rejectedView_cells (state : ViewState) (guard : Borrow.Guard) :
    (rejectedView state guard).2.cells = state.cells :=
  Borrow.release_cells state guard

/-- A rejected extended layout consumes the temporary acquisition. -/
theorem rejectedView_consumes {state : ViewState} {guard : Borrow.Guard}
    {slot : Borrow.Slot AccountView.Slice}
    (live : state.resolve guard = some slot) :
    (rejectedView state guard).2.resolve guard = none :=
  Borrow.release_consumes live

/-- Successful view mapping retains exactly the original cell and shared/exclusive
mode under a fresh token generation. It does not manufacture a second lease. -/
theorem mapView_resolves {state : ViewState} {guard : Borrow.Guard}
    {slot : Borrow.Slot AccountView.Slice}
    (live : state.resolve guard = some slot) (kind : ViewKind) :
    (mapView state guard kind).1 = .ok ⟨⟨guard.id, guard.generation + 1⟩, kind⟩ ∧
    (mapView state guard kind).2.resolve ⟨guard.id, guard.generation + 1⟩ =
      some { slot with generation := guard.generation + 1, view := ⟨0, kind.length⟩ } ∧
    (mapView state guard kind).2.resolve guard = none := by
  refine ⟨?_, Borrow.transfer_resolves live ⟨0, kind.length⟩,
    Borrow.transfer_consumes live ⟨0, kind.length⟩⟩
  simp [mapView, Borrow.transfer_live live, Except.map, Except.mapError]

/-- Availability is an actual count of the current guard records. Acquisition
returns the fresh issue identity and preserves the selected data view. -/
theorem acquireData_available {state : ViewState} {handle : Borrow.Handle}
    {cell : Borrow.Cell AccountView.Account}
    (present : state.lookupCell handle = some cell)
    (exclusive : state.exclusiveCount handle = 0)
    (room : state.sharedCount handle < cell.policy.sharedLimit) :
    acquireData state handle cell.value =
      (.ok (state.issue handle .shared cell.value.whole).1,
        (state.issue handle .shared cell.value.whole).2) := by
  simp [acquireData, Borrow.acquire, present, exclusive, Nat.not_le.mpr room,
    Borrow.State.issue, Except.mapError]

/-- Every path through the local parser preserves every account byte/header,
including early errors and guard retirement after invalid token-2022 data. -/
theorem fromAccountView_cells (revision : ViewRevision) (kind : ViewKind)
    (state : ViewState) (handle : Borrow.Handle) :
    (fromAccountView revision kind state handle).2.cells = state.cells := by
  unfold fromAccountView
  split
  · rfl
  · rename_i cell present
    split
    · rfl
    · split
      · rfl
      · have same := acquireData_cells state handle cell.value
        cases acquired : acquireData state handle cell.value with
        | mk result afterBorrow =>
          simp only [acquired] at same
          cases result with
          | error error =>
            simpa only using same
          | ok guard =>
            dsimp only
            split
            · exact (rejectedView_cells afterBorrow guard).trans same
            · exact (mapView_cells afterBorrow guard kind).trans same

/-- A live field reference denotes the exact checked bytes of its original
account allocation, rather than an independently supplied key snapshot. -/
theorem currentKey_of_current {state : ViewState} {ref : KeyRef}
    {view : AccountView.Slice} {account : AccountView.Account}
    (current : Borrow.current state ref.guard = .ok (view, account))
    (field : ref.offset + 32 ≤ view.length)
    (inside : view.offset + view.length ≤ account.dataLen)
    (backing : account.dataLen ≤ account.backing.length) :
    currentKey state ref =
      .ok (.ofBytes (Solanalib.Runtime.slice account.backing (view.offset + ref.offset) 32)) := by
  have full : view.offset + ref.offset + 32 ≤ account.backing.length := by omega
  simp [currentKey, current, field, inside, backing, readKey, full]

/-- Reading through a field reference agrees with reading that same field
inside the typed byte view of the parent. -/
theorem currentKey_view {state : ViewState} {ref : KeyRef}
    {view : AccountView.Slice} {account : AccountView.Account}
    (current : Borrow.current state ref.guard = .ok (view, account))
    (field : ref.offset + 32 ≤ view.length)
    (inside : view.offset + view.length ≤ account.dataLen)
    (backing : account.dataLen ≤ account.backing.length) :
    currentKey state ref =
      .ok (.ofBytes (Solanalib.Runtime.slice (account.read view) ref.offset 32)) := by
  rw [currentKey_of_current current field inside backing]
  simp only [AccountView.Account.read, Solanalib.Runtime.slice_slice field]

/-- A concrete single-cell state for closed model witnesses. Its empty guard
registry is independent of token bytes or program ownership. -/
def viewWitnessState (owner : Solanalib.Runtime.Pubkey) (bytes : Bytes) : ViewState :=
  let account : AccountView.Account := { AccountView.Account.empty with
    owner := owner
    dataLen := bytes.length
    entryLen := bytes.length
    backing := bytes }
  ⟨[⟨account, .accountView⟩], []⟩

/-- A finite empty guard registry satisfies the shared lease invariant. -/
theorem viewWitnessState_protocol (owner : Solanalib.Runtime.Pubkey) (bytes : Bytes) :
    (viewWitnessState owner bytes).Valid := by
  constructor
  · intro id slot found
    simp [viewWitnessState, Borrow.State.lookupSlot] at found
  · intro handle cell found
    simp [viewWitnessState, Borrow.State.exclusiveCount, Borrow.State.sharedCount,
      Borrow.State.count]

/-- The raw all-zero account is admitted by both Pinocchio readers. It need not
be initialized; later SPL Pack decoding has a different admission rule. -/
def accountWitness : AccountRaw :=
  ⟨List.replicate accountLength 0, by simp⟩

/-- The raw all-zero mint witnesses permissive view parsing, independently of
the initialized-mint requirement of SPL. -/
def mintWitness : MintRaw :=
  ⟨List.replicate mintLength 0, by simp⟩

/-- A live typed account guard for closed field-reference witnesses. -/
def accountWitnessState : ViewState :=
  { viewWitnessState legacyProgramId accountWitness.bytes with
    slots := [some ⟨⟨0⟩, .shared, 1, ⟨0, accountLength⟩⟩] }

/-- A live typed mint guard for closed decimal-reference witnesses. -/
def mintWitnessState : ViewState :=
  { viewWitnessState legacyProgramId mintWitness.bytes with
    slots := [some ⟨⟨0⟩, .shared, 1, ⟨0, mintLength⟩⟩] }

/-- The returned token of the concrete account acquisition. -/
def accountWitnessRef : Ref := ⟨⟨0, 1⟩, .account⟩

/-- The returned token of the concrete mint acquisition. -/
def mintWitnessRef : Ref := ⟨⟨0, 1⟩, .mint⟩

/-- The account witness reads the current guarded bytes exactly. -/
theorem accountWitness_current :
    currentAccount accountWitnessState accountWitnessRef = .ok accountWitness := by
  simp only [currentAccount, currentBytes, Borrow.current, Borrow.State.resolve,
    Borrow.State.lookupSlot, Borrow.State.lookupCell, accountWitnessState,
    accountWitnessRef, viewWitnessState, AccountView.Account.read, Solanalib.Runtime.slice,
    accountWitness, ViewKind.length, readAccountRaw, Except.bind,
    List.getElem?_cons_zero, Option.bind_some, List.length_replicate,
    Nat.zero_add, Nat.le_refl, and_self, ↓reduceIte, ↓reduceDIte, List.drop_zero,
    List.take_replicate, Nat.min_self]

/-- The mint witness reads the current guarded bytes exactly. -/
theorem mintWitness_current :
    currentMint mintWitnessState mintWitnessRef = .ok mintWitness := by
  rfl

end Solanalib.Specs.Core.Token
