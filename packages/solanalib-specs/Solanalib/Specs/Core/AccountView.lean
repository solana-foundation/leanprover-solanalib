/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewData
public import Solanalib.Specs.Core.BorrowFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

universe u

/-- One account pool and its identified guards. Equal handles denote aliases;
there is no per-handle copy of the contents or borrow counter. -/
abbrev State := Borrow.State Account Slice

/-- An identity in the shared account pool, including aliases of one cell. -/
abbrev Handle := Borrow.Handle
/-- A registry token carrying a stable identity and ownership generation. -/
abbrev Guard := Borrow.Guard
/-- The shared or exclusive mode of an identified data lease. -/
abbrev Mode := Borrow.Mode

/-- The SDK errors exposed by these local AccountView operations. -/
inductive Error where
  /-- The requested operation conflicts with the current data leases. -/
  | accountBorrowFailed
  /-- The requested length or accumulated growth exceeds its admitted bound. -/
  | invalidRealloc
  deriving DecidableEq, Repr

/-- Every stored AccountView cell has its source policy and valid contents.
The common Borrow invariant supplies identified leases and mutual exclusion. -/
def PoolWellFormed {View : Type u} (state : Borrow.State Account View) : Prop :=
  state.Valid ∧ ∀ cell ∈ state.cells,
    cell.policy = Borrow.Policy.accountView ∧ cell.value.Valid

/-- The byte-range instance of the account-pool invariant. -/
def State.WellFormed (state : State) : Prop := PoolWellFormed state

/-- A handle denotes a cell in this finite pool. -/
def State.HasAccount (state : State) (handle : Handle) : Prop :=
  ∃ cell, state.lookupCell handle = some cell

/-- Read the current account. The fallback makes the mathematical observation
total; a source binding must establish that a Rust handle denotes a real cell. -/
def State.account (state : State) (handle : Handle) : Account :=
  ((state.lookupCell handle).map Borrow.Cell.value).getD Account.empty

/-- A present account is exactly the content selected by the total projection. -/
theorem State.account_of_lookup {state : State} {handle : Handle} {cell : Borrow.Cell Account}
    (present : state.lookupCell handle = some cell) :
    state.account handle = cell.value := by
  simp [State.account, present]

/-- An admissible account handle, with the complete pool invariant. -/
def Ready (state : State) (handle : Handle) : Prop :=
  state.WellFormed ∧ state.HasAccount handle

/-- The source borrow-byte observation, derived from the identified leases. -/
def isBorrowed (state : State) (handle : Handle) : Bool :=
  decide (state.lease handle ≠ Solanalib.Runtime.Lease.free)

/-- Whether an exclusive data guard is live. This does not acquire a guard. -/
def isBorrowedMut (state : State) (handle : Handle) : Bool :=
  decide (state.exclusiveCount handle ≠ 0)

/-- A reference to the address field retains its account identity. -/
structure AddressRef where
  /-- The cell whose address field this reference denotes. -/
  account : Handle
  deriving DecidableEq, Repr

/-- Owner references additionally carry the revision at which they were made.
Changing ownership or closing the account invalidates older revisions. -/
structure OwnerRef where
  /-- The cell whose owner field this reference denotes. -/
  account : Handle
  /-- The owner-field generation at reference creation. -/
  epoch : Nat
  deriving DecidableEq, Repr

/-- A dereference retains its originating guard. The Boolean distinguishes
shared access from a mutable reference; it grants no global account uniqueness. -/
structure DataRef where
  /-- The live guard authorizing the current target of this reference. -/
  guard : Guard
  /-- Whether this reference denotes mutable access through that guard. -/
  writable : Bool
  deriving DecidableEq, Repr

/-- Read the address denoted by an existing address reference. -/
def AddressRef.value (reference : AddressRef) (state : State) : Solanalib.Runtime.Pubkey :=
  (state.account reference.account).metadata.address

/-- An owner reference is usable only before its recorded revision is invalidated. -/
def OwnerRef.Valid (reference : OwnerRef) (state : State) : Prop :=
  state.HasAccount reference.account ∧
    (state.account reference.account).ownerEpoch = reference.epoch

/-- Read an owner value; callers must supply OwnerRef.Valid at the point of use. -/
def OwnerRef.value (reference : OwnerRef) (state : State) : Solanalib.Runtime.Pubkey :=
  (state.account reference.account).owner

/-- A live guard identifies its mode, existing account and current valid range. -/
def GuardReady (state : State) (mode : Mode) (guard : Guard) : Prop :=
  state.WellFormed ∧ ∃ slot cell,
    state.resolve guard = some slot ∧ state.lookupCell slot.cell = some cell ∧
    slot.mode = mode ∧ slot.view.ValidFor cell.value

/-- Read the current guard range. Invalid or consumed tokens fail in the shared
protocol; no stale acquisition snapshot is retained by the reference. -/
def guardRead (state : State) (guard : Guard) : Except Borrow.Error Solanalib.Runtime.Bytes :=
  (Borrow.current state guard).map fun (view, account) => account.read view

/-- A data reference can be used only while its originating guard remains live.
Mutable access additionally requires the exclusive mode of that guard. -/
def DataRef.Valid (reference : DataRef) (state : State) : Prop :=
  ∃ slot cell, state.resolve reference.guard = some slot ∧
    state.lookupCell slot.cell = some cell ∧ slot.view.ValidFor cell.value ∧
    (reference.writable = true → slot.mode = .exclusive)

/-- Current bytes observed through a data reference. -/
def DataRef.read (reference : DataRef) (state : State) : Except Borrow.Error
  Solanalib.Runtime.Bytes :=
  guardRead state reference.guard

/-- Direct header replacement retains all guard identities, policies and other
accounts by using the common cell-update operation. -/
def setLamports (state : State) (args : Handle × Nat) : Unit × State :=
  ((), (Borrow.modifyCell state args.1 (fun account => account.setLamports args.2)).2)

/-- All protocol failures of a checked AccountView acquisition have the AccountBorrowFailed value of
the SDK. A source binding separately identifies real cells. -/
def borrowResult {Value : Type} (result : Except Borrow.Error Value) : Except Error Value :=
  result.mapError fun _ => .accountBorrowFailed

/-- Acquire the current whole-data view using the single shared guard protocol. -/
def acquire (state : State) (handle : Handle) (mode : Mode) :
    Except Error Guard × State :=
  let step := Borrow.acquire state handle mode (state.account handle).whole
  (borrowResult step.1, step.2)

/-- A write through a live exclusive reference commits immediately to the
selected byte range. Preconditions for the source-facing write relation enforce
its range and length; this checked model also rejects stale/read-only references. -/
def writeReference (state : State) (reference : DataRef) (bytes : Solanalib.Runtime.Bytes) :
    Except Borrow.Error Unit × State :=
  if reference.writable then
    match state.resolve reference.guard with
    | none => (.error .invalidGuard, state)
    | some slot => match state.lookupCell slot.cell with
      | none => (.error .missingCell, state)
      | some cell => Borrow.write state reference.guard (cell.value.write slot.view bytes)
  else (.error .wrongMode, state)

/-- A scalar read returns a field of the current cell and preserves the pool.
Cell presence is required; metadata authentication and source widths remain
separate interpretation obligations. -/
def observationContract {Value : Type} (observe : Account → Value) :
    Solanalib.Contracts.Model State Handle Value :=
  .returning (fun before handle => before.HasAccount handle)
    (fun before handle value after => after = before ∧
      ∃ cell, before.lookupCell handle = some cell ∧ value = observe cell.value)

/-- Reference interpretation of a scalar observation. -/
def observation {Value : Type} (observe : Account → Value) (state : State) (handle : Handle) :
    Value × State := (observe (state.account handle), state)

/-- Scalar observation contracts are realized uniformly by their projection. -/
theorem observation_reference {Value : Type} (observe : Account → Value) :
    (observationContract observe).RealizedBy (observation observe) := by
  intro before handle present
  obtain ⟨cell, lookup⟩ := present
  exact ⟨rfl, cell, lookup, congrArg observe (State.account_of_lookup lookup)⟩

/-- Cloning preserves the account identity and the complete pool. -/
def clone_contract : Solanalib.Contracts.Model State Handle Handle :=
  .returning (fun _ _ => True) (fun before handle value after => after = before ∧ value = handle)

/-- The address result denotes the address field of the original account. -/
def address_contract : Solanalib.Contracts.Model State Handle AddressRef :=
  .returning (fun _ _ => True)
    (fun before handle value after => after = before ∧ value = ⟨handle⟩)

/-- The owner result retains its cell identity and current owner generation. -/
def owner_contract : Solanalib.Contracts.Model State Handle OwnerRef :=
  .returning (fun _ _ => True)
    (fun before handle value after =>
      after = before ∧ value = ⟨handle, (before.account handle).ownerEpoch⟩)

/-- Owner comparison reads the current owner of the actual cell and preserves the
pool. An absent handle cannot supply the compared owner. -/
def owned_by_contract : Solanalib.Contracts.Model State (Handle × Solanalib.Runtime.Pubkey) Bool :=
  .returning (fun before args => before.HasAccount args.1)
    (fun before args value after =>
      after = before ∧ ∃ cell, before.lookupCell args.1 = some cell ∧
        value = decide (cell.value.owner = args.2))

/-- Observe the current balance of the selected account. -/
def lamports_contract := observationContract Account.lamports
/-- Observe the current logical data length of the selected account. -/
def data_len_contract := observationContract Account.dataLen
/-- Test whether the logical length of the selected account is zero. -/
def is_data_empty_contract := observationContract (fun account => account.dataLen == 0)
/-- Observe the signer metadata without deriving authority from it. -/
def is_signer_contract := observationContract (fun account => account.metadata.signer)
/-- Observe writable metadata without changing the account. -/
def is_writable_contract := observationContract (fun account => account.metadata.writable)

/-- Replace the balance of an existing cell. Source integer widths and
preservation of the stronger pool invariant are separate conditions. -/
def set_lamports_contract : Solanalib.Contracts.Model State (Handle × Nat) Unit :=
  .returning (fun before args => before.HasAccount args.1)
    (fun before args _ after =>
      Borrow.modifyCell before args.1 (fun account => account.setLamports args.2) =
        (.ok (), after))

/-- The complete acquisition contract exposes the actual identified guard and
all registry effects of the shared protocol, not only its current bytes. -/
def borrowContract (mode : Mode) : Solanalib.Contracts.Model State Handle (Except Error Guard) :=
  .returning (fun _ _ => True)
    (fun before handle result after => ∃ protocolResult,
      Borrow.acquire before handle mode (before.account handle).whole =
        (protocolResult, after) ∧ result = borrowResult protocolResult)

/-- Acquire an identified shared guard for the current whole-data range. -/
def try_borrow_contract := borrowContract .shared
/-- Acquire an identified exclusive guard for the current whole-data range. -/
def try_borrow_mut_contract := borrowContract .exclusive

/-- Dereference makes a reference to the existing view of the guard without issuing
another lease or changing any account data. -/
def derefContract (_mode : Mode) (writable : Bool) :
    Solanalib.Contracts.Model State Guard DataRef :=
  .returning (fun _ _ => True)
    (fun before guard value after => after = before ∧ value = ⟨guard, writable⟩)

/-- The ordinary byte-profile specialization of shared dereference. -/
def ref_deref_contract := derefContract .shared false
/-- The ordinary byte-profile specialization of read-only exclusive dereference. -/
def ref_mut_deref_contract := derefContract .exclusive false
/-- The ordinary byte-profile specialization of mutable dereference. -/
def ref_mut_deref_mut_contract := derefContract .exclusive true

/-- Guard destruction consumes its identity; it does not copy data back. -/
def releaseContract (_mode : Mode) : Solanalib.Contracts.Model State Guard Unit :=
  .returning (fun before guard => ∃ slot, before.resolve guard = some slot)
    (fun before guard _ after => Borrow.release before guard = (.ok (), after))

/-- The ordinary byte-profile specialization of shared guard destruction. -/
def ref_release_contract := releaseContract .shared
/-- The ordinary byte-profile specialization of exclusive guard destruction. -/
def ref_mut_release_contract := releaseContract .exclusive

/-- A direct update of an existing cell succeeds. All other effects are the actual replacement of
the common protocol, not an independently modeled copy. -/
theorem modify_success {state : State} {handle : Handle} (present : state.HasAccount handle)
    (update : Account → Account) :
    Borrow.modifyCell state handle update =
      (.ok (), (Borrow.modifyCell state handle update).2) := by
  obtain ⟨cell, present⟩ := present
  simp [Borrow.modifyCell, Borrow.replaceCell, present]

theorem clone_reference : clone_contract.RealizedBy (fun before handle => (handle, before)) := by
  intro before handle _
  exact ⟨rfl, rfl⟩

theorem address_reference :
    address_contract.RealizedBy (fun before handle => (⟨handle⟩, before)) := by
  intro before handle _
  exact ⟨rfl, rfl⟩

theorem owner_reference : owner_contract.RealizedBy
    (fun before handle => (⟨handle, (before.account handle).ownerEpoch⟩, before)) := by
  intro before handle _
  exact ⟨rfl, rfl⟩

theorem owned_by_reference : owned_by_contract.RealizedBy
    (fun before args => (decide ((before.account args.1).owner = args.2), before)) := by
  intro before args present
  obtain ⟨cell, lookup⟩ := present
  refine ⟨rfl, cell, lookup, ?_⟩
  change decide ((before.account args.1).owner = args.2) = _
  rw [State.account_of_lookup lookup]

theorem set_lamports_reference : set_lamports_contract.RealizedBy setLamports := by
  intro before args ready
  exact modify_success ready _

theorem borrow_reference (mode : Mode) :
    (borrowContract mode).RealizedBy (fun before handle => acquire before handle mode) := by
  intro before handle _
  exact ⟨(Borrow.acquire before handle mode (before.account handle).whole).1, rfl, rfl⟩

theorem deref_reference (mode : Mode) (writable : Bool) :
    (derefContract mode writable).RealizedBy
      (fun before guard => (⟨guard, writable⟩, before)) := by
  intro before guard _
  exact ⟨rfl, rfl⟩

theorem release_reference (mode : Mode) :
    (releaseContract mode).RealizedBy
      (fun before guard => ((), (Borrow.release before guard).2)) := by
  intro before guard ready
  obtain ⟨slot, live⟩ := ready
  simp [Solanalib.Contracts.Model.ensures, releaseContract, Borrow.release, live]


/-- Checked header-only close rejects any live data lease before changing the
selected account, retaining every physical byte and the length-delta field. -/
def closeHeader (state : State) (handle : Handle) : Except Error Unit × State :=
  if isBorrowed state handle then (.error .accountBorrowFailed, state)
  else (.ok (), (Borrow.modifyCell state handle Account.closeHeader).2)

/-- Header-only close checks leases before its update. The update branch needs
an existing cell to establish successful modification. -/
def closeHeader_contract : Solanalib.Contracts.Model State Handle (Except Error Unit) :=
  .returning (fun before handle => isBorrowed before handle = false → before.HasAccount handle)
    (fun before handle result after =>
      if isBorrowed before handle then
        result = .error .accountBorrowFailed ∧ after = before
      else result = .ok () ∧
        Borrow.modifyCell before handle Account.closeHeader = (.ok (), after))

/-- The concrete header-only operation realizes each branch of its contract. -/
theorem closeHeader_reference : closeHeader_contract.RealizedBy closeHeader := by
  intro before handle ready
  change isBorrowed before handle = false → before.HasAccount handle at ready
  cases borrowed : isBorrowed before handle with
  | true => simp [closeHeader_contract, closeHeader, borrowed]
  | false =>
    have update := modify_success (ready borrowed) Account.closeHeader
    simp only [closeHeader_contract, Solanalib.Contracts.Model.ensures,
      Solanalib.Contracts.Model.returning, closeHeader, borrowed]
    exact ⟨rfl, update⟩

end Solanalib.Specs.Core.AccountView
