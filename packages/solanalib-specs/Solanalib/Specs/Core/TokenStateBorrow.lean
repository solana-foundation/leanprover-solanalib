/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenState
public import Solanalib.Specs.Core.AccountViewData
public import Solanalib.Specs.Core.Borrow
public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- The two byte-view types exposed by the selected Pinocchio token crates. -/
inductive ViewKind where
  /-- A 165-byte token account. -/
  | account
  /-- An 82-byte mint. -/
  | mint
  deriving DecidableEq, Repr

/-- The size of the typed base view, excluding any token-2022 extension area. -/
def ViewKind.length : ViewKind → Nat
  | .account => accountLength
  | .mint => mintLength

/-- The token-2022 discriminator byte following its common 165-byte base area. -/
def ViewKind.typeByte : ViewKind → UInt8
  | .account => 2
  | .mint => 1

/-- The two selected Pinocchio parser policies. They share byte projections
but differ in ownership/length/borrow ordering and extension admission. -/
inductive ViewRevision where
  /-- The legacy-only exact-size parser in Pinocchio-token 0.6.0. -/
  | legacy
  /-- The extensible parser in Pinocchio-token-2022 0.3.1. -/
  | token2022
  deriving DecidableEq, Repr

/-- The same identified account/guard state used by AccountView. -/
abbrev ViewState := Borrow.State AccountView.Account AccountView.Slice

/-- A typed borrowed view retains its guard identity and current generation.
The recorded kind is a logical type, not an extra byte in the value of Rust. -/
structure Ref where
  /-- The actual shared Borrow token, including its current generation. -/
  guard : Borrow.Guard
  /-- The byte-view type checked by typed getters. -/
  kind : ViewKind
  deriving DecidableEq, Repr

/-- A field reference borrows from an existing guard. It creates no new lease
and never snapshots the current bytes of the field. -/
structure KeyRef where
  /-- The existing parent token that bounds the lifetime of this field reference. -/
  guard : Borrow.Guard
  /-- The byte offset of the field within the current parent view. -/
  offset : Nat
  deriving DecidableEq, Repr

/-- Ownership errors differ between mint and account readers even though the
runtime account owner is checked at the same point in each revision. -/
def viewOwnerError : ViewKind → Error
  | .account => .InvalidAccountData
  | .mint => .InvalidAccountOwner

/-- The selected token program owns the runtime account containing these bytes. -/
def ViewRevision.programId : ViewRevision → Solanalib.Runtime.Pubkey
  | .legacy => legacyProgramId
  | .token2022 => token2022ProgramId

/-- Checked acquisition mapped to the documented borrow error of the SDK. Existing
source handles and their representation remain Rust-binding obligations. -/
def acquireData (state : ViewState) (handle : Borrow.Handle)
    (account : AccountView.Account) : Except Error Borrow.Guard × ViewState :=
  let (result, after) := Borrow.acquire state handle .shared account.whole
  (result.mapError (fun _ => (.AccountBorrowFailed : Error)), after)

/-- Release the shared guard already acquired by a failed token-2022 parser. Slots
retain the common tombstone identity history; no data or live lease is retained. -/
def rejectedView (state : ViewState) (guard : Borrow.Guard) :
    Except Error Ref × ViewState :=
  (.error .InvalidAccountData, (Borrow.release state guard).2)

/-- Ref::map consumes the whole-data token and retains its lease under a new
generation and a base-sized view. Protocol failures have no source analogue for
a valid Rust guard; their total-reference fallback is AccountBorrowFailed. -/
def mapView (state : ViewState) (guard : Borrow.Guard) (kind : ViewKind) :
    Except Error Ref × ViewState :=
  let (mapped, after) := Borrow.transfer state guard ⟨0, kind.length⟩
  (mapped.map (fun next => ⟨next, kind⟩) |>.mapError
    (fun _ => (.AccountBorrowFailed : Error)), after)

/-- Exact ordinary parser preparation. Legacy checks length then owner before
borrowing. Token-2022 checks owner, borrows, then validates the base/type layout;
a layout error releases that guard. Neither path tests initialization or TLVs. -/
def fromAccountView (revision : ViewRevision) (kind : ViewKind)
    (state : ViewState) (handle : Borrow.Handle) : Except Error Ref × ViewState :=
  match state.lookupCell handle with
  | none => (.error .InvalidAccountData, state)
  | some cell =>
    if revision = .legacy ∧ cell.value.dataLen ≠ kind.length then
      (.error .InvalidAccountData, state)
    else if cell.value.owner ≠ revision.programId then
      (.error (viewOwnerError kind), state)
    else
      let (acquired, afterBorrow) := acquireData state handle cell.value
      match acquired with
      | .error error => (.error error, afterBorrow)
      | .ok guard =>
        if revision = .token2022 ∧
            pinocchio2022Layout cell.value.bytes kind.length kind.typeByte = false then
          rejectedView afterBorrow guard
        else mapView afterBorrow guard kind

/-- Read a current typed range. Failure here records a violated logical
reference premise; ordinary field getters do not return this helper error. -/
def currentBytes (state : ViewState) (ref : Ref) : Except Error Bytes :=
  match Borrow.current state ref.guard with
  | .error _ => .error .InvalidAccountData
  | .ok (view, account) =>
    if view.length = ref.kind.length ∧ view.offset + view.length ≤ account.dataLen ∧
        account.dataLen ≤ account.backing.length then
      .ok (account.read view)
    else .error .InvalidAccountData

/-- Observe the raw account currently borrowed by this reference. -/
def currentAccount (state : ViewState) (ref : Ref) : Except Error AccountRaw :=
  if ref.kind = .account then (currentBytes state ref).bind readAccountRaw
  else .error .InvalidAccountData

/-- Observe the raw mint currently borrowed by this reference. -/
def currentMint (state : ViewState) (ref : Ref) : Except Error MintRaw :=
  if ref.kind = .mint then (currentBytes state ref).bind readMintRaw
  else .error .InvalidAccountData

/-- A field reference reads through its still-live original guard and checks
the whole 32-byte field against the currently recorded view and data extent. -/
def currentKey (state : ViewState) (ref : KeyRef) : Except Error Solanalib.Runtime.Pubkey :=
  match Borrow.current state ref.guard with
  | .error _ => .error .InvalidAccountData
  | .ok (view, account) =>
    if ref.offset + 32 ≤ view.length ∧
        view.offset + view.length ≤ account.dataLen ∧
        account.dataLen ≤ account.backing.length then
      match readKey account.backing (view.offset + ref.offset) with
      | some key => .ok key
      | none => .error .InvalidAccountData
    else .error .InvalidAccountData

/-- Normal field reads require a current, complete raw account view. This
retains the guard capability; raw bytes alone do not satisfy the premise. -/
def AccountReadable (state : ViewState) (ref : Ref) : Prop :=
  ∃ raw, currentAccount state ref = .ok raw

/-- Normal decimal reads require a current, complete raw mint view. -/
def MintReadable (state : ViewState) (ref : Ref) : Prop :=
  ∃ raw, currentMint state ref = .ok raw

/-- A token balance read changes no account, guard, generation or view. The
fallback is outside AccountReadable and supplies no source-lifetime claim. -/
def amountReference (state : ViewState) (ref : Ref) : Nat × ViewState :=
  (match currentAccount state ref with | .ok raw => raw.amount | .error _ => 0, state)

/-- The mint-key field shares the existing guard identity of the parent. -/
def mintReference (state : ViewState) (ref : Ref) : KeyRef × ViewState :=
  (⟨ref.guard, 0⟩, state)

/-- The token-owner field shares the existing guard identity of the parent. -/
def ownerReference (state : ViewState) (ref : Ref) : KeyRef × ViewState :=
  (⟨ref.guard, 32⟩, state)

/-- Decimal precision is observed without changing the mint or its guard. -/
def decimalsReference (state : ViewState) (ref : Ref) : UInt8 × ViewState :=
  (match currentMint state ref with | .ok raw => raw.decimals | .error _ => 0, state)

/-- Invalid state conversion is an explicit panic event; no ordinary value is
available. The supplied handler selects target-specific unwind/terminal effects. -/
abbrev StatePanic (Unwind Terminal : Type) :=
  Callback.Run ViewState UInt8 Empty Unwind Terminal

/-- The state getter returns the enum value for 0/1/2 or forwards the actual panic
handler outcome. A handler cannot return an ordinary value because its result
type is Empty. Invalid/consumed reference premises admit no modeled exit. -/
def stateRun {Unwind Terminal : Type} (panic : StatePanic Unwind Terminal)
    (before : ViewState) (ref : Ref) :
    Outcome ViewState AccountState Unwind Terminal → Prop :=
  match currentAccount before ref with
  | .error _ => fun _ => False
  | .ok raw =>
    match decodeAccountState raw.stateByte with
    | some state => fun outcome => outcome = .returned state before
    | none => Callback.map (fun impossible : Empty => nomatch impossible) panic
        before raw.stateByte

/-- Legacy length rejection happens before owner and borrow checks, preserving
all current account contents and guard history. -/
theorem fromAccountView_legacy_length {state : ViewState} {handle : Borrow.Handle}
    {cell : Borrow.Cell AccountView.Account} {kind : ViewKind}
    (present : state.lookupCell handle = some cell)
    (wrong : cell.value.dataLen ≠ kind.length) :
    fromAccountView .legacy kind state handle = (.error .InvalidAccountData, state) := by
  simp [fromAccountView, present, wrong]

/-- An owner error occurs before any borrow on the token-2022 path. -/
theorem fromAccountView_2022_owner {state : ViewState} {handle : Borrow.Handle}
    {cell : Borrow.Cell AccountView.Account} {kind : ViewKind}
    (present : state.lookupCell handle = some cell)
    (wrong : cell.value.owner ≠ token2022ProgramId) :
    fromAccountView .token2022 kind state handle = (.error (viewOwnerError kind), state) := by
  simp [fromAccountView, present, ViewRevision.programId, wrong]

/-- A field read always preserves the entire shared state. -/
theorem amountReference_state (state : ViewState) (ref : Ref) :
    (amountReference state ref).2 = state := rfl

/-- Current guard observations determine the token amount exactly. -/
theorem amountReference_of_current {state : ViewState} {ref : Ref} {raw : AccountRaw}
    (current : currentAccount state ref = .ok raw) :
    amountReference state ref = (raw.amount, state) := by
  simp [amountReference, current]

/-- Current guard observations determine the mint decimals exactly. -/
theorem decimalsReference_of_current {state : ViewState} {ref : Ref} {raw : MintRaw}
    (current : currentMint state ref = .ok raw) :
    decimalsReference state ref = (raw.decimals, state) := by
  simp [decimalsReference, current]

end Solanalib.Specs.Core.Token
