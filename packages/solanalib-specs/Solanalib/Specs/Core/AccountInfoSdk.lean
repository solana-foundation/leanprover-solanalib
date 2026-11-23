/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoFacts
public import Solanalib.Specs.Core.BorrowLifecycle

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountInfoSdk

open AccountInfo

/-- Identity of the existing shared AccountInfo reference. Returning `self`
preserves this identity, rather than creating another owned AccountInfo. -/
structure Reference where
  id : Nat
  deriving DecidableEq, Repr

/-- Reflexive AsRef neither reads the pointee nor clones its Rc fields. -/
def asRef (state : AccountInfo.State) (reference : Reference) :
    Reference × AccountInfo.State := (reference, state)

def asRefContract : Solanalib.Contracts.Model AccountInfo.State Reference Reference :=
  .returning (fun _ _ => True)
    (fun before input output after => output = input ∧ after = before)

theorem asRef_realizes : asRefContract.RealizedBy asRef := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

/-- Only the selected current lamports cell and the common lease invariant are
needed to return a typed live guard; flags and the data cell are not premises. -/
def LamportsBorrowReady (state : AccountInfo.State) (info : AccountInfo.Value) : Prop :=
  state.Valid ∧ ∃ amount policy, state.lookupCell info.lamports = some ⟨.lamports amount, policy⟩

def borrowLamports (mode : Borrow.Mode) (state : AccountInfo.State) (args : Args) :=
  AccountInfo.tryBorrow mode args.info.lamports state

def lamportsBorrowContract (mode : Borrow.Mode) :
    Solanalib.Contracts.Model AccountInfo.State Args (Except ProgramError.Value Borrow.Guard) :=
  .returning (fun state args => LamportsBorrowReady state args.info)
    (fun before args result after =>
      borrowLamports mode before args = (result, after) ∧ after.Valid ∧
        match result with
        | .ok guard => ∃ amount, Borrow.current after guard = .ok (.whole, .lamports amount)
        | .error _ => True)

theorem lamportsBorrow_realizes (mode : Borrow.Mode) :
    (lamportsBorrowContract mode).RealizedBy (borrowLamports mode) := by
  intro state args ready
  obtain ⟨valid, amount, policy, present⟩ := ready
  have invariant := Borrow.acquire_valid valid args.info.lamports mode View.whole
  cases acquired : Borrow.acquire state args.info.lamports mode View.whole with
  | mk result after =>
    have afterValid : after.Valid := by simpa only [acquired] using invariant
    cases result with
    | error error =>
      simp only [borrowLamports, AccountInfo.tryBorrow, acquired, Except.mapError]
      exact ⟨by simp [borrowLamports, AccountInfo.tryBorrow, acquired, Except.mapError],
        afterValid, trivial⟩
    | ok guard =>
      simp only [borrowLamports, AccountInfo.tryBorrow, acquired, Except.mapError]
      exact ⟨by simp [borrowLamports, AccountInfo.tryBorrow, acquired, Except.mapError],
        afterValid, amount, Borrow.acquire_current acquired present⟩

theorem sample_lamportsReady : LamportsBorrowReady sampleState sampleInfo :=
  ⟨sample_valid.2.1, 40, sampleProfile.policy, rfl⟩

/-- The checked length getter maps a temporary shared-borrow failure to the
unit SDK error. On success that guard has already been released. `none` is an
unrepresented mathematical input, not a source return value. -/
def tryDataLen (state : AccountInfo.State) (args : Args) :
    Option (Except ProgramError.Value Nat × AccountInfo.State) :=
  match observe .dataLen state args.info with
  | (.value value, after) => some (.ok value, after)
  | (.borrowFailed, after) => some (.error .accountBorrowFailed, after)
  | (.malformed, _) => none

def tryDataLenReference (state : AccountInfo.State) (args : Args) :
    Outcome AccountInfo.State (Except ProgramError.Value Nat) Empty Empty → Prop
  | .returned value after => tryDataLen state args = some (value, after)
  | .unwound impossible _ | .terminated impossible => nomatch impossible

def tryDataLenContract :
    Solanalib.Contracts.Model AccountInfo.State Args (Except ProgramError.Value Nat) where
  requires := fun state args => ObservationReady .dataLen state args.info
  post := tryDataLenReference

theorem tryDataLen_exists (state : AccountInfo.State) (args : Args)
    (ready : ObservationReady .dataLen state args.info) :
    ∃ result after, tryDataLen state args = some (result, after) := by
  have good := observe_not_malformed .dataLen state args.info ready
  cases step : observe .dataLen state args.info with
  | mk value after =>
    cases value with
    | malformed => simp [step] at good
    | value value => exact ⟨.ok value, after, by simp [tryDataLen, step]⟩
    | borrowFailed => exact ⟨.error .accountBorrowFailed, after, by simp [tryDataLen, step]⟩

theorem tryDataLen_holds : tryDataLenContract.Holds tryDataLenReference := by
  intro _ _ _ _ step
  exact step

/-- The boolean getter has the same borrowing, panic strategy and cleanup as
`data_len`; only its successfully returned observation changes. -/
def dataIsEmptyReference (state : AccountInfo.State) (args : Args) :
    Outcome AccountInfo.State Bool Panic Panic → Prop := fun outcome =>
  match observe .dataLen state args.info with
  | (.value value, after) => outcome = .returned (value == 0) after
  | (.borrowFailed, after) =>
    if args.profile.aborts then outcome = .terminated .borrowFailed
    else outcome = .unwound .borrowFailed after
  | (.malformed, _) => False

def dataIsEmptyContract : Solanalib.Contracts.Model AccountInfo.State Args Bool Panic Panic where
  requires := fun state args => ObservationReady .dataLen state args.info
  post := dataIsEmptyReference

theorem dataIsEmpty_holds : dataIsEmptyContract.Holds dataIsEmptyReference := by
  intro _ _ _ _ step
  exact step

theorem dataIsEmpty_exists (state : AccountInfo.State) (args : Args)
    (ready : ObservationReady .dataLen state args.info) :
    ∃ result, dataIsEmptyReference state args result := by
  have good := observe_not_malformed .dataLen state args.info ready
  cases step : observe .dataLen state args.info with
  | mk value after =>
    cases value with
    | malformed => simp [step] at good
    | value value => exact ⟨.returned (value == 0) after, by simp [dataIsEmptyReference, step]⟩
    | borrowFailed =>
      cases strategy : args.profile.aborts with
      | false => exact ⟨.unwound .borrowFailed after, by simp [dataIsEmptyReference, step,
        strategy]⟩
      | true => exact ⟨.terminated .borrowFailed, by simp [dataIsEmptyReference, step, strategy]⟩

/-- The serialized original-length header is immutable during resize. The
length word and spare bytes are mutable; spare bytes remain visible to a later
nonzeroing realloc. Current logical bytes stay in the existing data cell. -/
structure Buffer where
  originalLen : Nat
  serializedLen : Nat
  spare : _root_.Solanalib.Runtime.Bytes
  deriving DecidableEq, Repr

/-- Additional storage for owner assignment and loader-backed resize. Buffer
indices are data-cell identities, so all AccountInfo clones share the same
length word and backing. This extends, rather than replaces, the borrow world. -/
structure State where
  borrow : AccountInfo.State
  owners : List _root_.Solanalib.Runtime.Pubkey
  buffers : List (Option Buffer)
  deriving DecidableEq, Repr

def State.buffer (state : State) (handle : Borrow.Handle) : Option Buffer :=
  state.buffers[handle.cell]?.join

def State.owner (state : State) (reference : OwnerRef) : Option _root_.Solanalib.Runtime.Pubkey :=
  state.owners[reference.id]?

def assign (state : State) (args : AccountInfo.Value × _root_.Solanalib.Runtime.Pubkey) : Unit ×
  State :=
  ((), { state with owners := state.owners.set args.1.ownerRef.id args.2 })

/-- Assignment addresses owner storage directly and performs no RefCell
acquisition, signer check, writable check or runtime authorization check. -/
def assignContract : Solanalib.Contracts.Model State (AccountInfo.Value ×
  _root_.Solanalib.Runtime.Pubkey) Unit :=
  .returning (fun state args => args.1.ownerRef.id < state.owners.length)
    (fun before args _ after =>
      after = { before with owners := before.owners.set args.1.ownerRef.id args.2 } ∧
      after.owner args.1.ownerRef = some args.2)

theorem assign_realizes : assignContract.RealizedBy assign := by
  intro state args present
  exact ⟨rfl, by simpa [assign, State.owner] using
    (List.getElem?_set_self (a := args.2) present)⟩

/-- An alias reads the assigned current owner, even when its saved owner
observation differs. This says nothing about authorization to reassign it. -/
theorem assign_alias (state : State) (info alias : AccountInfo.Value) (owner :
  _root_.Solanalib.Runtime.Pubkey)
    (same : alias.ownerRef = info.ownerRef) (present : info.ownerRef.id < state.owners.length) :
    (assign state (info, owner)).2.owner alias.ownerRef = some owner := by
  rw [same]
  exact (assign_realizes state (info, owner) present).2

def sample : State := ⟨sampleState, [.zero], [none, some ⟨3, 3, [40, 50, 60]⟩]⟩

end Solanalib.Specs.Core.AccountInfoSdk
