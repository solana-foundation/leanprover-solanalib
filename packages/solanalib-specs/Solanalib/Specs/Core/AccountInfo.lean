/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Borrow
public import Solanalib.Specs.Core.ProgramError
public import Solanalib.Specs.Core

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountInfo

/-- The independently borrowed contents of the two `Rc<RefCell<_>>` fields.
Balances are bounded `u64` values; data remains an ordered byte list. -/
inductive Content where
  | lamports (value : UInt64)
  | data (bytes : _root_.Solanalib.Runtime.Bytes)
  deriving DecidableEq, Repr

/-- A guard carries a checked projection descriptor, not a snapshot. A byte
range can later support the mapped data guard of Anchor. -/
inductive View where
  | whole
  | bytesRange (offset length : Nat)
  deriving DecidableEq, Repr

/-- All AccountInfo aliases live in the same identified-cell world. -/
abbrev State := Borrow.State Content View

/-- Identity of the referenced owner storage. This ghost identity is not a
machine address; equal observed keys need not designate the same storage. -/
structure OwnerRef where
  id : Nat
  deriving DecidableEq, Repr

/-- A binding reads the current owner from its mutable auxiliary world. In
particular, an `assign` performed by a callback can change later observations. -/
abbrev OwnerAt (Aux : Type) := Aux → OwnerRef → _root_.Solanalib.Runtime.Pubkey

/-- A mathematical AccountInfo value. Clones preserve cell and owner-reference
identities. `owner` records an entry observation, not an immutable pointed value:
after callbacks, source owner reads use `OwnerAt` and `ownerRef`. The deprecated
placeholder is retained as uninterpreted data. -/
structure Value where
  key : _root_.Solanalib.Runtime.Pubkey
  lamports : Borrow.Handle
  data : Borrow.Handle
  owner : _root_.Solanalib.Runtime.Pubkey
  unused : UInt64
  isSigner : Bool
  isWritable : Bool
  executable : Bool
  ownerRef : OwnerRef
  deriving DecidableEq, Repr

/-- A binding chooses the pointer-sized RefCell counter and panic
strategy of its target. Selecting Solana source cfgs alone does not establish this width. -/
structure Profile where
  wordBits : Nat
  aborts : Bool
  deriving DecidableEq, Repr

/-- The checked policy is `isize::MAX`, rather than the byte limit of AccountView. -/
def Profile.policy (profile : Profile) : Borrow.Policy := .refCell profile.wordBits

/-- A valid model value has two distinct typed cells with the policies of the target,
a representable data length, and a valid common guard world. -/
def Valid (profile : Profile) (state : State) (info : Value) : Prop :=
  2 ≤ profile.wordBits ∧ state.Valid ∧ info.lamports ≠ info.data ∧
  (∃ balance, state.lookupCell info.lamports = some ⟨.lamports balance, profile.policy⟩) ∧
  (∃ bytes, state.lookupCell info.data = some ⟨.data bytes, profile.policy⟩ ∧
    bytes.length < 2^profile.wordBits)

/-- The account and explicit target binding supplied to each borrow operation. -/
structure Args where
  profile : Profile
  info : Value
  deriving DecidableEq, Repr

/-- Cloning adds an alias to the existing cells and owner reference; it does not
copy pointed contents or acquire a lease. Its recorded owner observation is not
a claim that the referenced owner remains unchanged. -/
def clone (info : Value) : Value := info

/-- The checked borrow error callback of AccountInfo discards the diagnostic of RefCell. -/
def borrowError (_ : Borrow.Error) : ProgramError.Value := .accountBorrowFailed

/-- Common checked acquisition for either of the cells of AccountInfo. There is no
metadata writability check, including for an exclusive borrow. -/
def tryBorrow (mode : Borrow.Mode) (handle : Borrow.Handle) (state : State) :
    Except ProgramError.Value Borrow.Guard × State :=
  let (result, after) := Borrow.acquire state handle mode .whole
  (result.mapError borrowError, after)

/-- Checked shared data borrowing returns an identified live guard. -/
def tryBorrowData (state : State) (args : Args) := tryBorrow .shared args.info.data state

/-- Checked mutable data borrowing consults only the live leases of the data cell. -/
def tryBorrowMutData (state : State) (args : Args) := tryBorrow .exclusive args.info.data state

/-- Getter selection also determines which independent cell is borrowed. -/
inductive Observation where
  | lamports
  | dataLen
  deriving DecidableEq, Repr

def Observation.handle (observation : Observation) (info : Value) : Borrow.Handle :=
  match observation with
  | .lamports => info.lamports
  | .dataLen => info.data

/-- Typed projection of the current contents. `none` is a malformed model
representation, excluded by the validity requirement of the versioned contract. -/
def Observation.project (observation : Observation) : Content → Option Nat
  | .lamports value => match observation with | .lamports => some value.toNat | _ => none
  | .data bytes => match observation with | .dataLen => some bytes.length | _ => none

/-- A successful getter acquires and releases a temporary shared guard. The
tombstone is ghost history, preserving the non-reuse of prior guard identities.
Malformed model paths are separate from source borrow panics. -/
inductive ReadResult where
  | value (value : Nat)
  | borrowFailed
  | malformed
  deriving DecidableEq, Repr

def observe (observation : Observation) (state : State) (info : Value) : ReadResult × State :=
  let (borrowed, during) := Borrow.acquire state (observation.handle info) .shared .whole
  match borrowed with
  | .error .missingCell | .error .invalidGuard | .error .wrongMode => (.malformed, state)
  | .error .conflict | .error .sharedLimit => (.borrowFailed, state)
  | .ok guard =>
    match Borrow.current during guard with
    | .error _ => (.malformed, during)
    | .ok (_, content) =>
      match observation.project content with
      | none => (.malformed, during)
      | some value =>
        let (released, after) := Borrow.release during guard
        match released with
        | .error _ => (.malformed, after)
        | .ok () => (.value value, after)

/-- The only source-level failure of these getters is the borrow panic of RefCell.
The reason carries no fabricated ProgramError return. -/
inductive Panic where
  | borrowFailed
  deriving DecidableEq, Repr

/-- Getter outcomes expose both panic strategies and their actual modeled
state. Malformed model representations admit no finite outcome. -/
def observePost (observation : Observation) (state : State) (args : Args)
    (outcome : Outcome State Nat Panic Panic) : Prop :=
  match observe observation state args.info with
  | (.malformed, _) => False
  | (.value value, after) => outcome = .returned value after
  | (.borrowFailed, after) =>
    if args.profile.aborts then outcome = .terminated .borrowFailed
    else outcome = .unwound .borrowFailed after

/-- Reference relation computes acquisition, current data and guard release. -/
def observeReference (observation : Observation) (state : State) (args : Args) :
    Outcome State Nat Panic Panic → Prop := observePost observation state args

/-- Interpret a mapped data guard against the current byte contents of the cell.
No buffer, owner, discriminator or cast condition is invented by this projection. -/
def projectBytes (view : View) : Content → Except Unit _root_.Solanalib.Runtime.Bytes
  | .lamports _ => .error ()
  | .data bytes => match view with
    | .whole => .ok bytes
    | .bytesRange offset length =>
      if offset + length ≤ bytes.length then .ok ((bytes.drop offset).take length)
      else .error ()

/-- A small free world used by the closed witnesses and composition tests.
This is a mathematical fixture, not a claimed Rust allocation. -/
def sampleProfile : Profile := ⟨64, false⟩

def sampleInfo : Value := ⟨.zero, ⟨0⟩, ⟨1⟩, .zero, 0, false, false, false, ⟨0⟩⟩

def sampleState : State :=
  ⟨[⟨.lamports 40, sampleProfile.policy⟩, ⟨.data [10, 20, 30], sampleProfile.policy⟩], []⟩

def sampleArgs : Args := ⟨sampleProfile, sampleInfo⟩

theorem sample_valid : Valid sampleProfile sampleState sampleInfo := by
  refine ⟨by decide, ?_, by decide, ⟨40, rfl⟩, ⟨[10, 20, 30], rfl, by decide⟩⟩
  constructor
  · intro id slot found
    simp [Borrow.State.lookupSlot, sampleState] at found
  · intro handle cell found
    simp only [Borrow.State.exclusiveCount, Borrow.State.sharedCount, Borrow.State.count,
      sampleState, List.countP_nil]
    exact ⟨by decide, by decide, Nat.zero_le _⟩

end Solanalib.Specs.Core.AccountInfo
