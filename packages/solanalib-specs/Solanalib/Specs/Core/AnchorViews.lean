/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorAccount
public import Solanalib.Specs.Core.OwnedFocus
public import Solanalib.Specs.Core.BorrowFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorViews

/-- Anchor 0.27 owns its AccountInfo fields; the other reviewed releases keep
shared references. This changes reference identity and clone/drop dependencies. -/
inductive InfoStorage where
  | owned
  | borrowed
  deriving DecidableEq, Repr

/-- Common current wrapper contents. `account` reuses the decoded-value and
AccountInfo observations used by the construction models of Anchor. `infoIdentity`
identifies the referred-to AccountInfo object, not its lamports/data Rc cells.
The optional saved owner is present only for InterfaceAccount. Info-only
wrappers use Unit payload; Sysvar uses its decoded sysvar payload. -/
structure Wrapper (Payload : Type) where
  account : AnchorAccount.Account Payload
  infoIdentity : Nat
  savedOwner : Option Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- Wrapper objects and source loans use the common identified-cell protocol.
A retired owner has `none` contents; its identity is never reused. The leases
here describe Rust references, not the AccountInfo RefCell borrow counters. -/
abbrev Store (Payload : Type) := Borrow.State (Option (Wrapper Payload)) Unit

/-- The auxiliary component can include account cells, payload resources and
interior mutation. It is shared by all callbacks of one operation assignment. -/
abbrev World (Payload Aux : Type) := Store Payload × Aux

/-- A payload reference retains the exact parent loan and permission. It
contains no saved payload; dereference reads the current field of the wrapper. -/
structure PayloadRef where
  guard : Borrow.Guard
  mutable : Bool
  deriving DecidableEq, Repr

/-- Distinguish an owned wrapper field from an independently referred-to
AccountInfo object. Two wrappers may share the latter without being aliases
of one another or sharing their decoded payload fields. -/
inductive InfoLocation where
  | field (wrapper : Borrow.Handle)
  | external (identity : Nat)
  deriving DecidableEq, Repr

/-- A shared AccountInfo reference, bounded by its parent source loan. -/
structure InfoRef where
  guard : Borrow.Guard
  location : InfoLocation
  deriving DecidableEq, Repr

/-- An actual callback receives the source reference as well as its readable
contents. Pointer identity must not be erased by passing only a value snapshot. -/
structure PayloadArg (Payload : Type) where
  reference : PayloadRef
  location : Borrow.Handle
  value : Payload
  deriving DecidableEq, Repr

/-- The generic sysvar decoder sees the original AccountInfo object. Its
address is independent of the Rc aliases stored inside that object. -/
structure InfoArg where
  reference : InfoRef
  value : AccountInfo.Value
  deriving DecidableEq, Repr

variable {Payload Aux : Type}

/-- Resolve the still-live parent token and read the current wrapper. -/
def current (store : Store Payload) (guard : Borrow.Guard) : Option (Wrapper Payload) :=
  match Borrow.current store guard with
  | .ok (_, value) => value
  | .error _ => none

/-- The location of the payload field is the current parent wrapper identity.
Different live loans to the same object therefore denote the same field. -/
def payloadLocation (store : Store Payload) (reference : PayloadRef) : Option Borrow.Handle :=
  (store.resolve reference.guard).map Borrow.Slot.cell

/-- The actual current payload, read through the still-live parent loan. -/
def readPayload (store : Store Payload) (reference : PayloadRef) : Option Payload :=
  (current store reference.guard).map fun wrapper => wrapper.account.value

/-- The returned info pointer targets either the owned field of this wrapper or
the exact AccountInfo object stored by shared reference in later releases. -/
def infoLocation (storage : InfoStorage) (store : Store Payload)
    (guard : Borrow.Guard) (wrapper : Wrapper Payload) : Option InfoLocation :=
  match storage with
  | .owned => (store.resolve guard).map fun slot => .field slot.cell
  | .borrowed => some (.external wrapper.infoIdentity)

/-- Observe an AccountInfo reference only while its original loan and its
recorded target remain current. Its lamports/data handles retain account aliases. -/
def readInfo (storage : InfoStorage) (store : Store Payload)
    (reference : InfoRef) : Option AccountInfo.Value := do
  let wrapper ← current store reference.guard
  let location ← infoLocation storage store reference.guard wrapper
  if location = reference.location then some wrapper.account.info else none

/-- A current wrapper suffices for a shared field operation. No source layout,
owner, signer, writable or serialization premise is used by that mathematics. -/
def Readable (store : Store Payload) (guard : Borrow.Guard) : Prop :=
  ∃ wrapper, current store guard = some wrapper

/-- A mutable field operation additionally needs the exclusive loan of the caller.
This does not require AccountInfo.is_writable: only anchor-debug checks it. -/
def Writable (store : Store Payload) (guard : Borrow.Guard) : Prop :=
  Readable store guard ∧ ∃ slot, store.resolve guard = some slot ∧ slot.mode = .exclusive

/-- The local field projection allocates no loan and does not copy the field. -/
def payloadReference (mutable : Bool) (before : World Payload Aux) (guard : Borrow.Guard) :
    PayloadRef × World Payload Aux := (⟨guard, mutable⟩, before)

/-- The pointer fallback has no admitted source input; shared reference
contracts require a live wrapper and consequently resolve its actual target. -/
def infoReference (storage : InfoStorage) (before : World Payload Aux) (guard : Borrow.Guard) :
    InfoRef × World Payload Aux :=
  let location := (current before.1 guard).bind (infoLocation storage before.1 guard)
  (⟨guard, location.getD (.external 0)⟩, before)

/-- Key copies the key value and preserves the complete wrapper/loan world. -/
def keyReference (before : World Payload Aux) (guard : Borrow.Guard) :
    Solanalib.Runtime.Pubkey × World Payload Aux :=
  (((current before.1 guard).map fun wrapper => wrapper.account.info.key).getD .zero, before)

/-- Updating a decoded payload preserves its AccountInfo and saved owner.
This helper represents an already authorized field store, not T::drop. -/
def Wrapper.withPayload (wrapper : Wrapper Payload) (payload : Payload) : Wrapper Payload :=
  { wrapper with account := { wrapper.account with value := payload } }

/-- A store through a mutable result uses the same exclusive parent loan and
updates the actual current field. Shared references cannot perform this store. -/
def writePayload (before : Store Payload) (reference : PayloadRef) (payload : Payload) :
    Except Borrow.Error Unit × Store Payload :=
  if reference.mutable then
    match current before reference.guard with
    | none => (.error .invalidGuard, before)
    | some wrapper => Borrow.write before reference.guard (some (wrapper.withPayload payload))
  else (.error .wrongMode, before)

/-- The field view never manufactures a new acquisition or consumes its
parent token. Lifetime closure uses the existing common Borrow.release. -/
theorem payloadReference_identity (mutable : Bool) (before : World Payload Aux)
    (guard : Borrow.Guard) :
    (payloadReference mutable before guard).1.guard = guard ∧
      (payloadReference mutable before guard).2 = before := ⟨rfl, rfl⟩

/-- Shared payload references cannot mutate, independently of the mode of their parent
loan. A shared reborrow of an exclusive receiver stays shared. -/
theorem writePayload_shared (before : Store Payload) (guard : Borrow.Guard) (payload : Payload) :
    writePayload before ⟨guard, false⟩ payload = (.error .wrongMode, before) := rfl

/-- Key reads the key of the selected wrapper, including keys that alias an
AccountInfo reached from some other wrapper. It is a copy, not a new key owner. -/
theorem keyReference_current (before : World Payload Aux) (guard : Borrow.Guard)
    (wrapper : Wrapper Payload) (present : current before.1 guard = some wrapper) :
    keyReference before guard = (wrapper.account.info.key, before) := by
  simp [keyReference, present]

/-- A borrowed AccountInfo field preserves the exact external object identity. -/
theorem infoReference_borrowed (before : World Payload Aux) (guard : Borrow.Guard)
    (wrapper : Wrapper Payload) (present : current before.1 guard = some wrapper) :
    infoReference .borrowed before guard = (⟨guard, .external wrapper.infoIdentity⟩, before) := by
  simp [infoReference, present, infoLocation]

end Solanalib.Specs.Core.AnchorViews
