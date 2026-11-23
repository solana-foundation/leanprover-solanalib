/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.StoreOps
public import Solanalib.Specs.Core.Outcome

/-!
Pure identified cells and guard tokens. Identities are mathematical indices, not physical
pointers or Rust permissions. Cell contents remain current while guards are live. The stable
identity of a guard names one lease; its generation identifies the currently usable token.
Mapping advances that generation, and release leaves a tombstone, so an old token is not revived
by a later acquisition.

The view parameter is a projection descriptor supplied by the surrounding model. This module
does not guess what bytes or typed value a descriptor denotes. Direct cell replacements also
require the operation-specific authorization and footprint rules of the adapter. `Borrow` reuses
`Solanalib.Runtime.Lease` as an observation without redefining it. Shared limits are per-cell
policy, rather than a universal SDK bound. -/

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borrow

universe u v w x

/-- A mathematical cell identity; equal handles are aliases. -/
structure Handle where
  /-- Stable index into the finite cell table. -/
  cell : Nat
  deriving DecidableEq, Repr

/-- Clone an alias without creating a cell or a lease. -/
def Handle.alias (handle : Handle) : Handle := handle

/-- The stable identity of one acquisition and the currently usable generation.
These ghost identifiers do not supply a physical-pointer validity claim. -/
structure Guard where
  /-- Stable index allocated for exactly one acquisition. -/
  id : Nat
  /-- Current move generation; this mathematical counter does not wrap. -/
  generation : Nat
  deriving DecidableEq, Repr

/-- A live lease grants shared observation or exclusive guarded mutation. -/
inductive Mode where
  /-- A shared lease, counted against the shared limit of the cell. -/
  | shared
  /-- An exclusive lease, incompatible with every other lease on this cell. -/
  | exclusive
  deriving DecidableEq, Repr

/-- The finite shared-acquisition bound of an interface. Zero is a meaningful policy. -/
structure Policy where
  /-- Maximum simultaneous shared acquisitions on one cell. -/
  sharedLimit : Nat
  deriving DecidableEq, Repr

/-- The AccountView borrow-byte policy, agreeing with the canonical model. -/
def Policy.accountView : Policy := ⟨254⟩

/-- A signed-counter policy at an explicitly chosen width. This is mathematics;
an adapter must bind the width to the RefCell representation of its supported target. -/
def Policy.refCell (bits : Nat) : Policy := ⟨2^(bits - 1) - 1⟩

/-- Current contents and the fixed acquisition policy of an identified cell. -/
structure Cell (Content : Type u) where
  /-- Current contents, including changes made while a guard is live. -/
  value : Content
  /-- The fixed acquisition bound for this cell identity. -/
  policy : Policy
  deriving DecidableEq, Repr

/-- The live record of a guard. Its cell and mode remain fixed during mapping. -/
structure Slot (View : Type v) where
  /-- The underlying leased cell, preserved by a guard transfer. -/
  cell : Handle
  /-- The shared or exclusive mode of the acquisition, preserved by transfer. -/
  mode : Mode
  /-- The only token generation currently accepted for this guard identity. -/
  generation : Nat
  /-- The current target descriptor of the adapter; validity is a separate obligation. -/
  view : View
  deriving DecidableEq, Repr

/-- Finite cells and an append-only identity space for guards. A released guard
leaves `none`; acquisition never reuses that index. -/
structure State (Content : Type u) (View : Type v) where
  /-- Finite identified cells; insertion appends without moving existing identities. -/
  cells : List (Cell Content)
  /-- Guard records and permanent release tombstones. -/
  slots : List (Option (Slot View))
  deriving DecidableEq, Repr

/-- Checked failures of this mathematical protocol. Versioned APIs translate
these into their own errors or panics and exclude malformed handles as needed. -/
inductive Error where
  /-- The supplied cell handle is absent from the finite cell table. -/
  | missingCell
  /-- The guard is unissued, released, or from a consumed generation. -/
  | invalidGuard
  /-- Existing live leases conflict with the requested acquisition mode. -/
  | conflict
  /-- The shared-acquisition count has reached the policy limit of this cell. -/
  | sharedLimit
  /-- Guarded mutation was requested through a shared guard. -/
  | wrongMode
  deriving DecidableEq, Repr

variable {Content : Type u} {View : Type v} {Failure : Type w} {Value : Type x}

/-- An empty finite world. -/
def State.empty : State Content View := ⟨[], []⟩

/-- Find a cell by its stable identity. -/
def State.lookupCell (state : State Content View) (handle : Handle) : Option (Cell Content) :=
  state.cells[handle.cell]?

/-- Find the live record at a stable guard identity; tombstones return `none`. -/
def State.lookupSlot (state : State Content View) (id : Nat) : Option (Slot View) :=
  state.slots[id]?.bind fun entry => entry

/-- A guard token is live only at its current recorded generation. -/
def State.resolve (state : State Content View) (guard : Guard) : Option (Slot View) :=
  (state.lookupSlot guard.id).bind fun slot =>
    if slot.generation = guard.generation then some slot else none

/-- Count actual live slots for this cell and mode. -/
def State.count (state : State Content View) (handle : Handle) (mode : Mode) : Nat :=
  state.slots.countP fun entry => match entry with
    | none => false
    | some slot => decide (slot.cell = handle ∧ slot.mode = mode)

/-- The current number of distinct shared leases. -/
def State.sharedCount (state : State Content View) (handle : Handle) : Nat :=
  state.count handle .shared

/-- The current number of exclusive leases; validity bounds this by one. -/
def State.exclusiveCount (state : State Content View) (handle : Handle) : Nat :=
  state.count handle .exclusive

/-- The canonical lease observation derived from live guard records. -/
def State.lease (state : State Content View) (handle : Handle) : Solanalib.Runtime.Lease :=
  if state.exclusiveCount handle = 0 then
    match state.sharedCount handle with
    | 0 => .free
    | n + 1 => .shared (n + 1)
  else .exclusive

/-- Every live guard refers to an existing cell. Shared and exclusive leases
exclude one another, and every cell obeys its own shared bound. -/
def State.Valid (state : State Content View) : Prop :=
  (∀ id slot, state.lookupSlot id = some slot →
    ∃ cell, state.lookupCell slot.cell = some cell) ∧
  (∀ handle cell, state.lookupCell handle = some cell →
    state.exclusiveCount handle ≤ 1 ∧
    (state.exclusiveCount handle = 1 → state.sharedCount handle = 0) ∧
    state.sharedCount handle ≤ cell.policy.sharedLimit)

/-- Add a fresh cell identity without changing any existing identity or guard. -/
def State.insert (state : State Content View) (policy : Policy) (value : Content) :
    Handle × State Content View :=
  (⟨state.cells.length⟩, { state with cells := state.cells ++ [⟨value, policy⟩] })

/-- Change the current contents of one cell, preserving its policy and all guards.
This primitive does not confer permission: callers supply the authorization and footprint conditions
of the direct operation, such as an AccountView header update. -/
def replaceCell (state : State Content View) (handle : Handle) (value : Content) :
    Except Error Unit × State Content View :=
  match state.lookupCell handle with
  | none => (.error .missingCell, state)
  | some cell => (.ok (),
      { state with cells := state.cells.set handle.cell { cell with value := value } })

/-- A direct cell update with the same explicit adapter obligations as replacement. -/
def modifyCell (state : State Content View) (handle : Handle) (update : Content → Content) :
    Except Error Unit × State Content View :=
  match state.lookupCell handle with
  | none => (.error .missingCell, state)
  | some cell => replaceCell state handle (update cell.value)

/-- Append one fresh lease record. Acquisition checks the policy before using this. -/
def State.issue (state : State Content View) (handle : Handle) (mode : Mode) (view : View) :
    Guard × State Content View :=
  (⟨state.slots.length, 0⟩,
    { state with slots := state.slots ++ [some ⟨handle, mode, 0, view⟩] })

/-- Shared acquisition checks conflict before saturation; exclusive acquisition
requires no live lease. Neither mode checks the writable metadata of an account. -/
def acquire (state : State Content View) (handle : Handle) (mode : Mode) (view : View) :
    Except Error Guard × State Content View :=
  match state.lookupCell handle with
  | none => (.error .missingCell, state)
  | some cell =>
    match mode with
    | .shared =>
      if state.exclusiveCount handle ≠ 0 then (.error .conflict, state)
      else if cell.policy.sharedLimit ≤ state.sharedCount handle then
        (.error .sharedLimit, state)
      else let (guard, after) := state.issue handle .shared view
        (.ok guard, after)
    | .exclusive =>
      if state.exclusiveCount handle ≠ 0 ∨ state.sharedCount handle ≠ 0 then
        (.error .conflict, state)
      else let (guard, after) := state.issue handle .exclusive view
        (.ok guard, after)

/-- Current contents together with the actual projection descriptor of the live guard.
The cell value is read now, not copied into the guard at acquisition. -/
def current (state : State Content View) (guard : Guard) : Except Error (View × Content) :=
  match state.resolve guard with
  | none => .error .invalidGuard
  | some slot => match state.lookupCell slot.cell with
    | none => .error .missingCell
    | some cell => .ok (slot.view, cell.value)

/-- Interpret the recorded projection against current contents. Projection errors
remain distinct from invalid/consumed guard errors; this operation changes no state. -/
def deref (project : View → Content → Except Failure Value)
    (state : State Content View) (guard : Guard) :
    Except Error (Except Failure Value) × State Content View :=
  (match current state guard with
    | .error error => .error error
    | .ok (view, content) => .ok (project view content), state)

/-- An exclusive guarded write changes the cell immediately, retaining the lease
and descriptor. The adapter restricts it to the denoted footprint of the descriptor. -/
def write (state : State Content View) (guard : Guard) (value : Content) :
    Except Error Unit × State Content View :=
  match state.resolve guard with
  | none => (.error .invalidGuard, state)
  | some slot =>
    if slot.mode = .exclusive then replaceCell state slot.cell value
    else (.error .wrongMode, state)

/-- Release consumes the current token. No copy-back occurs: writes have already
changed the current cell. A second release or subsequent dereference fails. -/
def release (state : State Content View) (guard : Guard) :
    Except Error Unit × State Content View :=
  match state.resolve guard with
  | none => (.error .invalidGuard, state)
  | some _ => (.ok (), { state with slots := state.slots.set guard.id none })

/-- Move a guard into a new projection, retaining its stable lease identity and
mode while consuming its input generation. Callback mapping invokes this only
after accounting for the effects and projection conditions of the callback. -/
def transfer (state : State Content View) (guard : Guard) (view : View) :
    Except Error Guard × State Content View :=
  match state.resolve guard with
  | none => (.error .invalidGuard, state)
  | some slot =>
    (.ok ⟨guard.id, guard.generation + 1⟩,
      { state with
        slots := state.slots.set guard.id
          (some { slot with generation := guard.generation + 1, view := view }) })

end Solanalib.Specs.Core.Borrow
