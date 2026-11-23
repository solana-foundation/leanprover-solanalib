/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorrowMapLaws
public import Solanalib.Specs.Core.FieldReference
public import Solanalib.Specs.Core.ProgramError
public import Solanalib.Runtime.Account

/-!
The two independently leased account fields of Pinocchio. An AccountInfo is an alias
of a header; that header identifies one lamports cell and one data cell. Each
cell has seven shared leases. Physical data past the logical length is retained,
so shrinking and later growing cannot resurrect stale bytes.

This is the 0.9 account format, not the one-byte, data-only protocol of AccountView.
Source offsets, integer representation and permissions are separate bindings.
-/

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.PinocchioAccount

abbrev Handle := Borrow.Handle
abbrev Guard := Borrow.Guard
abbrev Mode := Borrow.Mode

/-- The two independently borrowed fields in the same raw account. -/
inductive Field where
  | lamports
  | data
  deriving DecidableEq, Repr

/-- Current data, its hidden allocation tail, and the signed resize counter. -/
structure Data where
  backing : Solanalib.Runtime.Bytes
  dataLen : Nat
  entryLen : Nat
  resizeDelta : Int
  deriving DecidableEq, Repr

def Data.empty : Data := ⟨[], 0, 0, 0⟩
def Data.bytes (data : Data) : Solanalib.Runtime.Bytes := data.backing.take data.dataLen

/-- A resize preserves the allocation and hidden suffix; growth clears exactly
the newly exposed bytes, even after a preceding shrink. -/
def Data.resize (data : Data) (newLen : Nat) : Data :=
  { data with
    dataLen := newLen
    resizeDelta := data.resizeDelta + ((newLen : Int) - data.dataLen)
    backing := if data.dataLen < newLen then
      Solanalib.Runtime.writeAt data.backing data.dataLen (List.replicate (newLen - data.dataLen) 0)
    else data.backing }

/-- An independent cell is either the lamports word or account data. -/
inductive Content where
  | lamports (value : UInt64)
  | data (value : Data)
  deriving DecidableEq, Repr

/-- Ordinary guards select the entire field or an in-field byte range. Generic
mapped Rust targets are interpreted by the separate guard profile. -/
inductive View where
  | whole
  | bytes (offset length : Nat)
  deriving DecidableEq, Repr

/-- Raw flags retain noncanonical nonzero values. Header identity, rather than
key equality, determines AccountInfo aliasing. -/
structure Header where
  key : Solanalib.Runtime.Pubkey
  owner : Solanalib.Runtime.Pubkey
  isSigner : UInt8
  isWritable : UInt8
  executable : UInt8
  lamports : Handle
  data : Handle
  deriving DecidableEq, Repr

def Header.empty : Header := ⟨.zero, .zero, 0, 0, 0, ⟨0⟩, ⟨0⟩⟩
def Header.field (header : Header) : Field → Handle
  | .lamports => header.lamports
  | .data => header.data

/-- The header table and both field stores are shared by every alias. -/
abbrev State := Borrow.State Content View × List Header

def State.empty : State := (Borrow.State.empty, [])
def State.lookup (state : State) (handle : Handle) : Option Header := state.2[handle.cell]?
def State.header (state : State) (handle : Handle) : Header :=
  (state.lookup handle).getD Header.empty
def State.field (state : State) (handle : Handle) (field : Field) : Handle :=
  (state.header handle).field field
def State.content (state : State) (handle : Handle) (field : Field) : Option Content :=
  (state.1.lookupCell (state.field handle field)).map Borrow.Cell.value

/-- Values copied from one unique loader record before creating aliases. -/
structure Input where
  key : Solanalib.Runtime.Pubkey
  owner : Solanalib.Runtime.Pubkey
  isSigner : UInt8
  isWritable : UInt8
  executable : UInt8
  lamports : UInt64
  data : Data
  deriving DecidableEq, Repr

def policy : Borrow.Policy := ⟨7⟩

/-- Allocate one header and two independent field cells. Duplicates reuse the
returned handle, without inserting another header or resetting either lease. -/
def State.insert (state : State) (input : Input) : Handle × State :=
  let balance := state.1.insert policy (.lamports input.lamports)
  let data := balance.2.insert policy (.data input.data)
  let header := Header.mk input.key input.owner input.isSigner input.isWritable
    input.executable balance.1 data.1
  (⟨state.2.length⟩, (data.2, state.2 ++ [header]))

/-- A field exists in the selected header and its identified store. -/
def FieldPresent (state : State) (handle : Handle) (field : Field) : Prop :=
  ∃ header cell, state.lookup handle = some header ∧
    state.1.lookupCell (header.field field) = some cell

def State.lamports (state : State) (handle : Handle) : UInt64 :=
  match state.content handle .lamports with | some (.lamports value) => value | _ => 0
def State.data (state : State) (handle : Handle) : Data :=
  match state.content handle .data with | some (.data value) => value | _ => Data.empty

/-- The source nibble counts remaining shared slots. Exclusive acquisition
clears bit 3 while leaving the seven shared slots available for later release. -/
def borrowNibble {Target : Type} (store : Borrow.State Content Target) (handle : Handle) : Nat :=
  (if store.exclusiveCount handle = 0 then 8 else 0) + (7 - store.sharedCount handle)

/-- Data uses the low nibble; lamports uses the high nibble. -/
def borrowByte (state : State) (handle : Handle) : Nat :=
  16 * borrowNibble state.1 (state.field handle .lamports) +
    borrowNibble state.1 (state.field handle .data)

/-- Exact local borrow admission: data and balance never block each other. -/
def available (state : State) (handle : Handle) (field : Field) (mode : Mode) : Bool :=
  let selected := state.field handle field
  match mode with
  | .shared => decide (state.1.exclusiveCount selected = 0 ∧ state.1.sharedCount selected < 7)
  | .exclusive => decide (state.1.exclusiveCount selected = 0 ∧ state.1.sharedCount selected = 0)

/-- The fixed seven-slot protocol issues the common identified guard on
success. No writable/signer/owner check is made by these local SDK methods. -/
def acquire (field : Field) (mode : Mode) (state : State) (handle : Handle) :
    Except ProgramError.Value Guard × State :=
  if available state handle field mode then
    let issued := state.1.issue (state.field handle field) mode .whole
    (.ok issued.1, (issued.2, state.2))
  else (.error .accountBorrowFailed, state)

/-- Successful acquisition exposes the exact cell and mode; failure preserves
the entire world and reports AccountBorrowFailed. -/
def borrowContract (field : Field) (mode : Mode) :
    Solanalib.Contracts.Model State Handle (Except ProgramError.Value Guard) :=
  .returning (fun before handle => FieldPresent before handle field)
    (fun before handle result after =>
      if available before handle field mode then
        ∃ guard content,
          result = .ok guard ∧
          (guard, after.1) = before.1.issue (before.field handle field) mode .whole ∧
          after.2 = before.2 ∧
          after.1.resolve guard = some ⟨before.field handle field, mode, 0, .whole⟩ ∧
          Borrow.current after.1 guard = .ok (.whole, content)
      else result = .error .accountBorrowFailed ∧ after = before)

theorem borrow_reference (field : Field) (mode : Mode) :
    (borrowContract field mode).RealizedBy (acquire field mode) := by
  intro before handle ready
  obtain ⟨header, cell, headerAt, cellAt⟩ := ready
  have selected : before.field handle field = header.field field := by
    simp [State.field, State.header, headerAt]
  have current := Borrow.State.issue_resolves before.1 (before.field handle field) mode View.whole
  by_cases can : available before handle field mode = true
  · simp only [borrowContract, Solanalib.Contracts.Model.ensures,
    Solanalib.Contracts.Model.returning,
      acquire, can, ↓reduceIte]
    refine ⟨_, cell.value, by trivial, by trivial, by trivial, current, ?_⟩
    change Borrow.current (before.1.issue (before.field handle field) mode .whole).2
      (before.1.issue (before.field handle field) mode .whole).1 = .ok (.whole, cell.value)
    unfold Borrow.current
    rw [current]
    have cellAt' : before.1.cells[(header.field field).cell]? = some cell := cellAt
    simp only [Borrow.State.issue, Borrow.State.lookupCell, selected, cellAt']
  · simp [borrowContract, acquire, can]

/-- A field reference keeps the account identity and selects the current key
or owner on a later read. It is not a key snapshot or a new lease. -/
inductive PubkeyField where
  | key
  | owner
  deriving DecidableEq, Repr

abbrev PubkeyRef := FieldReference Handle PubkeyField
def PubkeyRef.read (reference : PubkeyRef) (state : State) : Option Solanalib.Runtime.Pubkey :=
  (state.lookup reference.parent).map fun header =>
    match reference.field with | .key => header.key | .owner => header.owner

def keyRef (handle : Handle) : PubkeyRef := ⟨handle, .key⟩
def ownerRef (handle : Handle) : PubkeyRef := ⟨handle, .owner⟩

def sampleInput : Input := ⟨.zero, .zero, 2, 3, 0, 40, ⟨[10, 20, 30, 90, 91], 3, 3, 0⟩⟩
def sampleHandle : Handle := ⟨0⟩
def sampleState : State := (State.empty.insert sampleInput).2

theorem sample_fieldPresent (field : Field) : FieldPresent sampleState sampleHandle field := by
  cases field <;> exact ⟨_, _, rfl, rfl⟩

theorem borrow_satisfiable (field : Field) (mode : Mode) :
    (borrowContract field mode).Satisfiable :=
  ⟨sampleState, sampleHandle, sample_fieldPresent field⟩

def headerContract {Value : Type} (project : Header → Value) :
    Solanalib.Contracts.Model State Handle Value :=
  .returning (fun before handle => ∃ header, before.lookup handle = some header)
    (fun before handle value after => after = before ∧
      ∃ header, before.lookup handle = some header ∧ value = project header)
def headerRun {Value : Type} (project : Header → Value) (state : State) (handle : Handle) :
    Value × State := (project (state.header handle), state)
theorem header_reference {Value : Type} (project : Header → Value) :
    (headerContract project).RealizedBy (headerRun project) := by
  rintro before handle ⟨header, found⟩
  exact ⟨rfl, header, found, by simp [headerRun, State.header, found]⟩
theorem header_satisfiable {Value : Type} (project : Header → Value) :
    (headerContract project).Satisfiable := ⟨sampleState, sampleHandle, _, rfl⟩


end Solanalib.Specs.Core.PinocchioAccount
