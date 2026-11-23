/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.FieldReference
public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.LegacyStake
public import Solanalib.Specs.Core.TokenState

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport

/-- The three distinct tuple-wrapper source types. Stake uses the legacy
four-variant state, without the later StakeStateV2 flags byte. -/
inductive Wrapper where
  | stakeAccount
  | tokenAccount
  | interfaceTokenAccount
  deriving DecidableEq, Repr

/-- The complete pointee, including all token option fields and stake float
bits. A dereference neither deserializes nor validates these values. -/
def Wrapper.Pointee : Wrapper → Type
  | .stakeAccount => LegacyStake.State
  | .tokenAccount | .interfaceTokenAccount => Token.Account

/-- A wrapper dereference starts from an existing live source reference.
Parent identities and their current contents remain supplied by that borrow;
no guard, allocation, or value snapshot is manufactured by the projection. -/
structure DerefIndex (wrapper : Wrapper) where
  State : Type
  Parent : Type
  access : FieldReference.Access State Parent wrapper.Pointee

/-- All three wrappers select their single tuple field. -/
abbrev DerefResult {wrapper : Wrapper} (index : DerefIndex wrapper) :=
  FieldReference index.Parent Unit

/-- Form the reference to tuple field zero and retain the exact parent. -/
def deref {wrapper : Wrapper} (index : DerefIndex wrapper)
    (before : index.State) (parent : index.Parent) : DerefResult index × index.State :=
  (⟨parent, ()⟩, before)

/-- The complete field-reference contract. The existing parent must be
readable now; the result follows that parent in every later permitted state. -/
def derefFamily (wrapper : Wrapper) : Family where
  Index := DerefIndex wrapper
  State := DerefIndex.State
  Args := DerefIndex.Parent
  Value := DerefResult
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun index => .returning
    (fun before parent => ∃ value, index.access.Reads before parent value)
    (fun before parent reference after => reference = ⟨parent, ()⟩ ∧ after = before)

/-- Mathematical reference formation, independent of a Rust implementation. -/
def derefRun (wrapper : Wrapper) : FamilyRun (derefFamily wrapper) :=
  fun index => returnsOf (deref index)

/-- Every admitted parent produces the same field reference without changing
the state. The proof retains the arbitrary source-reference interpretation. -/
theorem deref_reference (wrapper : Wrapper) :
    FamilyReference (derefFamily wrapper) (derefRun wrapper) := by
  intro index
  apply (realized_iff_holds _ _).mp
  intro before parent _
  exact ⟨rfl, rfl⟩

/-- A later read uses the current parent value in that later state, not the
contents that happened to be present when deref was called. -/
theorem deref_reads_current {wrapper : Wrapper} (index : DerefIndex wrapper)
    (state : index.State) (parent : index.Parent) (value : wrapper.Pointee)
    (read : index.access.Reads state parent value) :
    FieldReference.Reads index.access (fun _ contents => contents)
      state (⟨parent, ()⟩ : DerefResult index) value :=
  FieldReference.reads_of_parent index.access (fun _ contents => contents)
    state ⟨parent, ()⟩ value read

/-- An inaccessible parent forbids reads through the returned reference even
when an unrelated observation still contains the old value. -/
theorem deref_expired {wrapper : Wrapper} (index : DerefIndex wrapper)
    (state : index.State) (parent : index.Parent)
    (expired : ¬ index.access.live state parent) :
    ∀ value, ¬ FieldReference.Reads index.access (fun _ contents => contents)
      state (⟨parent, ()⟩ : DerefResult index) value :=
  FieldReference.no_read_of_not_live index.access (fun _ contents => contents)
    state ⟨parent, ()⟩ expired

/-- The sample is a present-or-absent slot. Removing it invalidates the
parent and its derived reference; changing it changes the current read. -/
def derefSample (wrapper : Wrapper) : DerefIndex wrapper where
  State := Option wrapper.Pointee
  Parent := Unit
  access := {
    live := fun state _ => state.isSome
    current := fun state _ => state }

/-- A nonzero, initialized account with every optional value populated. -/
def tokenSample : Token.Account :=
  ⟨.ofNat 1, .ofNat 2, 42, some (.ofNat 3), .initialized, some 9, 7, some (.ofNat 4)⟩

/-- Closed values witness the inhabited domain of each source wrapper. -/
def wrapperSample : (wrapper : Wrapper) → wrapper.Pointee
  | .stakeAccount => .stake
      ⟨40, ⟨.ofNat 1, .ofNat 2⟩, ⟨-1, 5, .ofNat 3⟩⟩
      ⟨⟨.ofNat 4, 25, 6, 9, 0x3fd0000000000000⟩, 17⟩
  | .tokenAccount | .interfaceTokenAccount => tokenSample

/-- Closed useful execution for the exact family and reference, including a
live parent and a complete pointee instead of an empty argument domain. -/
theorem deref_execution (wrapper : Wrapper) :
    FamilyHasExecution (derefFamily wrapper) (derefRun wrapper) (derefSample wrapper) := by
  exact ⟨some (wrapperSample wrapper), (),
    .returned ⟨(), ()⟩ (some (wrapperSample wrapper)),
    ⟨wrapperSample wrapper, rfl, rfl⟩, rfl⟩

/-- The two concrete Anchor marker types use the canonical SPL program IDs. -/
inductive Program where
  | token
  | token2022
  deriving DecidableEq, Repr

/-- These methods copy the ID and perform no validation or invocation. -/
def programId : Program → Solanalib.Runtime.Pubkey
  | .token => Token.legacyProgramId
  | .token2022 => Token.token2022ProgramId

/-- The exact pure ID contract, preserving an arbitrary ambient state. -/
def idContract (program : Program) (State : Type) :
    Solanalib.Contracts.Model State Unit Solanalib.Runtime.Pubkey :=
  .returning (fun _ _ => True)
    (fun before _ value after => value = programId program ∧ after = before)

/-- Copying the ID of a marker. -/
def idReference (program : Program) {State : Type}
    (before : State) (_ : Unit) : Solanalib.Runtime.Pubkey × State :=
  (programId program, before)

theorem id_reference (program : Program) (State : Type) :
    (idContract program State).RealizedBy (idReference program) :=
  fun _ _ _ => ⟨rfl, rfl⟩

/-- A stable name for the single static two-element ID array of the source. It is
neither a newly allocated vector nor a copy of the address of the array. -/
inductive InterfaceIdsRef where
  | ids
  deriving DecidableEq, Repr

/-- The static reference reads both supported program IDs, in source order. -/
def InterfaceIdsRef.read (_ : InterfaceIdsRef) : List Solanalib.Runtime.Pubkey :=
  [Token.legacyProgramId, Token.token2022ProgramId]

/-- Returning the same static shared slice leaves the entire state unchanged. -/
def idsContract (State : Type) : Solanalib.Contracts.Model State Unit InterfaceIdsRef :=
  .returning (fun _ _ => True)
    (fun before _ value after => value = .ids ∧ after = before)

def idsReference {State : Type} (before : State) (_ : Unit) : InterfaceIdsRef × State :=
  (.ids, before)

theorem ids_reference (State : Type) :
    (idsContract State).RealizedBy idsReference := fun _ _ _ => ⟨rfl, rfl⟩

/-- The slice length and element order are fixed; neither program is omitted. -/
theorem ids_exact : InterfaceIdsRef.ids.read =
    [Token.legacyProgramId, Token.token2022ProgramId] := rfl

/-- Each source ID method preserves the complete ambient state of the caller. -/
def idFamily (program : Program) : Family where
  Index := Type
  State := id
  Args := fun _ => Unit
  Value := fun _ => Solanalib.Runtime.Pubkey
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := idContract program

/-- The indexed ID reference is the same pure copy at every state type. -/
def idRun (program : Program) : FamilyRun (idFamily program) :=
  fun _ => returnsOf (idReference program)

theorem id_family_reference (program : Program) : FamilyReference (idFamily program) (idRun
  program) :=
  fun state => (realized_iff_holds _ _).mp (id_reference program state)

/-- A nonzero ambient state witnesses an actual ID return. -/
theorem id_execution (program : Program) : FamilyHasExecution (idFamily program) (idRun program)
  Nat :=
  ⟨(7 : Nat), (), .returned (programId program) (7 : Nat), trivial, rfl⟩

/-- The static slice of the source is shared across calls at every state type. -/
def idsFamily : Family where
  Index := Type
  State := id
  Args := fun _ => Unit
  Value := fun _ => InterfaceIdsRef
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := idsContract

def idsRun : FamilyRun idsFamily := fun _ => returnsOf idsReference

theorem ids_family_reference : FamilyReference idsFamily idsRun :=
  fun state => (realized_iff_holds _ _).mp (ids_reference state)

theorem ids_execution : FamilyHasExecution idsFamily idsRun Nat :=
  ⟨(7 : Nat), (), .returned .ids (7 : Nat), trivial, rfl⟩

end Solanalib.Specs.Core.AnchorSplSupport
