/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorContextOwned
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorContextOperations

/-- The three references and bump payload moved by `Context::new`. Reference
types retain the identities and lifetimes of the caller; in particular, the mutable
accounts reference is not replaced by an observation of the accounts. The
older `BTreeMap` and the newer associated `Bumps` are separate instantiations.
There is no account validation, callback, allocation or CPI in this constructor. -/
structure ContextValue (ProgramRef AccountsRef RemainingRef Bumps : Type) where
  programId : ProgramRef
  accounts : AccountsRef
  remainingAccounts : RemainingRef
  bumps : Bumps
  deriving DecidableEq, Repr

/-- Owned CPI-context fields, with their actual representation supplied by the
caller. `Program` is an owned `AccountInfo` through Anchor 0.32.1, and a copyable
`Pubkey` from 1.0. `Remaining` is the resource identity of the vector, not its saved
contents; `SeedRef` is the borrowed nested slice descriptor. This common carrier
performs no invocation and does not coerce an old program handle into a key. -/
structure CpiValue (Accounts Program Remaining SeedRef : Type) where
  accounts : Accounts
  program : Program
  remainingAccounts : Remaining
  signerSeeds : SeedRef
  deriving DecidableEq, Repr

/-- Actual source representations of the borrowed Context fields. -/
structure ContextTypes where
  State : Type
  ProgramRef : Type
  AccountsRef : Type
  RemainingRef : Type
  Bumps : Type

abbrev ContextTypes.Value (types : ContextTypes) :=
  ContextValue types.ProgramRef types.AccountsRef types.RemainingRef types.Bumps

/-- `Context::new` only moves its four arguments. Trait bounds used by other
Context methods impose no mathematical validation on this constructor. -/
def contextNewFamily : Family where
  Index := ContextTypes
  State := ContextTypes.State
  Args := ContextTypes.Value
  Value := ContextTypes.Value
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => .returning (fun _ _ => True)
    (fun before args result after => result = args ∧ after = before)

def contextNewRun : FamilyRun contextNewFamily :=
  fun _ => returnsOf (fun before args => (args, before))

theorem contextNew_reference : FamilyReference contextNewFamily contextNewRun := by
  intro types
  apply (realized_iff_holds _ _).mp
  exact fun _ _ _ => ⟨rfl, rfl⟩

abbrev contextSample : ContextTypes := ⟨Nat, Nat, Nat, Nat, List (String × UInt8)⟩

def contextSampleArgs : contextSample.Value := ⟨11, 12, 13, [("vault", 254)]⟩

theorem contextNew_execution : FamilyHasExecution contextNewFamily contextNewRun contextSample :=
  ⟨(7 : Nat), contextSampleArgs, .returned contextSampleArgs (7 : Nat), trivial, rfl⟩

theorem contextNew_satisfiable : FamilySatisfiable contextNewFamily contextSample :=
  contextNew_execution.satisfiable

/-- The source-level identities needed to describe a CPI context without
choosing the old program-handle representation or the new copied Pubkey. -/
structure CpiTypes where
  State : Type
  Accounts : Type
  Program : Type
  Remaining : Type
  SeedRef : Type

abbrev CpiTypes.Value (types : CpiTypes) :=
  CpiValue types.Accounts types.Program types.Remaining types.SeedRef

/-- Empty construction uses the common vector primitive. The zero-length
borrowed seed descriptor is supplied separately from a byte-list observation. -/
structure NewTypes extends CpiTypes where
  AccountInfo : Type
  remaining : Owned.VectorOps State AccountInfo Remaining Empty Empty
  emptySeeds : SeedRef

/-- Arguments of the signer constructor, retaining all borrowed seed aliases. -/
structure NewArgs (Accounts Program SeedRef : Type) where
  program : Program
  accounts : Accounts
  seeds : SeedRef
  deriving DecidableEq, Repr

/-- Only guarantees of the reached empty-vector primitive are needed here. -/
structure EmptyReady (types : NewTypes) (before : types.State) : Prop where
  current : types.remaining.current (types.remaining.empty before).2
    (types.remaining.empty before).1 = some []
  fresh : types.remaining.current before (types.remaining.empty before).1 = none

def newWithSigner (types : NewTypes) (before : types.State)
    (args : NewArgs types.Accounts types.Program types.SeedRef) :
    types.toCpiTypes.Value × types.State :=
  let (remaining, after) := types.remaining.empty before
  (⟨args.accounts, args.program, remaining, args.seeds⟩, after)

def newWithSignerFamily : Family where
  Index := NewTypes
  State := fun types => types.State
  Args := fun types => NewArgs types.Accounts types.Program types.SeedRef
  Value := fun types => types.toCpiTypes.Value
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun types => .returning (fun before _ => EmptyReady types before)
    (fun before args result after => (result, after) = newWithSigner types before args ∧
      types.remaining.current after result.remainingAccounts = some [] ∧
      types.remaining.current before result.remainingAccounts = none)

def newWithSignerRun : FamilyRun newWithSignerFamily := fun types => returnsOf (newWithSigner types)

theorem newWithSigner_reference : FamilyReference newWithSignerFamily newWithSignerRun := by
  intro types
  apply (realized_iff_holds _ _).mp
  exact fun _ _ ready => ⟨rfl, ready.current, ready.fresh⟩

def newContext (types : NewTypes) (before : types.State)
    (args : types.Program × types.Accounts) : types.toCpiTypes.Value × types.State :=
  newWithSigner types before ⟨args.1, args.2, types.emptySeeds⟩

def newFamily : Family where
  Index := NewTypes
  State := fun types => types.State
  Args := fun types => types.Program × types.Accounts
  Value := fun types => types.toCpiTypes.Value
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun types => .returning (fun before _ => EmptyReady types before)
    (fun before args result after => (result, after) = newContext types before args ∧
      result.signerSeeds = types.emptySeeds ∧
      types.remaining.current after result.remainingAccounts = some [] ∧
      types.remaining.current before result.remainingAccounts = none)

def newRun : FamilyRun newFamily := fun types => returnsOf (newContext types)

theorem new_reference : FamilyReference newFamily newRun := by
  intro types
  apply (realized_iff_holds _ _).mp
  exact fun _ _ ready => ⟨rfl, rfl, ready.current, ready.fresh⟩

/-- Replacing borrowed signer seeds drops no owned accounts and calls no
vector dependency. Every owned field and the entire ambient state are kept. -/
def withSignerFamily : Family where
  Index := CpiTypes
  State := CpiTypes.State
  Args := fun types => types.Value × types.SeedRef
  Value := CpiTypes.Value
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => .returning (fun _ _ => True)
    (fun before args result after => result = { args.1 with signerSeeds := args.2 } ∧ after =
      before)

def withSignerRun : FamilyRun withSignerFamily :=
  fun _ => returnsOf (fun before args => ({ args.1 with signerSeeds := args.2 }, before))

theorem withSigner_reference : FamilyReference withSignerFamily withSignerRun := by
  intro types
  apply (realized_iff_holds _ _).mp
  exact fun _ _ _ => ⟨rfl, rfl⟩

/-- `Vec<AccountInfo>` destruction has no user-defined unwinding destructor.
Its actual reference releases and deallocation are retained in the common
vector dependency. A terminal exit stops the method before returning self. -/
structure RemainingTypes extends CpiTypes where
  AccountInfo : Type
  Terminal : Type
  remaining : Owned.VectorOps State AccountInfo Remaining Empty Terminal

/-- Assignment destroys the old vector before returning the context with the
new vector owner. Accounts, program and seeds are moved unchanged; neither
vector is reduced to a saved list of observations. -/
def withRemainingRun (types : RemainingTypes) :
    Callback.Run types.State (types.toCpiTypes.Value × types.Remaining)
      types.toCpiTypes.Value Empty types.Terminal :=
  fun before args => Callback.map (fun _ => { args.1 with remainingAccounts := args.2 })
    types.remaining.drop before args.1.remainingAccounts

def withRemainingFamily : Family where
  Index := RemainingTypes
  State := fun types => types.State
  Args := fun types => types.toCpiTypes.Value × types.Remaining
  Value := fun types => types.toCpiTypes.Value
  Unwind := fun _ => Empty
  Terminal := RemainingTypes.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := withRemainingRun types }

theorem withRemaining_reference : FamilyReference withRemainingFamily withRemainingRun :=
  fun _ _ _ _ _ step => step

/-- A normal return retains the final state of the actual destructor and replaces
only the remaining-vector owner. This rules out a state-free overwrite. -/
theorem withRemaining_returned_iff (types : RemainingTypes)
    (before after : types.State) (context result : types.toCpiTypes.Value)
    (remaining : types.Remaining) :
    withRemainingRun types before (context, remaining) (.returned result after) ↔
      types.remaining.drop before context.remainingAccounts (.returned () after) ∧
      result = { context with remainingAccounts := remaining } := by
  constructor
  · rintro ⟨intermediate, dropped, equal⟩
    cases intermediate with
    | returned value state =>
      cases value
      cases equal
      exact ⟨dropped, rfl⟩
    | unwound reason => exact Empty.elim reason
    | terminated reason => cases equal
  · rintro ⟨dropped, rfl⟩
    exact ⟨.returned () after, dropped, rfl⟩

abbrev cpiSample : NewTypes where
  State := Owned.VectorState Nat
  Accounts := Nat
  Program := Nat
  Remaining := Nat
  SeedRef := List Nat
  AccountInfo := Nat
  remaining := Owned.vectorReference
  emptySeeds := []

def cpiSampleArgs : NewArgs cpiSample.Accounts cpiSample.Program cpiSample.SeedRef :=
  ⟨41, 42, [7, 7, 9]⟩

theorem newWithSigner_execution : FamilyHasExecution newWithSignerFamily newWithSignerRun cpiSample
  :=
  ⟨[], cpiSampleArgs, .returned ⟨42, 41, 0, [7, 7, 9]⟩ [some []],
    ⟨Owned.vectorReference_laws.empty_current [], Owned.vectorReference_laws.empty_fresh []⟩, rfl⟩

theorem newWithSigner_satisfiable : FamilySatisfiable newWithSignerFamily cpiSample :=
  newWithSigner_execution.satisfiable

theorem new_execution : FamilyHasExecution newFamily newRun cpiSample :=
  ⟨[], (41, 42), .returned ⟨42, 41, 0, []⟩ [some []],
    ⟨Owned.vectorReference_laws.empty_current [], Owned.vectorReference_laws.empty_fresh []⟩, rfl⟩

theorem new_satisfiable : FamilySatisfiable newFamily cpiSample := new_execution.satisfiable

theorem withSigner_execution : FamilyHasExecution withSignerFamily withSignerRun
  cpiSample.toCpiTypes :=
  ⟨[some [5]], (⟨42, 41, 0, [1]⟩, [7, 7, 9]),
    .returned ⟨42, 41, 0, [7, 7, 9]⟩ [some [5]], trivial, rfl⟩

theorem withSigner_satisfiable : FamilySatisfiable withSignerFamily cpiSample.toCpiTypes :=
  withSigner_execution.satisfiable

abbrev remainingSample : RemainingTypes where
  toCpiTypes := cpiSample.toCpiTypes
  AccountInfo := Nat
  Terminal := Empty
  remaining := Owned.vectorReference

theorem withRemaining_execution :
    FamilyHasExecution withRemainingFamily withRemainingRun remainingSample := by
  refine ⟨[some [5, 6], some [8]], (⟨42, 41, 0, [7]⟩, 1),
    .returned ⟨42, 41, 1, [7]⟩ [none, some [8]], trivial, ?_⟩
  exact ⟨.returned () [none, some [8]], ⟨[5, 6], rfl, rfl⟩, rfl⟩

theorem withRemaining_satisfiable : FamilySatisfiable withRemainingFamily remainingSample :=
  withRemaining_execution.satisfiable

end Solanalib.Specs.Core.AnchorContextOperations
