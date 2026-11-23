/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenStateFacts
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- The complete checked parser computation of the version, retaining its guard
effects on both success and ordinary error. -/
def fromViewContract (revision : ViewRevision) (kind : ViewKind) :
    Solanalib.Contracts.Model ViewState Borrow.Handle (Except Error Ref) :=
  .returning (fun _ _ => True) (fun before handle value after =>
    fromAccountView revision kind before handle = (value, after))

/-- Reference realization of the complete parser, with no assumed success. -/
theorem fromViewReference_realizes (revision : ViewRevision) (kind : ViewKind) :
    (fromViewContract revision kind).RealizedBy (fromAccountView revision kind) := by
  intro before handle _
  rfl

/-- Every parser policy has a represented input, including uninitialized bytes. -/
theorem fromViewContract_satisfiable (revision : ViewRevision) (kind : ViewKind) :
    (fromViewContract revision kind).Satisfiable :=
  ⟨viewWitnessState revision.programId (List.replicate kind.length 0), ⟨0⟩,
    True.intro⟩

/-- A balance read observes the currently borrowed raw account. -/
def amountContract : Solanalib.Contracts.Model ViewState Ref Nat :=
  .returning AccountReadable (fun before ref value after =>
    after = before ∧ ∃ raw, currentAccount before ref = .ok raw ∧ value = raw.amount)

/-- The amount reference returns exactly the value selected by the live guard. -/
theorem amountReference_realizes : amountContract.RealizedBy amountReference := by
  intro before ref readable
  obtain ⟨raw, current⟩ := readable
  exact ⟨rfl, raw, current, by simp [amountReference, current]⟩

/-- Balance reading has a live, current shared-guard witness. -/
theorem amountContract_satisfiable : amountContract.Satisfiable :=
  ⟨accountWitnessState, accountWitnessRef, accountWitness, accountWitness_current⟩

/-- Construct the mint-field descriptor with the supplied parent guard identity.
Reading its bytes separately requires a current, complete guarded view. -/
def mintContract : Solanalib.Contracts.Model ViewState Ref KeyRef :=
  .returning (fun _ _ => True) (fun before ref value after =>
    after = before ∧ value = ⟨ref.guard, 0⟩)

/-- Returning a field reference preserves the lease identity of the parent. -/
theorem mintReference_realizes : mintContract.RealizedBy mintReference := by
  intro before ref _
  exact ⟨rfl, rfl⟩

/-- Mint-field borrowing has a represented live parent reference. -/
theorem mintContract_satisfiable : mintContract.Satisfiable :=
  ⟨accountWitnessState, accountWitnessRef, True.intro⟩

/-- Construct the owner-field descriptor at offset 32 with the supplied guard.
This descriptor equality does not establish that the guard is readable. -/
def ownerContract : Solanalib.Contracts.Model ViewState Ref KeyRef :=
  .returning (fun _ _ => True) (fun before ref value after =>
    after = before ∧ value = ⟨ref.guard, 32⟩)

/-- Returning the owner-field reference preserves the lease identity of the parent. -/
theorem ownerReference_realizes : ownerContract.RealizedBy ownerReference := by
  intro before ref _
  exact ⟨rfl, rfl⟩

/-- Owner-field borrowing has a represented live parent reference. -/
theorem ownerContract_satisfiable : ownerContract.Satisfiable :=
  ⟨accountWitnessState, accountWitnessRef, True.intro⟩

/-- Decimal precision is read from the currently borrowed mint byte view. -/
def decimalsContract : Solanalib.Contracts.Model ViewState Ref UInt8 :=
  .returning MintReadable (fun before ref value after =>
    after = before ∧ ∃ raw, currentMint before ref = .ok raw ∧ value = raw.decimals)

/-- Decimal reading retains the same account contents and guard registry. -/
theorem decimalsReference_realizes : decimalsContract.RealizedBy decimalsReference := by
  intro before ref readable
  obtain ⟨raw, current⟩ := readable
  exact ⟨rfl, raw, current, by simp [decimalsReference, current]⟩

/-- Decimal reading has a live guarded mint witness. -/
theorem decimalsContract_satisfiable : decimalsContract.Satisfiable :=
  ⟨mintWitnessState, mintWitnessRef, mintWitness, mintWitness_current⟩

/-- The target-specific panic provider of the state projection. Its Empty result
forbids converting a Rust panic into an ordinary account-state value. -/
structure StatePolicy where
  /-- The unwind reasons of the selected target. -/
  Unwind : Type
  /-- The terminal reasons of the selected target. -/
  Terminal : Type
  /-- The explicit nonreturning handler for an invalid state byte. -/
  panic : StatePanic Unwind Terminal

/-- The state getter requires a current raw account view. Its explicit panic
provider supplies the finite exits of invalid-byte conversion; readability
does not require that provider to terminate. -/
def stateFamily : Family where
  Index := StatePolicy
  State := fun _ => ViewState
  Args := fun _ => Ref
  Value := fun _ => AccountState
  Unwind := StatePolicy.Unwind
  Terminal := StatePolicy.Terminal
  contract := fun policy => {
    requires := AccountReadable
    post := stateRun policy.panic }

/-- The reference family follows the checked state conversion and forwards
each finite panic outcome exactly. -/
def stateFamilyRun : FamilyRun stateFamily := fun policy => stateRun policy.panic

/-- The state-family reference is correct for every target-specific handler. -/
theorem stateFamily_reference : FamilyReference stateFamily stateFamilyRun := by
  intro policy before ref outcome _ run
  exact run

/-- Readability supplies the actual state byte and its local continuation:
a decoded enum returns normally, while every actual finite panic exit is
forwarded with its state and reason. No panic-provider outcome is assumed. -/
theorem stateFamily_continues (policy : StatePolicy) {before : ViewState} {ref : Ref}
    (readable : (stateFamily.contract policy).requires before ref) :
    ∃ raw, currentAccount before ref = .ok raw ∧
      match decodeAccountState raw.stateByte with
      | some value => stateFamilyRun policy before ref (.returned value before)
      | none => ∀ outcome, policy.panic before raw.stateByte outcome →
          stateFamilyRun policy before ref
            (Outcome.map (fun impossible : Empty => nomatch impossible) outcome) := by
  obtain ⟨raw, current⟩ := readable
  refine ⟨raw, current, ?_⟩
  cases decoded : decodeAccountState raw.stateByte with
  | some value =>
    simp only [stateFamilyRun, stateRun, current, decoded]
    rfl
  | none =>
    intro outcome ran
    change stateRun policy.panic before ref _
    simp only [stateRun, current, decoded, Callback.map]
    exact ⟨outcome, ran, rfl⟩

/-- A concrete abort policy for the closed witness. It is one sample target
interpretation, not a universal assumption that panics always abort. -/
def stateAbortPolicy : StatePolicy where
  Unwind := Empty
  Terminal := UInt8
  panic := fun _ byte outcome => outcome = .terminated byte

/-- The raw state byte of the account witness is uninitialized. -/
theorem accountWitness_stateByte : accountWitness.stateByte = 0 := by
  simp only [AccountRaw.stateByte, accountWitness, getElem!_def,
    List.getElem?_replicate_of_lt (show 108 < accountLength by decide)]

/-- The selected family sample has a current live reference. -/
theorem stateFamily_satisfiable : FamilySatisfiable stateFamily stateAbortPolicy :=
  ⟨accountWitnessState, accountWitnessRef, accountWitness, accountWitness_current⟩

/-- A real finite normal execution witnesses the nonvacuity of the sample. Invalid
state-byte panic executions are checked separately in the regression suite. -/
theorem stateFamily_execution :
    FamilyHasExecution stateFamily stateFamilyRun stateAbortPolicy := by
  refine ⟨accountWitnessState, accountWitnessRef,
    .returned .uninitialized accountWitnessState,
    ⟨accountWitness, accountWitness_current⟩, ?_⟩
  change stateRun stateAbortPolicy.panic accountWitnessState accountWitnessRef _
  simp only [stateRun, accountWitness_current, accountWitness_stateByte, decodeAccountState]
  rfl

end Solanalib.Specs.Core.Token
