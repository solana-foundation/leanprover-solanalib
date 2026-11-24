/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleCollections
public import Solanalib.Specs.Core.AnchorLifecyclePayloadSamples

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

/-- Source collection indices fix the missing-account error factory of Anchor.
Only T::try_accounts and Box::new remain explicit dependency interfaces. -/
structure AccountCollectionTypes extends Base where
  Bumps : Type
  Payload : Type
  PayloadBox : Type
  inner : Callback.Run (AnchorAccount.World Aux × AccountsState Bumps) AccountsArgs
    (Except (AnchorErrorOperations.Error errorStorage Program StringResource BoxResource) Payload)
    (AnchorAccount.ConstructorUnwind Unwind) (AnchorAccount.ConstructorTerminal Terminal)
  newBox : Callback.Run (AnchorAccount.World Aux × AccountsState Bumps) Payload PayloadBox Empty
    Terminal

def collectionBoxOutcome {State Value Terminal : Type} :
    Outcome State Value Empty Terminal → Outcome State Value Empty
      (AnchorAccount.ConstructorTerminal Terminal)
  | .returned value after => .returned value after
  | .unwound impossible _ => nomatch impossible
  | .terminated reason => .terminated (.inr reason)

def AccountCollectionTypes.operations (types : AccountCollectionTypes) : CollectionTypes where
  Aux := types.Aux
  Bumps := types.Bumps
  Payload := types.Payload
  BoxResource := types.PayloadBox
  Error := types.toBase.Error
  Unwind := types.toBase.Unw
  Terminal := types.toBase.Term
  missing := Owned.Focus.fst.lift (code types.toBase .notEnoughKeys)
  inner := types.inner
  newBox := fun before value outcome => ∃ produced,
    types.newBox before value produced ∧ collectionBoxOutcome produced = outcome

def collectionOptionFamily (allowMissing : Bool) : Family where
  Index := AccountCollectionTypes
  State := fun types => AnchorAccount.World types.Aux × AccountsState types.Bumps
  Args := fun _ => AccountsArgs
  Value := fun types => Except types.toBase.Error (Option types.Payload)
  Unwind := fun types => types.toBase.Unw
  Terminal := fun types => types.toBase.Term
  contract := fun types => (optionAccountsFamily allowMissing).contract types.operations

def collectionOptionRun (allowMissing : Bool) : FamilyRun (collectionOptionFamily allowMissing) :=
  fun types => optionAccounts allowMissing types.operations

theorem collectionOption_reference (allowMissing : Bool) :
    FamilyReference (collectionOptionFamily allowMissing) (collectionOptionRun allowMissing) := by
  intro _ _ _ _ _ called
  exact called

def collectionBoxedFamily : Family where
  Index := AccountCollectionTypes
  State := fun types => AnchorAccount.World types.Aux × AccountsState types.Bumps
  Args := fun _ => AccountsArgs
  Value := fun types => Except types.toBase.Error types.PayloadBox
  Unwind := fun types => types.toBase.Unw
  Terminal := fun types => types.toBase.Term
  contract := fun types => boxedAccountsFamily.contract types.operations

def collectionBoxedRun : FamilyRun collectionBoxedFamily := fun types => boxedAccounts
  types.operations

theorem collectionBoxed_reference : FamilyReference collectionBoxedFamily collectionBoxedRun := by
  intro _ _ _ _ _ called
  exact called

def accountCollectionSample (errors : AnchorErrorOperations.Storage) : AccountCollectionTypes where
  toBase := (payloadSample errors).toBase
  Bumps := Nat
  Payload := Nat
  PayloadBox := Nat
  inner := Callback.ofFunction fun state _ => .returned (.ok 9)
    (state.1, { state.2 with remaining := state.2.remaining.drop 1, bumps := state.2.bumps + 1 })
  newBox := Callback.ofFunction fun state value => .returned (value + 100) state

def accountCollectionState : AnchorAccount.World AnchorErrorOwned.Reference.State × AccountsState
  Nat :=
  ((AccountInfo.sampleState, AnchorOwnedSamples.auxiliary), ⟨[⟨19, AccountInfo.sampleInfo⟩], 2, []⟩)

theorem collectionOption_execution (allowMissing : Bool) (errors : AnchorErrorOperations.Storage) :
    FamilyHasExecution (collectionOptionFamily allowMissing) (collectionOptionRun allowMissing)
      (accountCollectionSample errors) := by
  exact ⟨accountCollectionState, collectionArgs,
    .returned (.ok none) (accountCollectionState.1, ⟨[], (2 : Nat), []⟩), trivial, rfl⟩

theorem collectionBoxed_execution (errors : AnchorErrorOperations.Storage) :
    FamilyHasExecution collectionBoxedFamily collectionBoxedRun (accountCollectionSample errors) :=
      by
  let after : AnchorAccount.World AnchorErrorOwned.Reference.State × AccountsState Nat :=
    (accountCollectionState.1, ⟨[], 3, []⟩)
  exact ⟨accountCollectionState, collectionArgs, .returned (.ok (109 : Nat)) after, trivial,
    .returned (.ok (9 : Nat)) after, rfl,
    .returned (109 : Nat) after, ⟨.returned (109 : Nat) after, ⟨_, rfl, rfl⟩, rfl⟩, rfl⟩

/-- The index records the actual selected allow-missing-optionals cfg. Source
interpretation checks that flag against the resolved build of the defining crate. -/
structure OptionalTypes extends AccountCollectionTypes where
  allowMissing : Bool

def optionalFamily : Family where
  Index := OptionalTypes
  State := fun types => AnchorAccount.World types.Aux × AccountsState types.Bumps
  Args := fun _ => AccountsArgs
  Value := fun types => Except types.toAccountCollectionTypes.toBase.Error (Option types.Payload)
  Unwind := fun types => types.toAccountCollectionTypes.toBase.Unw
  Terminal := fun types => types.toAccountCollectionTypes.toBase.Term
  contract := fun types => (collectionOptionFamily types.allowMissing).contract
    types.toAccountCollectionTypes

def optionalRun : FamilyRun optionalFamily := fun types =>
  collectionOptionRun types.allowMissing types.toAccountCollectionTypes

theorem optional_reference : FamilyReference optionalFamily optionalRun := by
  intro _ _ _ _ _ called
  exact called

def optionalSample (errors : AnchorErrorOperations.Storage) : OptionalTypes :=
  ⟨accountCollectionSample errors, false⟩

theorem optional_execution (errors : AnchorErrorOperations.Storage) :
    FamilyHasExecution optionalFamily optionalRun (optionalSample errors) :=
  collectionOption_execution false errors

end Solanalib.Specs.Core.AnchorLifecycle
