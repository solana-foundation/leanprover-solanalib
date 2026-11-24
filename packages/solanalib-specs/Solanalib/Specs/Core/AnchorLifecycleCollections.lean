/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleValidation

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

def optionAccountsFamily (allowMissing : Bool) : Family where
  Index := CollectionTypes
  State := fun types => AnchorAccount.World types.Aux × AccountsState types.Bumps
  Args := fun _ => AccountsArgs
  Value := fun types => Except types.Error (Option types.Payload)
  Unwind := CollectionTypes.Unwind
  Terminal := CollectionTypes.Terminal
  contract := fun types => { requires := fun _ _ => True, post := optionAccounts allowMissing types
    }

def optionAccountsRun (allowMissing : Bool) : FamilyRun (optionAccountsFamily allowMissing) :=
  optionAccounts allowMissing

theorem optionAccounts_reference (allowMissing : Bool) :
    FamilyReference (optionAccountsFamily allowMissing) (optionAccountsRun allowMissing) := by
  intro _ _ _ _ _ called
  exact called

def boxedAccountsFamily : Family where
  Index := CollectionTypes
  State := fun types => AnchorAccount.World types.Aux × AccountsState types.Bumps
  Args := fun _ => AccountsArgs
  Value := fun types => Except types.Error types.BoxResource
  Unwind := CollectionTypes.Unwind
  Terminal := CollectionTypes.Terminal
  contract := fun types => { requires := fun _ _ => True, post := boxedAccounts types }

def boxedAccountsRun : FamilyRun boxedAccountsFamily := boxedAccounts

theorem boxedAccounts_reference : FamilyReference boxedAccountsFamily boxedAccountsRun := by
  intro _ _ _ _ _ called
  exact called

/-- A callback trace witnesses the scheduling boundary. Actual clients supply
their selected T::try_accounts and allocator relations in the family index. -/
def collectionSample : CollectionTypes where
  Aux := Unit
  Bumps := Nat
  Payload := Nat
  BoxResource := Nat
  Error := Unit
  Unwind := Unit
  Terminal := Unit
  missing := Callback.ofFunction fun state _ => .returned () state
  inner := Callback.ofFunction fun state _ => .returned (.ok 9)
    (state.1, { state.2 with remaining := state.2.remaining.drop 1, bumps := state.2.bumps + 1 })
  newBox := Callback.ofFunction fun state value => .returned (value + 100) state

def collectionState : AnchorAccount.World Unit × AccountsState Nat :=
  ((AccountInfo.sampleState, ()), ⟨[⟨19, AccountInfo.sampleInfo⟩], 2, []⟩)

def collectionArgs : AccountsArgs := ⟨AccountInfo.sampleProfile, .zero, [42]⟩

theorem optionAccounts_execution (allowMissing : Bool) :
    FamilyHasExecution (optionAccountsFamily allowMissing) (optionAccountsRun allowMissing)
      collectionSample := by
  exact ⟨collectionState, collectionArgs,
    .returned (.ok none) (collectionState.1, ⟨[], (2 : Nat), []⟩), trivial, rfl⟩

theorem boxedAccounts_execution :
    FamilyHasExecution boxedAccountsFamily boxedAccountsRun collectionSample := by
  let after : AnchorAccount.World Unit × AccountsState Nat := (collectionState.1, ⟨[], 3, []⟩)
  exact ⟨collectionState, collectionArgs, .returned (.ok (109 : Nat)) after, trivial,
    .returned (.ok (9 : Nat)) after, rfl,
    .returned (109 : Nat) after, ⟨.returned (109 : Nat) after, rfl, rfl⟩, rfl⟩

def boxedDispatchFamily : Family where
  Index := DispatchTypes
  State := DispatchTypes.State
  Args := fun types => types.BoxResource × types.Arg
  Value := fun types => Except types.Error Unit
  Unwind := DispatchTypes.Unwind
  Terminal := DispatchTypes.Terminal
  contract := fun types => {
    requires := fun before args => ∃ value, types.current before args.1 = some value
    post := boxedDispatch types }

def boxedDispatchRun : FamilyRun boxedDispatchFamily := boxedDispatch

theorem boxedDispatch_reference : FamilyReference boxedDispatchFamily boxedDispatchRun := by
  intro _ _ _ _ _ called
  exact called

/-- A represented current Box and an actual callback outcome always extend to
the exact outcome of the wrapper. Representation supplies no callback execution. -/
theorem boxedDispatch_retain {types : DispatchTypes} {before : types.State}
    {resource : types.BoxResource} {args : types.Arg} {value : types.Payload}
    (current : types.current before resource = some value)
    {outcome : Outcome types.State (Except types.Error Unit) types.Unwind types.Terminal}
    (called : types.call before (value, args) outcome) :
    boxedDispatch types before (resource, args) outcome := ⟨value, current, called⟩

def optionDispatchFamily : Family where
  Index := DispatchTypes
  State := DispatchTypes.State
  Args := fun types => Option types.Payload × types.Arg
  Value := fun types => Except types.Error Unit
  Unwind := DispatchTypes.Unwind
  Terminal := DispatchTypes.Terminal
  contract := fun types => { requires := fun _ _ => True, post := optionDispatch types }

def optionDispatchRun : FamilyRun optionDispatchFamily := optionDispatch

theorem optionDispatch_reference : FamilyReference optionDispatchFamily optionDispatchRun := by
  intro _ _ _ _ _ called
  exact called

def dispatchSample : DispatchTypes where
  State := Nat
  Payload := Nat
  BoxResource := Nat
  Arg := Solanalib.Runtime.Pubkey
  Error := Unit
  Unwind := Unit
  Terminal := Unit
  current := fun _ resource => some (resource + 1)
  call := Callback.ofFunction fun state (value, _) => .returned (.ok ()) (state + value)

theorem boxedDispatch_execution :
    FamilyHasExecution boxedDispatchFamily boxedDispatchRun dispatchSample := by
  exact ⟨(2 : Nat), ((3 : Nat), .zero), .returned (.ok ()) (6 : Nat),
    ⟨(4 : Nat), rfl⟩, (4 : Nat), rfl, rfl⟩

theorem optionDispatch_execution :
    FamilyHasExecution optionDispatchFamily optionDispatchRun dispatchSample := by
  exact ⟨(2 : Nat), (some (4 : Nat), .zero), .returned (.ok ()) (6 : Nat), trivial, rfl⟩

/-- Option::close captures its by-value destination in the closure. For None,
that uncalled closure still drops the moved AccountInfo. On Some the exact
destination is transferred into the selected T::close callback. -/
structure OptionCloseTypes extends Base where
  Payload : Type
  rc : AccountInfoRc.Ops (AnchorAccount.World Aux) Terminal
  close : Callback.Run (AnchorAccount.World Aux) (Payload × AccountInfo.Value)
    (Except (AnchorErrorOperations.Error errorStorage Program StringResource BoxResource) Unit)
      (AnchorAccount.ConstructorUnwind Unwind)
      (AnchorAccount.ConstructorTerminal Terminal)

def optionClose (types : OptionCloseTypes) :
    types.toBase.Run (Option types.Payload × AccountInfo.Value) (Except types.toBase.Error Unit) :=
  fun before (value, destination) outcome =>
    match value with
    | some value => types.close before (value, destination) outcome
    | none => Owned.cleanup (noDoubleUnwind types.toBase)
        [dropInfo types.toBase types.rc destination] (.returned (.ok ()) before) outcome

def optionCloseFamily : Family where
  Index := OptionCloseTypes
  State := fun types => AnchorAccount.World types.Aux
  Args := fun types => Option types.Payload × AccountInfo.Value
  Value := fun types => Except types.toBase.Error Unit
  Unwind := fun types => types.toBase.Unw
  Terminal := fun types => types.toBase.Term
  contract := fun types => { requires := fun _ _ => True, post := optionClose types }

def optionCloseRun : FamilyRun optionCloseFamily := optionClose

theorem optionClose_reference : FamilyReference optionCloseFamily optionCloseRun := by
  intro _ _ _ _ _ called
  exact called

def optionCloseSample : OptionCloseTypes where
  toBase := (validationSample .boxed).toBase
  Payload := Nat
  rc := (validationSample .boxed).rc
  close := Callback.ofFunction fun state _ => .returned (.ok ()) state

theorem optionClose_execution :
    FamilyHasExecution optionCloseFamily optionCloseRun optionCloseSample := by
  let state := (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary)
  exact ⟨state, (none, AccountInfo.sampleInfo), .returned (.ok ()) state, trivial,
    .returned () state,
    ⟨.returned () state, ⟨.returned () state,
      ⟨.returned () state, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- UncheckedAccount::try_from itself moves an AccountInfo in 0.27 and stores
a shared reference in later releases. Neither form clones or validates it. -/
def UncheckedInput : InfoStorage → Type
  | .owned => AccountInfo.Value
  | .borrowed => AccountReference

def uncheckedFromFamily (storage : InfoStorage) : Family where
  Index := Type
  State := id
  Args := fun _ => UncheckedInput storage
  Value := fun _ => UncheckedInput storage
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => Solanalib.Contracts.Model.returning (fun _ _ => True)
    (fun before info result after => result = info ∧ after = before)

def uncheckedFromRun (storage : InfoStorage) : FamilyRun (uncheckedFromFamily storage) :=
  fun _ => returnsOf fun state info => (info, state)

theorem uncheckedFrom_reference (storage : InfoStorage) :
    FamilyReference (uncheckedFromFamily storage) (uncheckedFromRun storage) := by
  intro state
  apply (realized_iff_holds _ _).mp
  intro _ _ _
  exact ⟨rfl, rfl⟩

def uncheckedFromSample : Type := Unit

theorem uncheckedFrom_execution (storage : InfoStorage) :
    FamilyHasExecution (uncheckedFromFamily storage) (uncheckedFromRun storage)
      uncheckedFromSample := by
  cases storage with
  | owned => exact ⟨(), AccountInfo.sampleInfo,
      .returned AccountInfo.sampleInfo (), trivial, rfl⟩
  | borrowed => exact ⟨(), (⟨19, AccountInfo.sampleInfo⟩ : AccountReference),
      .returned ⟨19, AccountInfo.sampleInfo⟩ (), trivial, rfl⟩

end Solanalib.Specs.Core.AnchorLifecycle
