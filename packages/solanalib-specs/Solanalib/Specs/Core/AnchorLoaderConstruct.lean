/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLoaderIdentity
public import Solanalib.Specs.Core.AnchorLifecycle

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLoader

/-- The unchecked loader only calls Owner and the fixed owned-error
primitives. It has no deserializer or CheckOwner trait dependency. -/
structure ConstructorTypes where
  Aux : Type
  Unwind : Type
  Terminal : Type
  StringResource : Type
  BoxResource : Type
  errors : AnchorErrorOwned.Ops (AnchorAccount.World Aux) StringResource BoxResource Terminal
  Payload : Type
  ownerAt : AccountInfo.OwnerAt Aux
  owner : Callback.Run (AnchorAccount.World Aux) Unit Solanalib.Runtime.Pubkey Unwind Terminal

/-- Reuse the existing source-ordered Owner diagnostic and checked-loader
implementation. The other two constructor branches are not invoked here;
their callback slots deliberately have no executions. -/
def ConstructorTypes.constructor (types : ConstructorTypes) (discriminator :
  Solanalib.Runtime.Bytes) :
    AnchorConstructOwned.Types where
  Aux := types.Aux
  Payload := types.Payload
  Unwind := types.Unwind
  Terminal := types.Terminal
  StringResource := types.StringResource
  BoxResource := types.BoxResource
  errors := types.errors
  discriminator := discriminator
  ownerAt := types.ownerAt
  owner := types.owner
  checkOwner := fun _ _ _ => False
  deserialize := fun _ _ _ => False

/-- Share the common lifecycle operations at the exact modern boxed-error
representation used by all three reviewed loader releases. -/
def ConstructorTypes.toBase (types : ConstructorTypes) : AnchorLifecycle.Base :=
  AnchorLifecycle.Base.ofConstructor (types.constructor [])

/-- Keep only constructor operations used by AccountLoader. -/
def ConstructorTypes.ofConstructor (types : AnchorConstructOwned.Types) : ConstructorTypes :=
  ⟨types.Aux, types.Unwind, types.Terminal, types.StringResource, types.BoxResource,
    types.errors, types.Payload, types.ownerAt, types.owner⟩

/-- The source program-ID argument is retained even though this constructor
does not inspect it. The account reference retains its own record identity. -/
structure UncheckedArgs where
  profile : AccountInfo.Profile
  programId : Solanalib.Runtime.Pubkey
  account : Reference
  deriving DecidableEq, Repr

def UncheckedArgs.info (args : UncheckedArgs) : AccountInfo.Args :=
  ⟨args.profile, args.account.info⟩

/-- `try_from_unchecked` checks Owner with its actual callback effects and
diagnostic error cleanup. It neither acquires data nor checks its discriminator. -/
def unchecked (types : ConstructorTypes) :
    types.toBase.Run UncheckedArgs (Except types.toBase.Error (Value types.Payload)) :=
  fun before args => AnchorEffects.resultBind
    (AnchorConstructOwned.ownerCheck (types.constructor []))
    (fun _ after outcome => outcome = .returned (.ok ⟨args.account⟩) after)
    before args.info

/-- Only reached mismatch diagnostics require their real error-Box/store
continuation. Data cells, balances and discriminators are not inspected. -/
def UncheckedReady (types : ConstructorTypes) (before : AnchorAccount.World types.Aux)
    (args : UncheckedArgs) : Prop :=
  AnchorConstructOwned.OwnerCheckReady (types.constructor []) before args.info

/-- Each actual matching Owner return immediately constructs the reference
without any further dependency, allocation or borrow. -/
theorem unchecked_matching {types : ConstructorTypes} {before after : AnchorAccount.World types.Aux}
    {args : UncheckedArgs} {owner : Solanalib.Runtime.Pubkey}
    (called : types.owner before () (.returned owner after))
    (same : types.ownerAt after.2 args.account.info.ownerRef = owner) :
    unchecked types before args (.returned (.ok ⟨args.account⟩) after) := by
  refine ⟨.returned (.ok ()) after, ?_, rfl⟩
  refine ⟨.returned owner after, ⟨.returned owner after, called, rfl⟩, ?_⟩
  simp only [ConstructorTypes.constructor, UncheckedArgs.info, same, ↓reduceIte]
  rfl

/-- The actual Owner unwind is retained without touching data or performing
an uncalled diagnostic branch. -/
theorem unchecked_unwind {types : ConstructorTypes} {before after : AnchorAccount.World types.Aux}
    {args : UncheckedArgs} {reason : types.Unwind}
    (called : types.owner before () (.unwound reason after)) :
    unchecked types before args (.unwound (.inr reason) after) := by
  exact ⟨.unwound (.inr reason) after,
    ⟨.unwound (.inr reason) after, ⟨.unwound reason after, called, rfl⟩, rfl⟩, rfl⟩

theorem unchecked_reference_identity {types : ConstructorTypes}
    {before after : AnchorAccount.World types.Aux} {args : UncheckedArgs}
    {value : Value types.Payload}
    (called : unchecked types before args (.returned (.ok value) after)) :
    value.account = args.account := by
  obtain ⟨produced, _, continued⟩ := called
  cases produced with
  | unwound _ _ => cases continued
  | terminated _ => cases continued
  | returned result middle =>
    cases result with
    | error _ => cases continued
    | ok _ => cases continued; rfl

def uncheckedFamily : Family where
  Index := ConstructorTypes
  State := fun types => AnchorAccount.World types.Aux
  Args := fun _ => UncheckedArgs
  Value := fun types => Except types.toBase.Error (Value types.Payload)
  Unwind := fun types => types.toBase.Unw
  Terminal := fun types => types.toBase.Term
  contract := fun types => { requires := UncheckedReady types, post := unchecked types }

def uncheckedReference : FamilyRun uncheckedFamily := unchecked
theorem unchecked_reference : FamilyReference uncheckedFamily uncheckedReference := by
  intro _ _ _ _ _ step
  exact step

/-- The generated bump type stays distinct from the source account sequence;
the readonly instruction bytes and program ID are kept in AccountsArgs. -/
structure AccountsTypes where
  constructor : ConstructorTypes
  Bumps : Type
  discriminator : Solanalib.Runtime.Bytes

/-- Every mutable `try_accounts` argument is part of the actual post-state.
Record identity, order and duplicate aliases survive slicing. -/
structure AccountsState (types : AccountsTypes) where
  world : AnchorAccount.World types.constructor.Aux
  remaining : List Reference
  bumps : types.Bumps
  reallocs : List Solanalib.Runtime.Pubkey

/-- Put the actual callback post-world back alongside the already-updated
slice. It cannot select a different tail, bump value or realloc set. -/
def accountsFocus (types : AccountsTypes) :
    Owned.Focus (AccountsState types) (AnchorAccount.World types.constructor.Aux) where
  get := AccountsState.world
  set := fun state world => { state with world := world }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Empty input constructs AccountNotEnoughKeys. Otherwise the source pops
exactly one record before calling the existing checked loader constructor.
That pop remains visible on an ordinary error and on an unwind. -/
def tryAccounts (types : AccountsTypes) :
    Callback.Run (AccountsState types) AnchorLifecycle.AccountsArgs
      (Except types.constructor.toBase.Error (Value types.constructor.Payload))
      types.constructor.toBase.Unw types.constructor.toBase.Term :=
  fun before args outcome => match before.remaining with
    | [] => (accountsFocus types).lift
        (AnchorLifecycle.fail types.constructor.toBase .notEnoughKeys) before () outcome
    | account :: rest => (accountsFocus types).lift
        (Callback.map (Except.map fun _ => Value.mk account)
          (AnchorConstructOwned.run .loader (types.constructor.constructor types.discriminator)))
        { before with remaining := rest } ⟨args.profile, account.info⟩ outcome

/-- Admission is the existing checked-loader domain at the reached head.
An empty slice has no owner, data or allocator-success precondition. -/
def AccountsReady (types : AccountsTypes) (before : AccountsState types)
    (args : AnchorLifecycle.AccountsArgs) : Prop :=
  match before.remaining with
  | [] => True
  | account :: _ => AnchorConstructOwned.Ready .loader
      (types.constructor.constructor types.discriminator) before.world ⟨args.profile, account.info⟩

/-- The slice pop and unchanged independent mutable arguments, including on
an error/unwind. A terminal has no model post-state. -/
def AccountsFrame (types : AccountsTypes) (before : AccountsState types) :
    Outcome (AccountsState types)
      (Except types.constructor.toBase.Error (Value types.constructor.Payload))
      types.constructor.toBase.Unw types.constructor.toBase.Term → Prop
  | .returned _ after | .unwound _ after =>
      after.remaining = before.remaining.drop 1 ∧ after.bumps = before.bumps ∧
        after.reallocs = before.reallocs
  | .terminated _ => True

theorem tryAccounts_frame {types : AccountsTypes} {before : AccountsState types}
    {args : AnchorLifecycle.AccountsArgs} {outcome}
    (called : tryAccounts types before args outcome) : AccountsFrame types before outcome := by
  unfold tryAccounts at called
  split at called
  next empty =>
    obtain ⟨produced, _, rfl⟩ := called
    cases produced <;> simp [accountsFocus, Owned.Focus.liftOutcome, AccountsFrame, empty]
  next account rest remaining =>
    obtain ⟨produced, _, rfl⟩ := called
    cases produced <;> simp [accountsFocus, Owned.Focus.liftOutcome, AccountsFrame, remaining]

/-- Every actual checked-constructor exit survives the outer account-slice
update with exactly the same value/error/unwind and callback state. -/
theorem tryAccounts_retain {types : AccountsTypes} {before : AccountsState types}
    {args : AnchorLifecycle.AccountsArgs} {account : Reference} {rest : List Reference}
    (remaining : before.remaining = account :: rest) {produced}
    (called : AnchorConstructOwned.run .loader
      (types.constructor.constructor types.discriminator) before.world
        ⟨args.profile, account.info⟩ produced) :
    tryAccounts types before args
      ((accountsFocus types).liftOutcome { before with remaining := rest }
        (Outcome.map (Except.map fun _ => Value.mk account) produced)) := by
  simp only [tryAccounts, remaining]
  exact ⟨_, ⟨produced, called, rfl⟩, rfl⟩

def accountsFamily : Family where
  Index := AccountsTypes
  State := AccountsState
  Args := fun _ => AnchorLifecycle.AccountsArgs
  Value := fun types => Except types.constructor.toBase.Error (Value types.constructor.Payload)
  Unwind := fun types => types.constructor.toBase.Unw
  Terminal := fun types => types.constructor.toBase.Term
  contract := fun types => {
    requires := AccountsReady types
    post := fun before args outcome => tryAccounts types before args outcome ∧ AccountsFrame types
      before outcome }

def accountsReference : FamilyRun accountsFamily := tryAccounts
theorem accounts_reference : FamilyReference accountsFamily accountsReference := by
  intro _ _ _ _ _ step
  exact ⟨step, tryAccounts_frame step⟩

def constructorSample : ConstructorTypes where
  Aux := AnchorOwnedSamples.constructor.Aux
  Unwind := AnchorOwnedSamples.constructor.Unwind
  Terminal := AnchorOwnedSamples.constructor.Terminal
  StringResource := AnchorOwnedSamples.constructor.StringResource
  BoxResource := AnchorOwnedSamples.constructor.BoxResource
  errors := AnchorOwnedSamples.constructor.errors
  Payload := Nat
  ownerAt := fun _ _ => .zero
  owner := Callback.ofFunction fun state _ => .returned .zero state

def uncheckedSampleArgs : UncheckedArgs :=
  ⟨AccountInfo.sampleProfile, .zero, sampleReference⟩

theorem constructorSample_ownerReady (before : AnchorAccount.World constructorSample.Aux)
    (args : AccountInfo.Args) (discriminator : Solanalib.Runtime.Bytes) :
    AnchorConstructOwned.OwnerCheckReady (constructorSample.constructor discriminator) before args
      := by
  intro expected after called mismatch
  cases called
  exact False.elim (mismatch rfl)

theorem unchecked_execution :
    FamilyHasExecution uncheckedFamily uncheckedReference constructorSample := by
  refine ⟨(AccountInfo.sampleState, AnchorOwnedSamples.auxiliary), uncheckedSampleArgs,
    .returned (.ok sampleValue) (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary),
    constructorSample_ownerReady _ _ _, ?_⟩
  exact unchecked_matching rfl rfl

def accountsSample : AccountsTypes := ⟨constructorSample, Nat, [10]⟩
def accountsSampleState : AccountsState accountsSample :=
  ⟨(AccountInfo.sampleState, AnchorOwnedSamples.auxiliary), [sampleReference], (17 : Nat), [.zero]⟩
def accountsSampleArgs : AnchorLifecycle.AccountsArgs := ⟨AccountInfo.sampleProfile, .zero, [99]⟩

theorem accounts_execution : FamilyHasExecution accountsFamily accountsReference accountsSample :=
  by
  let during := (AccountInfo.tryBorrowData AccountInfo.sampleState AccountInfo.sampleArgs).2
  let after := (Borrow.release during ⟨0, 0⟩).2
  refine ⟨accountsSampleState, accountsSampleArgs,
    .returned (.ok sampleValue) ⟨(after, AnchorOwnedSamples.auxiliary), [], (17 : Nat), [.zero]⟩,
      ?_, ?_⟩
  · change AnchorConstructOwned.Ready .loader _ _ _
    refine ⟨constructorSample_ownerReady _ _ _, ?_⟩
    intro checked owned
    obtain ⟨expected, ⟨produced, called, widened⟩, _⟩ :=
      AnchorConstructOwned.ownerCheck_returned_ok owned
    cases called
    cases widened
    refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩,
      AccountInfo.sample_valid.2.1, ?_⟩
    intro guard during acquired view bytes current failure selected
    change (Except.ok (⟨0, 0⟩ : Borrow.Guard), _) = (Except.ok guard, during) at acquired
    cases acquired
    change Except.ok (AccountInfo.View.whole, AccountInfo.Content.data [10, 20, 30]) =
      Except.ok (view, .data bytes) at current
    cases current
    change none = some failure at selected
    cases selected
  · refine ⟨_, ⟨.returned (.ok (AnchorAccount.Loader.mk (Payload := Nat) AccountInfo.sampleInfo))
      (after, AnchorOwnedSamples.auxiliary), ?_, rfl⟩, rfl⟩
    refine ⟨.returned (.ok ()) (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary), ?_, ?_⟩
    · exact ⟨.returned .zero _, ⟨.returned .zero _, rfl, rfl⟩, rfl⟩
    · exact ⟨.returned (.ok ()) (after, AnchorOwnedSamples.auxiliary),
        ⟨.returned (.ok ()) (during, AnchorOwnedSamples.auxiliary), rfl, rfl⟩, rfl⟩

end Solanalib.Specs.Core.AnchorLoader
