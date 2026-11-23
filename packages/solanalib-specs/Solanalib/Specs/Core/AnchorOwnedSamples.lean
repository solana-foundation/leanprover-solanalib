/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLoadingOwned
public import Solanalib.Specs.Core.AnchorSplAmountOwned
public import Solanalib.Specs.Core.AnchorErrorOwnedReference

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorOwnedSamples

/-- This inhabited index uses the shared finite error heap and independent
AccountInfo borrow state. The concrete callbacks return a decoded number;
they are model witnesses, not source implementation summaries. -/
def constructor : AnchorConstructOwned.Types where
  Aux := AnchorErrorOwned.Reference.State
  Payload := Nat
  Unwind := String
  Terminal := AnchorErrorOwned.Reference.Failure
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  errors := AnchorErrorOwned.Reference.ops.focus Owned.Focus.snd
  discriminator := [10]
  ownerAt := fun _ _ => .zero
  owner := Callback.ofFunction fun state _ => .returned .zero state
  checkOwner := Callback.ofFunction fun state _ => .returned (.ok ()) state
  deserialize := Callback.ofFunction fun state _ => .returned ⟨.ok 7, []⟩ state

def auxiliary : AnchorErrorOwned.Reference.State := AnchorErrorOwned.Reference.initial 6

theorem owner_check (state : AnchorAccount.World constructor.Aux) :
    AnchorConstructOwned.ownerCheck constructor state AccountInfo.sampleArgs
      (.returned (.ok ()) state) := by
  exact ⟨.returned .zero state, ⟨.returned .zero state, rfl, rfl⟩, rfl⟩

/-- The matching first Owner call of the sample never reaches an error allocation. -/
theorem owner_ready (state : AnchorAccount.World constructor.Aux) (args : AccountInfo.Args) :
    AnchorConstructOwned.OwnerCheckReady constructor state args := by
  intro expected after called mismatch
  cases called
  exact False.elim (mismatch rfl)

/-- Every finite exit of the sample decoder preserves its acquired guard. -/
theorem decode_ready : AnchorConstructOwned.DecodeReady constructor
    (AnchorAccount.sampleAfterInit, auxiliary) AccountInfo.sampleArgs := by
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro guard during acquired view bytes current produced called
  change (Except.ok (⟨1, 0⟩ : Borrow.Guard), AnchorAccount.sampleDataDuring) = (.ok guard, during)
    at acquired
  cases acquired
  cases called
  exact AnchorAccount.sharedDataFrame_refl _ _ AnchorAccount.sampleDataDuring_valid

theorem decode : AnchorConstructOwned.decodeAccount constructor
    (AnchorAccount.sampleAfterInit, auxiliary) AccountInfo.sampleArgs
    (.returned (.ok (7 : Nat)) (AnchorAccount.sampleAfterDecode, auxiliary)) := by
  refine ⟨.returned (.ok (7 : Nat)) (AnchorAccount.sampleDataDuring, auxiliary), ?_, rfl⟩
  exact ⟨.returned ⟨.ok (7 : Nat), []⟩ (AnchorAccount.sampleDataDuring, auxiliary),
    ⟨.returned ⟨.ok (7 : Nat), []⟩ (AnchorAccount.sampleDataDuring, auxiliary), rfl, rfl⟩, rfl⟩

/-- The actual closed sample meets every reached admission condition before
using its finite execution. The successful Loader branch allocates no error. -/
theorem constructor_ready (kind : AnchorAccount.Constructor) :
    AnchorConstructOwned.Ready kind constructor (AccountInfo.sampleState, auxiliary)
      AccountInfo.sampleArgs := by
  cases kind with
  | account =>
    refine ⟨?_, ?_⟩
    · intro _ impossible
      cases impossible
    intro after started
    refine ⟨owner_ready after _, ?_⟩
    intro checked owned
    have same : after = (AnchorAccount.sampleAfterInit, auxiliary) :=
      (Outcome.returned.inj started).2
    cases same
    obtain ⟨expected, ⟨produced, called, widened⟩, _⟩ :=
      AnchorConstructOwned.ownerCheck_returned_ok owned
    change .returned _ (AnchorAccount.sampleAfterInit, auxiliary) = produced at called
    cases called
    cases widened
    exact decode_ready
  | interfaceAccount =>
    refine ⟨?_, ?_⟩
    · intro _ impossible
      cases impossible
    intro after started checked owned
    have same : after = (AnchorAccount.sampleAfterInit, auxiliary) :=
      (Outcome.returned.inj started).2
    cases same
    obtain ⟨produced, called, widened⟩ := owned
    change .returned (.ok ()) (AnchorAccount.sampleAfterInit, auxiliary) = produced at called
    cases called
    cases widened
    exact decode_ready
  | loader =>
    refine ⟨owner_ready _ _, ?_⟩
    intro checked owned
    obtain ⟨expected, ⟨produced, called, widened⟩, _⟩ :=
      AnchorConstructOwned.ownerCheck_returned_ok owned
    change .returned _ (AccountInfo.sampleState, auxiliary) = produced at called
    cases called
    cases widened
    refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩,
      AccountInfo.sample_valid.2.1, ?_⟩
    intro guard during acquired view bytes current failure selected
    change (Except.ok (⟨0, 0⟩ : Borrow.Guard),
      (AccountInfo.tryBorrowData AccountInfo.sampleState AccountInfo.sampleArgs).2) =
        (Except.ok guard, during) at acquired
    cases acquired
    change Except.ok (AccountInfo.View.whole, AccountInfo.Content.data [10, 20, 30]) =
      Except.ok (view, .data bytes) at current
    cases current
    change none = some failure at selected
    cases selected

/-- Every constructor kind has an actual successful execution with its own
source sequence and the closed shared error-heap interpretation. -/
theorem constructor_execution (kind : AnchorAccount.Constructor) :
    FamilyHasExecution (AnchorConstructOwned.family kind)
      (AnchorConstructOwned.reference kind) constructor := by
  cases kind with
  | account =>
    refine ⟨(AccountInfo.sampleState, auxiliary), AccountInfo.sampleArgs,
      .returned (.ok (AnchorAccount.Account.mk (7 : Nat) AccountInfo.sampleInfo))
        (AnchorAccount.sampleAfterDecode, auxiliary), constructor_ready .account, ?_⟩
    refine ⟨.returned (.ok ()) (AnchorAccount.sampleAfterInit, auxiliary), rfl, ?_⟩
    refine ⟨.returned (.ok ()) (AnchorAccount.sampleAfterInit, auxiliary), owner_check _, ?_⟩
    exact ⟨.returned (.ok (7 : Nat)) (AnchorAccount.sampleAfterDecode, auxiliary), decode, rfl⟩
  | interfaceAccount =>
    refine ⟨(AccountInfo.sampleState, auxiliary), AccountInfo.sampleArgs,
      .returned (.ok (AnchorAccount.InterfaceAccount.mk
        ⟨(7 : Nat), AccountInfo.sampleInfo⟩ .zero))
        (AnchorAccount.sampleAfterDecode, auxiliary), constructor_ready .interfaceAccount, ?_⟩
    refine ⟨.returned (.ok ()) (AnchorAccount.sampleAfterInit, auxiliary), rfl, ?_⟩
    refine ⟨.returned (.ok ()) (AnchorAccount.sampleAfterInit, auxiliary),
      ⟨.returned (.ok ()) (AnchorAccount.sampleAfterInit, auxiliary), rfl, rfl⟩, ?_⟩
    exact ⟨.returned (.ok (7 : Nat)) (AnchorAccount.sampleAfterDecode, auxiliary), decode, rfl⟩
  | loader =>
    let during := (AccountInfo.tryBorrowData AccountInfo.sampleState AccountInfo.sampleArgs).2
    let after := (Borrow.release during ⟨0, 0⟩).2
    refine ⟨(AccountInfo.sampleState, auxiliary), AccountInfo.sampleArgs,
      .returned (.ok (AnchorAccount.Loader.mk (Payload := Nat) AccountInfo.sampleInfo))
        (after, auxiliary), constructor_ready .loader, ?_⟩
    refine ⟨.returned (.ok ()) (AccountInfo.sampleState, auxiliary), owner_check _, ?_⟩
    refine ⟨.returned (.ok ()) (after, auxiliary), ?_, rfl⟩
    exact ⟨.returned (.ok ()) (during, auxiliary), rfl, rfl⟩

def loading : AnchorLoadingOwned.Types where
  Aux := AnchorErrorOwned.Reference.State
  Terminal := AnchorErrorOwned.Reference.Failure
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  errors := AnchorErrorOwned.Reference.ops.focus Owned.Focus.snd
  layout := AnchorAccount.loadSample

/-- Successful mapping retains a live new guard generation; it does not
allocate an error or claim that mapped bytes already are a decoded payload. -/
theorem loading_execution (mode : Borrow.Mode) :
    FamilyHasExecution (AnchorLoadingOwned.family mode)
      (AnchorLoadingOwned.reference mode) loading := by
  refine ⟨(AccountInfo.sampleState, auxiliary), AnchorAccount.loadSampleArgs,
    .returned (.ok ⟨⟨0, 1⟩⟩)
      ((Borrow.transfer (AccountInfo.tryBorrow mode AccountInfo.sampleInfo.data
        AccountInfo.sampleState).2 ⟨0, 0⟩ (.bytesRange 1 2)).2, auxiliary),
    by cases mode <;> trivial, ?_⟩
  cases mode <;> rfl

def amount : AnchorSplAmountOwned.Types where
  Aux := AnchorErrorOwned.Reference.State
  Terminal := AnchorErrorOwned.Reference.Failure
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  errors := AnchorErrorOwned.Reference.ops.focus Owned.Focus.snd

theorem amount_execution :
    FamilyHasExecution AnchorSplAmountOwned.family AnchorSplAmountOwned.reference amount := by
  refine ⟨(AnchorSpl.amountSampleState, auxiliary), AccountInfo.sampleArgs,
    .returned (.ok 42)
      ((Borrow.release (AccountInfo.tryBorrowData AnchorSpl.amountSampleState
        AccountInfo.sampleArgs).2 ⟨0, 0⟩).2, auxiliary), trivial, ?_⟩
  rfl

end Solanalib.Specs.Core.AnchorOwnedSamples
