/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecyclePayloadFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World)

/-- Finite scheduling witnesses only. Source Rc counts remain supplied by the
selected dependency interpretation, never by this sample provider. -/
def sampleRc {State Terminal : Type} : AccountInfoRc.Ops State Terminal where
  cloneRc := Callback.ofFunction fun state _ => .returned () state
  dropRc := Callback.ofFunction fun state _ => .returned () state

@[simp] theorem sampleRc_clone (base : Base) (before : World base.Aux) (info : AccountInfo.Value)
    (outcome : Outcome (World base.Aux) AccountInfo.Value base.Unw base.Term) :
    cloneInfo base sampleRc before info outcome ↔ outcome = .returned info before := by
  simp [cloneInfo, dependency, AccountInfoRc.cloneCall, sampleRc, Callback.ofFunction,
    Callback.bind, Callback.map, AccountInfoRc.lift, AccountInfoRc.liftOutcome,
    AnchorAccount.widenCallback, AnchorAccount.widen, Outcome.map, AccountInfo.clone, eq_comm]

@[simp] theorem sampleRc_drop (base : Base) (before : World base.Aux) (info : AccountInfo.Value)
    (outcome : Outcome (World base.Aux) Unit base.Unw base.Term) :
    dropInfo base sampleRc info before outcome ↔ outcome = .returned () before := by
  simp [dropInfo, dependency, AccountInfoRc.dropCall, sampleRc, Callback.ofFunction,
    Callback.bind, AccountInfoRc.lift, AccountInfoRc.liftOutcome,
    AnchorAccount.widenCallback, AnchorAccount.widen, eq_comm]

def payloadSampleOwner : Solanalib.Runtime.Pubkey := ⟨List.replicate 32 1, by decide⟩

theorem payloadSampleOwner_ne : payloadSampleOwner ≠ AnchorAccount.systemProgramId := by decide

def payloadSample (errorStorage : AnchorErrorOperations.Storage) : PayloadTypes where
  toBase := { Base.ofConstructor AnchorOwnedSamples.constructor with errorStorage := errorStorage }
  Payload := Nat
  ownerAt := fun _ _ => payloadSampleOwner
  owner := Callback.ofFunction fun state _ => .returned payloadSampleOwner state
  checkOwner := Callback.ofFunction fun state _ => .returned (.ok ()) state
  deserialize := Callback.ofFunction fun state _ => .returned ⟨.ok 7, []⟩ state
  rc := sampleRc

def payloadSampleDuring : AccountInfo.State :=
  (AccountInfo.tryBorrowData AccountInfo.sampleState AccountInfo.sampleArgs).2

def payloadSampleAfter : AccountInfo.State :=
  (Borrow.release payloadSampleDuring ⟨0, 0⟩).2

theorem payloadSampleDuring_valid : payloadSampleDuring.Valid := by
  change (Borrow.acquire AccountInfo.sampleState AccountInfo.sampleInfo.data .shared
    AccountInfo.View.whole).2.Valid
  exact Borrow.acquire_valid AccountInfo.sample_valid.2.1 _ _ _

theorem payloadSample_initialized (errors : AnchorErrorOperations.Storage)
    (state : World (payloadSample errors).Aux) :
    initialized (payloadSample errors) state AccountInfo.sampleArgs (.returned (.ok ()) state) := by
  simp only [initialized, payloadSample, payloadSampleOwner_ne, ↓reduceIte]

theorem payloadSample_owner (errors : AnchorErrorOperations.Storage)
    (state : World (payloadSample errors).Aux) :
    ownerCheck (payloadSample errors) state AccountInfo.sampleArgs (.returned (.ok ()) state) := by
  exact ⟨.returned payloadSampleOwner state, ⟨.returned payloadSampleOwner state, rfl, rfl⟩, rfl⟩

theorem payloadSample_ownerReady (errors : AnchorErrorOperations.Storage)
    (state : World (payloadSample errors).Aux) :
    OwnerReady (payloadSample errors) state AccountInfo.sampleArgs := by
  intro _ expected after called mismatch
  cases called
  exact False.elim (mismatch rfl)

theorem payloadSample_decodeReady (storage : InfoStorage) (errors : AnchorErrorOperations.Storage) :
    DecodePayloadReady storage (payloadSample errors)
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) AccountInfo.sampleArgs := by
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro guard during acquired view bytes current
  change (Except.ok (⟨0, 0⟩ : Borrow.Guard), payloadSampleDuring) = (.ok guard, during) at acquired
  cases acquired
  have frame {Value Unwind Terminal : Type} (value : Value) :
      AccountInfo.GuardCallback.Frame (payloadSampleDuring, AnchorOwnedSamples.auxiliary) ⟨0, 0⟩
        (.returned value (payloadSampleDuring, AnchorOwnedSamples.auxiliary) :
          Outcome _ Value Unwind Terminal) :=
    AnchorAccount.sharedDataFrame_refl _ _ payloadSampleDuring_valid
  cases storage with
  | borrowed =>
    rintro _ ⟨_, called, rfl⟩
    cases called
    exact frame _
  | owned =>
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro _ called; cases called; exact frame _
    · intro middle called; cases called
      intro _ called; cases called; exact frame _
    intro info afterClone cloned
    have equal := (sampleRc_clone _ _ _ _).mp cloned
    cases equal
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, called, rfl⟩; cases called; exact frame _
    · rintro _ ⟨_, called, rfl⟩; cases called; trivial

theorem payloadSample_ready (kind : PayloadKind) (storage : InfoStorage)
    (errors : AnchorErrorOperations.Storage) :
    ConstructReady kind storage (payloadSample errors)
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) AccountInfo.sampleArgs := by
  refine ⟨?_, ?_⟩
  · intro system
    exact False.elim (payloadSampleOwner_ne system)
  intro after started
  have same : after = (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) := by
    have same : (.returned (.ok ()) after : Outcome _ (Except (payloadSample errors).toBase.Error
      Unit)
        (payloadSample errors).toBase.Unw (payloadSample errors).toBase.Term) =
        .returned (.ok ()) (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) := by
      simpa only [initialized, payloadSample, payloadSampleOwner_ne, ↓reduceIte] using started
    exact (Outcome.returned.inj same).2
  subst after
  cases kind with
  | account =>
    refine ⟨payloadSample_ownerReady errors _, ?_⟩
    intro checked owned
    obtain ⟨_, ⟨_, called, widened⟩, _⟩ := ownerCheck_ok owned
    cases called; cases widened
    exact payloadSample_decodeReady storage errors
  | interfaceAccount =>
    rintro checked ⟨_, called, widened⟩
    cases called; cases widened
    exact payloadSample_decodeReady storage errors

theorem payloadSample_decode (storage : InfoStorage) (errors : AnchorErrorOperations.Storage) :
    decodePayload storage (payloadSample errors)
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) AccountInfo.sampleArgs
      (.returned (.ok (7 : Nat)) (payloadSampleAfter, AnchorOwnedSamples.auxiliary)) := by
  refine ⟨.returned (.ok (7 : Nat)) (payloadSampleDuring, AnchorOwnedSamples.auxiliary), ?_, rfl⟩
  refine ⟨.returned ⟨.ok (7 : Nat), []⟩ (payloadSampleDuring, AnchorOwnedSamples.auxiliary), ?_,
    rfl⟩
  cases storage with
  | borrowed => exact ⟨_, rfl, rfl⟩
  | owned =>
    refine ⟨.returned AccountInfo.sampleInfo (payloadSampleDuring, AnchorOwnedSamples.auxiliary),
      ?_, ?_⟩
    · exact (sampleRc_clone _ _ _ _).mpr rfl
    · exact ⟨_, ⟨_, rfl, rfl⟩, rfl⟩

def payloadSampleValue : (kind : PayloadKind) → kind.constructor.Result Nat
  | .account => ⟨7, AccountInfo.sampleInfo⟩
  | .interfaceAccount => ⟨⟨7, AccountInfo.sampleInfo⟩, payloadSampleOwner⟩

theorem payload_execution (kind : PayloadKind) (storage : InfoStorage)
    (errors : AnchorErrorOperations.Storage) :
    FamilyHasExecution (payloadFamily kind storage) (payloadRun kind storage) (payloadSample
      errors) := by
  refine ⟨(AccountInfo.sampleState, AnchorOwnedSamples.auxiliary), AccountInfo.sampleArgs,
    .returned (.ok (payloadSampleValue kind)) (payloadSampleAfter, AnchorOwnedSamples.auxiliary),
    payloadSample_ready kind storage errors, ?_⟩
  refine ⟨.returned (.ok ()) (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary),
    payloadSample_initialized errors _, ?_⟩
  refine ⟨.returned (.ok ()) (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary), ?_, ?_⟩
  · cases kind
    · exact payloadSample_owner errors _
    · exact ⟨_, rfl, rfl⟩
  · refine ⟨.returned (.ok (7 : Nat)) (payloadSampleAfter, AnchorOwnedSamples.auxiliary),
      payloadSample_decode storage errors, ?_⟩
    cases kind <;> rfl

def payloadAccountsSample (errors : AnchorErrorOperations.Storage) : PayloadAccountsTypes :=
  ⟨payloadSample errors, Unit⟩

theorem payloadAccounts_execution (kind : PayloadKind) (storage : InfoStorage)
    (errors : AnchorErrorOperations.Storage) :
    FamilyHasExecution (payloadAccountsFamily kind storage) (payloadAccountsRun kind storage)
      (payloadAccountsSample errors) := by
  obtain ⟨before, args, outcome, admitted, called⟩ := payload_execution kind storage errors
  exact ⟨(before, ⟨[⟨19, args.info⟩], (), []⟩), ⟨args.profile, .zero, []⟩,
    Owned.Focus.fst.liftOutcome (before, (⟨[], (), []⟩ : AccountsState Unit)) outcome,
    admitted, outcome, called, rfl⟩

end Solanalib.Specs.Core.AnchorLifecycle
