/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecyclePayloadSamples

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World)

abbrev ReloadSampleAux := AnchorErrorOwned.Reference.State × Nat

def reloadSample (errors : AnchorErrorOperations.Storage) : ReloadTypes where
  Aux := ReloadSampleAux
  Unwind := String
  Terminal := AnchorErrorOwned.Reference.Failure
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  Program := ProgramError.Value
  errorStorage := errors
  errors := AnchorErrorOperations.Ops.fromOwned
    (AnchorErrorOwned.Reference.ops.focus (Owned.Focus.snd.comp Owned.Focus.fst))
  programValue := id
  Payload := Nat
  ownerAt := fun _ _ => payloadSampleOwner
  owner := Callback.ofFunction fun state _ => .returned payloadSampleOwner state
  checkOwner := Callback.ofFunction fun state _ => .returned (.ok ()) state
  deserialize := Callback.ofFunction fun state _ => .returned ⟨.ok 7, []⟩ state
  rc := sampleRc
  payload := Owned.Focus.snd.comp Owned.Focus.snd
  dropPayload := Callback.ofFunction fun state _ => .returned () state

def reloadSampleAux : ReloadSampleAux := (AnchorOwnedSamples.auxiliary, 2)

theorem reloadSample_replace (errors : AnchorErrorOperations.Storage)
    (state : World ReloadSampleAux) (replacement : Nat)
    (outcome : Outcome (World ReloadSampleAux) Unit
      (reloadSample errors).toPayloadTypes.toBase.Unw (reloadSample
        errors).toPayloadTypes.toBase.Term) :
    replacePayload (reloadSample errors) state replacement outcome ↔
      outcome = .returned () (state.1, (state.2.1, replacement)) := by
  simp [replacePayload, AnchorViewsAssignment.run, AnchorViewsAssignment.replaceAfter,
    reloadSample, AnchorAccount.widenCallback, AnchorAccount.widen, Callback.ofFunction,
    Owned.Focus.comp, Owned.Focus.snd]
  exact eq_comm

theorem reloadSample_decodeReplaceReady (errors : AnchorErrorOperations.Storage) :
    DecodeReplaceReady (reloadSample errors) (AccountInfo.sampleState, reloadSampleAux)
      AccountInfo.sampleArgs := by
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro guard during acquired view bytes current
  change (Except.ok (⟨0, 0⟩ : Borrow.Guard), payloadSampleDuring) = (.ok guard, during) at acquired
  cases acquired
  refine ⟨?_, ?_⟩
  · rintro _ ⟨_, called, rfl⟩
    cases called
    exact AnchorAccount.sharedDataFrame_refl _ _ payloadSampleDuring_valid
  · rintro decoded after ⟨_, called, widened⟩ replacement selected
    cases called
    cases widened
    cases selected
    intro outcome replaced
    have equal := (reloadSample_replace errors _ _ _).mp replaced
    subst outcome
    exact AnchorAccount.sharedDataFrame_refl _ _ payloadSampleDuring_valid

theorem reloadSample_decodePayloadReady (errors : AnchorErrorOperations.Storage) :
    DecodePayloadReady .borrowed (reloadSample errors).toPayloadTypes
      (AccountInfo.sampleState, reloadSampleAux) AccountInfo.sampleArgs := by
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro guard during acquired view bytes current
  change (Except.ok (⟨0, 0⟩ : Borrow.Guard), payloadSampleDuring) = (.ok guard, during) at acquired
  cases acquired
  rintro _ ⟨_, called, rfl⟩
  cases called
  exact AnchorAccount.sharedDataFrame_refl _ _ payloadSampleDuring_valid

theorem reloadSample_ready (mode : ReloadMode) (errors : AnchorErrorOperations.Storage) :
    ReloadReady mode (reloadSample errors) (AccountInfo.sampleState, reloadSampleAux)
      AccountInfo.sampleArgs := by
  cases mode with
  | legacy => exact reloadSample_decodeReplaceReady errors
  | account =>
    refine ⟨?_, ?_⟩
    · intro _ expected after called mismatch
      cases called
      exact False.elim (mismatch rfl)
    · intro checked called
      obtain ⟨_, ⟨_, owner, widened⟩, _⟩ := ownerCheck_ok called
      cases owner; cases widened
      exact reloadSample_decodeReplaceReady errors
  | interfaceAccount =>
    rintro checked ⟨_, called, widened⟩
    cases called; cases widened
    exact reloadSample_decodePayloadReady errors

theorem reloadSample_decodeReplace (errors : AnchorErrorOperations.Storage) :
    decodeReplace (reloadSample errors) (AccountInfo.sampleState, reloadSampleAux)
      AccountInfo.sampleArgs
      (.returned (.ok ()) (payloadSampleAfter, (AnchorOwnedSamples.auxiliary, (7 : Nat)))) := by
  refine ⟨.returned (.ok ()) (payloadSampleDuring, (AnchorOwnedSamples.auxiliary, (7 : Nat))), ?_,
    rfl⟩
  refine ⟨.returned (.ok (7 : Nat)) (payloadSampleDuring, reloadSampleAux), ?_, ?_⟩
  · exact ⟨_, ⟨_, rfl, rfl⟩, rfl⟩
  · exact ⟨_, (reloadSample_replace errors _ _ _).mpr rfl, rfl⟩

theorem reloadSample_decodePayload (errors : AnchorErrorOperations.Storage) :
    decodePayload .borrowed (reloadSample errors).toPayloadTypes
      (AccountInfo.sampleState, reloadSampleAux) AccountInfo.sampleArgs
      (.returned (.ok (7 : Nat)) (payloadSampleAfter, reloadSampleAux)) := by
  exact ⟨.returned (.ok (7 : Nat)) (payloadSampleDuring, reloadSampleAux),
    ⟨_, ⟨_, rfl, rfl⟩, rfl⟩, rfl⟩

theorem reload_execution (mode : ReloadMode) (errors : AnchorErrorOperations.Storage) :
    FamilyHasExecution (reloadFamily mode) (reloadRun mode) (reloadSample errors) := by
  refine ⟨(AccountInfo.sampleState, reloadSampleAux), AccountInfo.sampleArgs,
    .returned (.ok ()) (payloadSampleAfter, (AnchorOwnedSamples.auxiliary, (7 : Nat))),
    reloadSample_ready mode errors, ?_⟩
  cases mode with
  | legacy => exact reloadSample_decodeReplace errors
  | account =>
    refine ⟨.returned (.ok ()) (AccountInfo.sampleState, reloadSampleAux), ?_,
      reloadSample_decodeReplace errors⟩
    exact ⟨.returned payloadSampleOwner (AccountInfo.sampleState, reloadSampleAux), ⟨_, rfl, rfl⟩,
      rfl⟩
  | interfaceAccount =>
    refine ⟨.returned (.ok ()) (AccountInfo.sampleState, reloadSampleAux), ⟨_, rfl, rfl⟩, ?_⟩
    exact ⟨.returned (.ok (7 : Nat)) (payloadSampleAfter, reloadSampleAux),
      reloadSample_decodePayload errors, _, (reloadSample_replace errors _ _ _).mpr rfl, rfl⟩

end Solanalib.Specs.Core.AnchorLifecycle
