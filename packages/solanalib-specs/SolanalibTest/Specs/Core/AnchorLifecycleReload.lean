/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleProfiles

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AnchorLifecycleReload

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

abbrev Aux := AnchorErrorOwned.Reference.State × (Nat × Bool)

/-- This legal destructor attempts a mutable borrow of the same account data.
It records whether that borrow succeeded, writes on success and can unwind
afterward. Thus guard lifetime is observable independently of replacement. -/
def probe (unwinds : Bool) : ReloadTypes where
  Aux := Aux
  Unwind := String
  Terminal := AnchorErrorOwned.Reference.Failure
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  Program := ProgramError.Value
  errorStorage := .boxed
  errors := AnchorErrorOperations.Ops.fromOwned
    (AnchorErrorOwned.Reference.ops.focus (Owned.Focus.snd.comp Owned.Focus.fst))
  programValue := id
  Payload := Nat
  ownerAt := fun _ _ => payloadSampleOwner
  owner := Callback.ofFunction fun state _ => .returned payloadSampleOwner state
  checkOwner := Callback.ofFunction fun state _ => .returned (.ok ()) state
  deserialize := Callback.ofFunction fun state _ => .returned ⟨.ok 7, []⟩ state
  rc := sampleRc
  payload := Owned.Focus.snd.comp (Owned.Focus.snd.comp Owned.Focus.fst)
  dropPayload := Callback.ofFunction fun state _ =>
    let (borrowed, during) := AccountInfo.tryBorrowMutData state.1 AccountInfo.sampleArgs
    let (data, succeeded) := match borrowed with
      | .error _ => (during, false)
      | .ok guard => ((Borrow.release (Borrow.write during guard (.data [99, 20, 30])).2 guard).2,
        true)
    let after := (data, (state.2.1, (state.2.2.1, succeeded)))
    if unwinds then .unwound "old payload drop" after else .returned () after

def auxiliary : Aux := (AnchorOwnedSamples.auxiliary, (2, false))
def before : AnchorAccount.World Aux := (AccountInfo.sampleState, auxiliary)
def during : AnchorAccount.World Aux := (payloadSampleDuring, auxiliary)
def afterAccount : AnchorAccount.World Aux :=
  (payloadSampleAfter, (AnchorOwnedSamples.auxiliary, (7, false)))
def afterInterface : AnchorAccount.World Aux :=
  (⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data [99, 20, 30], AccountInfo.sampleProfile.policy⟩], [none, none]⟩,
    (AnchorOwnedSamples.auxiliary, (7, true)))

theorem account_probe_admitted (unwinds : Bool) :
    ReloadReady .account (probe unwinds) before AccountInfo.sampleArgs := by
  refine ⟨?_, ?_⟩
  · intro _ expected after called mismatch
    cases called
    exact False.elim (mismatch rfl)
  intro checked owned
  obtain ⟨_, ⟨_, called, widened⟩, _⟩ := ownerCheck_ok owned
  cases called; cases widened
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro guard borrowState acquired view bytes current
  change (Except.ok (⟨0, 0⟩ : Borrow.Guard), payloadSampleDuring) = (.ok guard, borrowState)
    at acquired
  cases acquired
  refine ⟨?_, ?_⟩
  · rintro _ ⟨_, called, widened⟩
    cases called; cases widened
    exact AnchorAccount.sharedDataFrame_refl _ _ payloadSampleDuring_valid
  · rintro decoded after ⟨_, called, widened⟩ replacement selected
    cases called; cases widened; cases selected
    rintro outcome ⟨dropped, ⟨raw, droppedCall, droppedWidened⟩, installed⟩
    cases unwinds <;> cases droppedCall <;> cases droppedWidened <;> cases installed <;>
      exact AnchorAccount.sharedDataFrame_refl _ _ payloadSampleDuring_valid

theorem interface_probe_admitted (unwinds : Bool) :
    ReloadReady .interfaceAccount (probe unwinds) before AccountInfo.sampleArgs := by
  rintro checked ⟨_, called, widened⟩
  cases called; cases widened
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro guard borrowState acquired view bytes current
  change (Except.ok (⟨0, 0⟩ : Borrow.Guard), payloadSampleDuring) = (.ok guard, borrowState)
    at acquired
  cases acquired
  rintro _ ⟨_, called, widened⟩
  cases called; cases widened
  exact AnchorAccount.sharedDataFrame_refl _ _ payloadSampleDuring_valid

theorem account_drop_sees_shared_guard :
    reload .account (probe false) before AccountInfo.sampleArgs
      (.returned (.ok ()) afterAccount) := by
  refine ⟨.returned (.ok ()) before,
    ⟨.returned payloadSampleOwner before, ⟨_, rfl, rfl⟩, rfl⟩, ?_⟩
  refine ⟨.returned (.ok ()) (during.1, (AnchorOwnedSamples.auxiliary, ((7 : Nat), false))), ?_,
    rfl⟩
  refine ⟨.returned (.ok (7 : Nat)) during, ⟨_, ⟨_, rfl, rfl⟩, rfl⟩,
    .returned () (during.1, (AnchorOwnedSamples.auxiliary, ((7 : Nat), false))), ?_, rfl⟩
  exact ⟨.returned () during, ⟨_, rfl, rfl⟩, rfl⟩

theorem interface_drop_sees_released_guard :
    reload .interfaceAccount (probe false) before AccountInfo.sampleArgs
      (.returned (.ok ()) afterInterface) := by
  refine ⟨.returned (.ok ()) before, ⟨_, rfl, rfl⟩,
    .returned (.ok (7 : Nat)) (payloadSampleAfter, auxiliary), ?_, ?_⟩
  · exact ⟨.returned (.ok (7 : Nat)) during, ⟨_, ⟨_, rfl, rfl⟩, rfl⟩, rfl⟩
  · refine ⟨.returned () afterInterface, ?_, rfl⟩
    exact ⟨.returned () (afterInterface.1, (AnchorOwnedSamples.auxiliary, ((2 : Nat), true))),
      ⟨_, rfl, rfl⟩, rfl⟩

theorem old_drop_unwind_still_installs_replacement :
    reload .account (probe true) before AccountInfo.sampleArgs
      (.unwound (.inr "old payload drop") afterAccount) := by
  refine ⟨.returned (.ok ()) before,
    ⟨.returned payloadSampleOwner before, ⟨_, rfl, rfl⟩, rfl⟩, ?_⟩
  refine ⟨.unwound (.inr "old payload drop")
    (during.1, (AnchorOwnedSamples.auxiliary, ((7 : Nat), false))), ?_, rfl⟩
  refine ⟨.returned (.ok (7 : Nat)) during, ⟨_, ⟨_, rfl, rfl⟩, rfl⟩,
    .unwound (.inr "old payload drop")
      (during.1, (AnchorOwnedSamples.auxiliary, ((7 : Nat), false))), ?_, rfl⟩
  exact ⟨.unwound (.inr "old payload drop") during, ⟨_, rfl, rfl⟩, rfl⟩

theorem replacement_and_data_observations :
    afterAccount.2.2 = (7, false) ∧ afterInterface.2.2 = (7, true) ∧
    (afterAccount.1.lookupCell AccountInfo.sampleInfo.data).map Borrow.Cell.value = some (.data
      [10, 20, 30]) ∧
    (afterInterface.1.lookupCell AccountInfo.sampleInfo.data).map Borrow.Cell.value = some (.data
      [99, 20, 30]) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def invalidClone : Callback.Run (AnchorAccount.World Unit)
    (AccountInfoRc.Field × Borrow.Handle) Unit Empty String :=
  Callback.ofFunction fun state (field, _) => match field with
    | .lamports => .returned () ({ state.1 with slots := [] }, ())
    | .data => .terminated "second clone never returns"

theorem first_rc_frame_required_even_when_second_terminates :
    ¬ RcReady invalidClone (payloadSampleDuring, ()) AccountInfo.sampleInfo ⟨0, 0⟩ := by
  intro ready
  have frame := ready.1 (.returned () ({ payloadSampleDuring with slots := [] }, ())) rfl
  have held := frame.held
  change (none : Option (Borrow.Slot AccountInfo.View)) = some ⟨⟨1⟩, .shared, 0, .whole⟩ at held
  cases held

end SolanalibTest.Specs.Core.AnchorLifecycleReload
