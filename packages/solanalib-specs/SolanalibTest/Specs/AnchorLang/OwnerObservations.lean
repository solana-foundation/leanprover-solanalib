/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.construct

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

set_option maxRecDepth 4096

namespace SolanalibTest.Specs.AnchorLang.OwnerObservations

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount

/-- Only owner-reference zero changes in this small auxiliary world. It is a
mathematical owner store, not a claimed implementation of AccountInfo::assign. -/
def ownerAt : AccountInfo.OwnerAt Nat := fun state reference =>
  if reference.id = 0 then .ofNat state else .zero

def decoder (state : World Nat) (_ : DecodeArgs) :
    Outcome (World Nat) (Decoded Nat) String String :=
  .returned ⟨.ok 7, []⟩ (state.1, 9)

def index : ConstructorIndex where
  Aux := Nat
  Payload := Nat
  Unwind := String
  Terminal := String
  discriminator := [10]
  ownerAt := ownerAt
  owner := Callback.ofFunction (fun state _ => .returned (.ofNat 9) state)
  checkOwner := Callback.ofFunction (fun state reference => .returned
    (if ownerAt state.2 reference = .zero then .ok ()
      else .error (error .ownedByWrongProgram)) state)
  deserialize := Callback.ofFunction decoder

/-- The owner assignment of the decoder changes only the auxiliary world, so every
finite exit preserves its actual held data lease and bytes. -/
theorem decoder_ready : DecodeReady index (sampleAfterInit, (0 : Nat)) AccountInfo.sampleArgs := by
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro guard during acquired view bytes current produced called
  change (Except.ok (⟨1, 0⟩ : Borrow.Guard), sampleDataDuring) = (.ok guard, during) at acquired
  cases acquired
  cases called
  exact sharedDataFrame_refl _ _ sampleDataDuring_valid

/-- The registered interface family checks admission after initialization and
the actual CheckOwner return, before it runs this owner-changing decoder. -/
theorem interface_ready :
    ((constructorFamily .interfaceAccount).contract index).requires
      (AccountInfo.sampleState, (0 : Nat)) AccountInfo.sampleArgs := by
  refine ⟨?_, ?_⟩
  · intro _ impossible
    cases impossible
  intro after started checked owned
  change (some (.returned (.ok ()) (sampleAfterInit, (0 : Nat))) :
    Option (Outcome (World Nat) (Except Error Unit) (ConstructorUnwind String)
      (ConstructorTerminal String))) = some (.returned (.ok ()) after) at started
  cases started
  obtain ⟨produced, called, widened⟩ := owned
  change .returned (.ok ()) (sampleAfterInit, (0 : Nat)) = produced at called
  cases called
  cases widened
  exact decoder_ready

theorem decoder_changes_owner :
    decodeAccount index (sampleAfterInit, (0 : Nat)) AccountInfo.sampleArgs
      (.returned (.ok (7 : Nat)) (sampleAfterDecode, (9 : Nat))) := by
  exact ⟨.returned ⟨.ok (7 : Nat), []⟩ (sampleDataDuring, (9 : Nat)), rfl, rfl⟩

/-- InterfaceAccount::new reads the owner after the codec has changed it. The
stored AccountInfo observation stays the original snapshot; its reference still
points to the owner whose current value is nine. -/
theorem interface_records_post_decoder_owner :
    construct .interfaceAccount index (AccountInfo.sampleState, (0 : Nat))
      AccountInfo.sampleArgs
      (.returned (.ok (InterfaceAccount.mk ⟨(7 : Nat), AccountInfo.sampleInfo⟩ (.ofNat 9)))
        (sampleAfterDecode, (9 : Nat))) := by
  have checked : widenCallback index.checkOwner (sampleAfterInit, (0 : Nat))
      AccountInfo.sampleInfo.ownerRef (.returned (.ok ()) (sampleAfterInit, (0 : Nat))) :=
    ⟨.returned (.ok ()) (sampleAfterInit, (0 : Nat)), rfl, rfl⟩
  obtain ⟨decoded, released, retained⟩ := constructor_interface_retain
    interface_ready rfl checked rfl rfl
    (show index.deserialize (sampleDataDuring, (0 : Nat))
      ⟨AccountInfo.sampleInfo, ⟨1, 0⟩, [10, 20, 30]⟩
      (.returned ⟨.ok (7 : Nat), []⟩ (sampleDataDuring, (9 : Nat))) from rfl)
  change some (Outcome.returned (Except.ok (7 : Nat)) (sampleAfterDecode, (9 : Nat))) =
    some decoded at released
  cases released
  exact retained

/-- A later Owner check on the retained alias sees the changed value, even
though the stored owner observation of the alias remains zero. -/
theorem later_owner_check_uses_current_state :
    ownerCheck index (sampleAfterDecode, (9 : Nat))
      ⟨AccountInfo.sampleProfile, AccountInfo.clone AccountInfo.sampleInfo⟩
      (.returned (.ok ()) (sampleAfterDecode, (9 : Nat))) ∧
    (AccountInfo.clone AccountInfo.sampleInfo).owner = .zero := by
  constructor
  · exact ⟨.returned (.ofNat 9) (sampleAfterDecode, (9 : Nat)),
      ⟨.returned (.ofNat 9) (sampleAfterDecode, (9 : Nat)), rfl, rfl⟩, rfl⟩
  · rfl

/-- A changed, nonsystem owner bypasses the lamports read even when the old
entry observation was the system address. -/
theorem initialization_reads_current_owner :
    initialized (Unwind := String) (Terminal := String) ownerAt
      (AccountInfo.sampleState, (9 : Nat)) AccountInfo.sampleArgs =
      some (.returned (.ok ()) (AccountInfo.sampleState, (9 : Nat))) := rfl

def withOwner (callback : Callback.Run (World Nat) Unit _root_.Solanalib.Runtime.Pubkey String
  String) :
    ConstructorIndex where
  Aux := Nat
  Payload := Nat
  Unwind := String
  Terminal := String
  discriminator := [10]
  ownerAt := ownerAt
  owner := callback
  checkOwner := index.checkOwner
  deserialize := index.deserialize

def matchingOwner : ConstructorIndex := withOwner
  (Callback.ofFunction (fun state _ =>
    .returned (.ofNat (state.2 + 1)) (state.1, state.2 + 1)))

/-- The comparison dereferences its left operand after the callback of Owner, so
an assignment performed by that callback affects the very same comparison. -/
theorem comparison_reads_after_owner_callback (state : AccountInfo.State) :
    ownerCheck matchingOwner (state, (0 : Nat)) AccountInfo.sampleArgs
      (.returned (.ok ()) (state, (1 : Nat))) := by
  refine ⟨.returned (.ofNat 1) (state, (1 : Nat)),
    ⟨.returned (.ofNat 1) (state, (1 : Nat)), rfl, rfl⟩, ?_⟩
  simp [matchingOwner, withOwner, ownerAt, AccountInfo.sampleArgs, AccountInfo.sampleInfo]

def mismatchingOwner : ConstructorIndex := withOwner
  (Callback.ofFunction (fun state _ =>
    .returned (.ofNat 99) (state.1, state.2 + 1)))

/-- The diagnostic tuple copies the observed key before its second callback.
The final owner is two, but the copied left key of the diagnostic remains one. -/
theorem diagnostic_keeps_pre_second_callback_key (state : AccountInfo.State) :
    ownerCheck mismatchingOwner (state, (0 : Nat)) AccountInfo.sampleArgs
      (.returned (.error ((error .ownedByWrongProgram).replaceCompared
        (.pubkeys (.ofNat 1) (.ofNat 99)))) (state, (2 : Nat))) := by
  refine ⟨.returned (.ofNat 99) (state, (1 : Nat)),
    ⟨.returned (.ofNat 99) (state, (1 : Nat)), rfl, rfl⟩, ?_⟩
  have different : _root_.Solanalib.Runtime.Pubkey.ofNat 1 ≠ .ofNat 99 := by decide
  simp only [mismatchingOwner, withOwner, ownerAt, AccountInfo.sampleArgs,
    AccountInfo.sampleInfo, ite_eq_left, different, ite_false]
  exact ⟨.returned (.ofNat 99) (state, (2 : Nat)),
    ⟨.returned (.ofNat 99) (state, (2 : Nat)), rfl, rfl⟩, rfl⟩

def observingCheckOwner : ConstructorIndex where
  Aux := Nat
  Payload := Nat
  Unwind := String
  Terminal := String
  discriminator := [10]
  ownerAt := ownerAt
  owner := index.owner
  checkOwner := Callback.ofFunction (fun state reference =>
    let after : World Nat := (state.1, state.2 + 1)
    .returned
      (if ownerAt after.2 reference = .ofNat 1 then .ok ()
        else .error (error .ownedByWrongProgram)) after)
  deserialize := index.deserialize

/-- CheckOwner receives a reference identity, so reads inside its own callback
also observe assignments made during that callback. -/
theorem check_owner_receives_reference (state : AccountInfo.State) :
    observingCheckOwner.checkOwner (state, (0 : Nat)) AccountInfo.sampleInfo.ownerRef
      (.returned (.ok ()) (state, (1 : Nat))) := by
  simp [observingCheckOwner, Callback.ofFunction, ownerAt, AccountInfo.sampleInfo]

/-- Equal entry observations do not collapse different owner references. -/
theorem distinct_owner_references :
    AccountInfo.sampleInfo.owner =
      ({ AccountInfo.sampleInfo with ownerRef := ⟨1⟩ } : AccountInfo.Value).owner ∧
    ownerAt 9 AccountInfo.sampleInfo.ownerRef = .ofNat 9 ∧
    ownerAt 9 ({ AccountInfo.sampleInfo with ownerRef := ⟨1⟩ } : AccountInfo.Value).ownerRef =
      .zero := ⟨rfl, rfl, rfl⟩

end SolanalibTest.Specs.AnchorLang.OwnerObservations
