/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleConstructTrace
public import Solanalib.Specs.Core.AnchorLifecyclePayloadSamples

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AnchorLifecycleConstructTrace

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

abbrev Aux := AnchorErrorOwned.Reference.State × Solanalib.Runtime.Pubkey

def checkedOwner : Solanalib.Runtime.Pubkey := ⟨List.replicate 32 2, by decide⟩
def decodedOwner : Solanalib.Runtime.Pubkey := ⟨List.replicate 32 3, by decide⟩

/-- Both callbacks change the observed owner in this mathematical provider.
The decoder also returns the length of the actual current data it receives. -/
def types (storage : AnchorErrorOperations.Storage) : PayloadTypes where
  Aux := Aux
  Unwind := String
  Terminal := AnchorErrorOwned.Reference.Failure
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  Program := ProgramError.Value
  errorStorage := storage
  errors := AnchorErrorOperations.Ops.fromOwned
    (AnchorErrorOwned.Reference.ops.focus (Owned.Focus.snd.comp Owned.Focus.fst))
  programValue := id
  Payload := Nat
  ownerAt := fun state _ => state.2
  owner := Callback.ofFunction fun state _ => .returned state.2.2 state
  checkOwner := Callback.ofFunction fun state _ =>
    .returned (.ok ()) (state.1, (state.2.1, checkedOwner))
  deserialize := Callback.ofFunction fun state args =>
    .returned ⟨.ok args.bytes.length, []⟩ (state.1, (state.2.1, decodedOwner))
  rc := sampleRc

def before : AnchorAccount.World Aux :=
  (AccountInfo.sampleState, (AnchorOwnedSamples.auxiliary, payloadSampleOwner))

def checked (kind : PayloadKind) : AnchorAccount.World Aux :=
  match kind with
  | .account => before
  | .interfaceAccount => (before.1, (before.2.1, checkedOwner))

def after : AnchorAccount.World Aux :=
  (payloadSampleAfter, (AnchorOwnedSamples.auxiliary, decodedOwner))

def result : (kind : PayloadKind) → kind.constructor.Result Nat
  | .account => ⟨3, AccountInfo.sampleInfo⟩
  | .interfaceAccount => ⟨⟨3, AccountInfo.sampleInfo⟩, decodedOwner⟩

theorem decode_calls_current_data (kind : PayloadKind) (storage : InfoStorage)
    (errors : AnchorErrorOperations.Storage) :
    decodePayload storage (types errors) (checked kind) AccountInfo.sampleArgs
      (.returned (.ok (3 : Nat)) after) := by
  have decode (owner : Solanalib.Runtime.Pubkey) :
      decodePayload storage (types errors) (AccountInfo.sampleState, (AnchorOwnedSamples.auxiliary,
        owner))
        AccountInfo.sampleArgs (.returned (.ok (3 : Nat)) after) := by
    refine ⟨.returned (.ok (3 : Nat)) (payloadSampleDuring, (AnchorOwnedSamples.auxiliary,
      decodedOwner)), ?_, rfl⟩
    refine ⟨.returned ⟨.ok (3 : Nat), []⟩ (payloadSampleDuring, (AnchorOwnedSamples.auxiliary,
      decodedOwner)), ?_, rfl⟩
    cases storage with
    | borrowed => exact ⟨_, rfl, rfl⟩
    | owned =>
      refine ⟨.returned AccountInfo.sampleInfo (payloadSampleDuring, (AnchorOwnedSamples.auxiliary,
        owner)), ?_, ?_⟩
      · exact (sampleRc_clone _ _ _ _).mpr rfl
      · exact ⟨_, ⟨_, rfl, rfl⟩, rfl⟩
  cases kind <;> exact decode _

theorem constructor_called (kind : PayloadKind) (storage : InfoStorage)
    (errors : AnchorErrorOperations.Storage) :
    construct kind storage (types errors) before AccountInfo.sampleArgs
      (.returned (.ok (result kind)) after) := by
  refine ⟨.returned (.ok ()) before, ?_, ?_⟩
  · simp only [initialized, types, before, payloadSampleOwner_ne, ↓reduceIte]
  refine ⟨.returned (.ok ()) (checked kind), ?_, ?_⟩
  · cases kind with
    | account => exact ⟨.returned payloadSampleOwner before, ⟨_, rfl, rfl⟩, rfl⟩
    | interfaceAccount => exact ⟨_, rfl, rfl⟩
  · refine ⟨.returned (.ok (3 : Nat)) after, decode_calls_current_data kind storage errors, ?_⟩
    cases kind <;> rfl

/-- The new trace theorem exposes the original input and the actual decoder
exit even when both callbacks change auxiliary state. -/
theorem source_info_retained (kind : PayloadKind) (storage : InfoStorage)
    (errors : AnchorErrorOperations.Storage) :
    (match kind, result kind with
      | .account, value => value.info
      | .interfaceAccount, value => value.account.info) = AccountInfo.sampleInfo := by
  cases kind with
  | account => exact construct_success_info (constructor_called .account storage errors)
  | interfaceAccount => exact construct_success_info (constructor_called .interfaceAccount storage
    errors)

theorem saved_owner_is_decoder_owner (storage : InfoStorage) (errors :
  AnchorErrorOperations.Storage) :
    (result .interfaceAccount).owner = decodedOwner := by
  obtain ⟨_, _, _, _, _, _, saved⟩ := construct_interface_success
    (constructor_called .interfaceAccount storage errors)
  exact saved

/-- Neither the entry owner nor the CheckOwner exit may replace the owner
read after successful decoding. -/
theorem stale_saved_owner_rejected (storage : InfoStorage) (errors : AnchorErrorOperations.Storage)
    (stale : Solanalib.Runtime.Pubkey) (earlier : stale = payloadSampleOwner ∨ stale =
      checkedOwner) :
    ¬ construct .interfaceAccount storage (types errors) before AccountInfo.sampleArgs
      (.returned (.ok ⟨⟨(3 : Nat), AccountInfo.sampleInfo⟩, stale⟩) after) := by
  intro called
  obtain ⟨_, _, _, _, _, _, saved⟩ := construct_interface_success called
  change stale = decodedOwner at saved
  rcases earlier with rfl | rfl
  · exact (by decide : payloadSampleOwner ≠ decodedOwner) saved
  · exact (by decide : checkedOwner ≠ decodedOwner) saved

theorem different_input_record_rejected (storage : InfoStorage) (errors :
  AnchorErrorOperations.Storage) :
    ¬ construct .account storage (types errors) before AccountInfo.sampleArgs
      (.returned (.ok ⟨(3 : Nat), { AccountInfo.sampleInfo with key := decodedOwner }⟩) after) := by
  intro called
  obtain ⟨_, _, _, _, _, same⟩ := construct_account_success called
  have key := congrArg AccountInfo.Value.key same
  exact (by decide : decodedOwner ≠ AccountInfo.sampleInfo.key) key

end SolanalibTest.Specs.Core.AnchorLifecycleConstructTrace
