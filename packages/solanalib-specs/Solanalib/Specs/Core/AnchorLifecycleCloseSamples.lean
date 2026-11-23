/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleCloseFacts
public import Solanalib.Specs.Core.AnchorLifecyclePayloadSamples

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World)

abbrev CloseSampleMeta := List Solanalib.Runtime.Pubkey × List (Option AccountInfoSdk.Buffer)
abbrev CloseSampleAux := CloseSampleMeta × AnchorErrorOwned.Reference.State

/-- A lawful view of the shared borrow state and SDK backing/owner metadata.
This never duplicates the current borrow store in auxiliary state. -/
def closeSampleFocus : Owned.Focus (World CloseSampleAux) AccountInfoSdk.State where
  get := fun state => ⟨state.1, state.2.1.1, state.2.1.2⟩
  set := fun state sdk => (sdk.borrow, ((sdk.owners, sdk.buffers), state.2.2))
  get_set := by intro _ sdk; cases sdk; rfl
  set_get := by intro state; rcases state with ⟨borrow, ⟨⟨owners, buffers⟩, heap⟩⟩; rfl
  set_set := by intro _ _ _; rfl

def closeSample (errors : AnchorErrorOperations.Storage) : CloseTypes where
  Aux := CloseSampleAux
  Unwind := String
  Terminal := AnchorErrorOwned.Reference.Failure
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  Program := ProgramError.Value
  errorStorage := errors
  errors := AnchorErrorOperations.Ops.fromOwned
    (AnchorErrorOwned.Reference.ops.focus (Owned.Focus.snd.comp Owned.Focus.snd))
  programValue := id
  sdk := closeSampleFocus
  borrow_eq := fun _ => rfl
  rc := sampleRc

def closeSampleBefore : World CloseSampleAux :=
  (AccountInfoSdk.sample.borrow,
    ((AccountInfoSdk.sample.owners, AccountInfoSdk.sample.buffers), AnchorOwnedSamples.auxiliary))

def closeSampleArgs : CloseArgs :=
  ⟨AccountInfo.sampleProfile, AccountInfo.sampleInfo, AccountInfo.sampleInfo⟩

def closeSampleAfterSdk : AccountInfoSdk.State :=
  ⟨⟨[⟨.lamports 0, AccountInfo.sampleProfile.policy⟩, ⟨.data [], AccountInfo.sampleProfile.policy⟩],
    List.replicate 5 none⟩, [.zero], [none, some ⟨3, 0, [10, 20, 30, 40, 50, 60]⟩]⟩

def closeSampleAfter : World CloseSampleAux := closeSampleFocus.set closeSampleBefore
  closeSampleAfterSdk

theorem closeSample_core (mode : CloseMode) :
    commonCloseCore mode AccountInfoSdk.sample closeSampleArgs =
      some (.returned (.ok ()) closeSampleAfterSdk) := by
  cases mode <;> rfl

def closeSampleBalanceState (balance : UInt64) (leases : Nat) : AccountInfoSdk.State :=
  { AccountInfoSdk.sample with borrow :=
    ⟨[⟨.lamports balance, AccountInfo.sampleProfile.policy⟩,
      ⟨.data [10, 20, 30], AccountInfo.sampleProfile.policy⟩], List.replicate leases none⟩ }

theorem closeSample_ready (mode : CloseMode) (errors : AnchorErrorOperations.Storage) :
    CommonCloseReady (closeSample errors) closeSampleBefore closeSampleArgs mode := by
  cases mode <;> refine ⟨⟨⟨.lamports 40, AccountInfo.sampleProfile.policy⟩, 40, rfl, rfl⟩, ?_⟩
  all_goals
    intro firstAmount afterFirst first
    change (some (.returned 40 (closeSampleBalanceState 40 1)) : Option (CloseOutcome Nat)) = some
      (.returned firstAmount afterFirst) at first
    cases first
    refine ⟨⟨⟨.lamports 40, AccountInfo.sampleProfile.policy⟩, 40, rfl, rfl⟩, ?_⟩
    intro secondAmount afterSecond second
    change (some (.returned 40 (closeSampleBalanceState 40 2)) : Option (CloseOutcome Nat)) = some
      (.returned secondAmount afterSecond) at second
    cases second
    intro _ credited credit zeroed zero
    change (some (.returned (.ok ()) (closeSampleBalanceState 80 3)) : Option (CloseOutcome (Except
      ProgramError.Value Unit))) = some (.returned (.ok ()) credited) at credit
    cases credit
    change (some (.returned (.ok ()) (closeSampleBalanceState 0 4)) : Option (CloseOutcome (Except
      ProgramError.Value Unit))) = some (.returned (.ok ()) zeroed) at zero
    cases zero
    refine ⟨by decide, ?_⟩
    refine ⟨?_, [10, 20, 30], AccountInfo.sampleProfile.policy, rfl, ?_⟩
    · change (closeSampleBalanceState 0 4).borrow.Valid
      constructor
      · intro id slot live
        change ((List.replicate 4 (none : Option (Borrow.Slot AccountInfo.View)))[id]?.bind (fun
          entry => entry)) = some slot at live
        simp only [List.getElem?_replicate] at live
        split at live <;> contradiction
      · intro handle cell found
        constructor <;> simp [Borrow.State.exclusiveCount, Borrow.State.sharedCount,
          Borrow.State.count,
          closeSampleBalanceState]
    · intro _ _ _
      exact ⟨⟨3, 3, [40, 50, 60]⟩, rfl, by intro _; exact Nat.zero_le _⟩

theorem closeSample_common (mode : CloseMode) (errors : AnchorErrorOperations.Storage) :
    commonClose mode (closeSample errors) closeSampleBefore closeSampleArgs
      (.returned (.ok ()) closeSampleAfter) := by
  change (match commonCloseCore mode AccountInfoSdk.sample closeSampleArgs with
    | none => False
    | some (.unwound reason after) => _
    | some (.terminated reason) => _
    | some (.returned (.ok ()) after) => _
    | some (.returned (.error failure) after) => _)
  rw [closeSample_core]
  rfl

theorem closeSample_drop (errors : AnchorErrorOperations.Storage)
    (state : World CloseSampleAux) (info : AccountInfo.Value) :
    closeLiftCall (fun state (_ : Unit) => dropInfo (closeSample errors).toBase (closeSample
      errors).rc info state)
      state () (.returned () state) := by
  exact ⟨.returned () state, (sampleRc_drop _ _ _ _).mpr rfl, rfl⟩

theorem closeSample_wrapper (cloned : Bool) (mode : CloseMode) (errors :
  AnchorErrorOperations.Storage) :
    wrapperClose cloned mode (closeSample errors) closeSampleBefore closeSampleArgs
      (.returned (.ok ()) closeSampleAfter) := by
  cases cloned with
  | false =>
    refine ⟨.returned (.ok ()) closeSampleAfter, closeSample_common mode errors, ?_⟩
    exact ⟨.returned () closeSampleAfter, closeSample_drop errors _ _, rfl⟩
  | true =>
    refine ⟨.returned AccountInfo.sampleInfo closeSampleBefore, ?_, ?_⟩
    · exact ⟨.returned AccountInfo.sampleInfo closeSampleBefore, (sampleRc_clone _ _ _ _).mpr rfl,
      rfl⟩
    · refine ⟨.returned (.ok ()) closeSampleAfter, closeSample_common mode errors, ?_⟩
      exact ⟨.returned () closeSampleAfter, closeSample_drop errors _ _,
        .returned () closeSampleAfter, closeSample_drop errors _ _, rfl⟩

theorem close_execution (cloned : Bool) (mode : CloseMode) (errors : AnchorErrorOperations.Storage)
  :
    FamilyHasExecution (closeFamily cloned mode) (closeRun cloned mode) (closeSample errors) := by
  refine ⟨closeSampleBefore, closeSampleArgs, .returned (.ok ()) closeSampleAfter, ?_,
    closeSample_wrapper cloned mode errors⟩
  cases cloned with
  | false => exact closeSample_ready mode errors
  | true =>
    intro info after cloned
    have same := (sampleRc_clone _ _ _ _).mp cloned
    cases same
    exact closeSample_ready mode errors

end Solanalib.Specs.Core.AnchorLifecycle
