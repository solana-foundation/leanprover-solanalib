/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.SolanaAccountView.Lifecycle

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaAccountView.Mapping.Infallible

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AccountView
open SolanalibTest.Specs.SolanaAccountView.Lifecycle

/-- The callback may capture a counter while projecting a byte range. -/
def profile : MapProfile := ⟨sliceProfileWithAux Nat, Empty, Empty⟩
/-- A shared byte guard with an independently captured counter. -/
def before : profile.target.World := (sharedState, (7 : Nat))
/-- The account pool of the callback after an aliased header update. -/
def changedState : State := (setLamports sharedState (handle, 29)).2
/-- The full resulting world of the callback, including its captured counter. -/
def changed : profile.target.World := (changedState, (8 : Nat))
/-- The mapped one-byte view inside the original account. -/
def target : Slice := ⟨1, 1⟩
/-- The modeled mapping input and its complete callback relation. -/
def args : TryMapArgs profile.fallible :=
  ⟨guard, fun _ _ _ outcome => outcome = .returned (.ok target) changed⟩
/-- The world after normal mapping transfers the guard to its new generation. -/
def after : profile.target.World :=
  ((Borrow.transfer changedState guard target).2, (8 : Nat))

theorem shared_ready : GuardReady sharedState .shared guard :=
  acquire_guardReady state_ready.1 shared_step

theorem changed_ready : Ready changedState handle :=
  setLamports_ready (acquire_ready state_ready .shared) (by decide)

/-- Captured header writes are allowed without changing the held shared bytes. -/
theorem callback_frame : Borrow.CallbackFrame sliceFootprint sharedState changedState guard := by
  apply Borrow.CallbackFrame.of_slots (before := sharedState) (after := changedState)
    changed_ready.1.1 rfl
  · intro query
    change ((Borrow.replaceCell sharedState handle (account.setLamports 29)).2.lookupCell query).map
        Borrow.Cell.policy = (sharedState.lookupCell query).map Borrow.Cell.policy
    exact Borrow.replaceCell_policy _ _ _ _
  · intro slot old next live oldPresent nextPresent
    change some ⟨handle, .shared, 0, ⟨0, 3⟩⟩ = some slot at live
    cases live
    change some ⟨account, Borrow.Policy.accountView⟩ = some old at oldPresent
    cases oldPresent
    change some ⟨account.setLamports 29, Borrow.Policy.accountView⟩ = some next at nextPresent
    cases nextPresent
    exact ⟨rfl, rfl, fun _ => rfl⟩

/-- Every finite exit of this concrete callback meets the generic source premise. -/
theorem callback_safe : profile.fallible.CallbackSafe before args := by
  intro slot cell live _ produced step
  change produced = .returned (.ok target) changed at step
  subst produced
  change some ⟨handle, .shared, 0, ⟨0, 3⟩⟩ = some slot at live
  cases live
  exact ⟨callback_frame, changed_ready.1, _, rfl, by change 2 ≤ 3; decide⟩

theorem precondition :
    (Solanalib.Specs.SolanaAccountView.Ref.map_contract.contract profile).requires before args :=
  ⟨⟨_, _, rfl, rfl, rfl⟩, callback_safe⟩

/-- This is an actual admitted run of the named source family reference. -/
theorem reference_runs :
    Solanalib.Specs.SolanaAccountView.Ref.map_model profile before args
      (.returned (nextGuard guard) after) := by
  exact genericTryMap_of_callback profile.fallible (before := before) (args := args)
    (slot := ⟨handle, .shared, 0, ⟨0, 3⟩⟩) (cell := ⟨account, Borrow.Policy.accountView⟩)
    (produced := .returned (.ok target) changed) rfl rfl callback_safe rfl

/-- The source contract follows by instantiating its universal reference theorem. -/
theorem mapping_contract :
    (Solanalib.Specs.SolanaAccountView.Ref.map_contract.contract profile).ensures before args
      (nextGuard guard) after :=
  (FamilyReference.at Solanalib.Specs.SolanaAccountView.Ref.map_reference profile)
    before args _ precondition reference_runs

/-- Shared map transfers ownership, narrows the view and preserves both captured
effects. The old token cannot be used or released a second time. -/
theorem mapping_effects :
    (State.account after.1 handle).lamports = 29 ∧ after.2 = (8 : Nat) ∧
    guardRead after.1 (nextGuard guard) = .ok [2] ∧
    guardRead after.1 guard = .error .invalidGuard ∧
    after.1.lease handle = .shared 1 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The mapped reference is usable in its target interpretation, while the input
token is permanently retired by the shared ownership protocol. -/
theorem mapped_reference_ready :
    profile.target.Ready .shared after (nextGuard guard) ∧ Borrow.Retired after.1 guard :=
  map_returned_guardReady profile .shared precondition mapping_contract

end SolanalibTest.Specs.SolanaAccountView.Mapping.Infallible

namespace SolanalibTest.Specs.SolanaAccountView.Mapping.Fallible

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AccountView
open SolanalibTest.Specs.SolanaAccountView.Lifecycle

/-- Type parameters retain ordinary errors, unwind and terminal outcomes. -/
def profile : TryMapProfile := ⟨sliceProfileWithAux Nat, Nat, Unit, Unit⟩
/-- An exclusive byte guard with an independently captured counter. -/
def before : profile.target.World := (exclusiveState, (7 : Nat))
/-- The callback world after an immediate data write and captured-counter update. -/
def changed : profile.target.World := (writtenState, (8 : Nat))
/-- The world after normal error return transfers the original guard generation. -/
def after : profile.target.World :=
  ((Borrow.transfer writtenState guard ⟨0, 3⟩).2, (8 : Nat))
/-- A fallible callback that mutates the world before returning an ordinary error. -/
def errorArgs : TryMapArgs profile :=
  ⟨guard, fun _ _ _ outcome => outcome = .returned (.error (9 : Nat)) changed⟩

/-- The callback writes immediately through its exclusive target. The common
frame still retains its original account, mode and guard generation until map
completion, and allows the separate captured counter to change. -/
theorem callback_frame : Borrow.CallbackFrame sliceFootprint exclusiveState writtenState guard := by
  apply Borrow.CallbackFrame.of_slots (before := exclusiveState) (after := writtenState)
    written_ready.1.1 rfl
  · intro query
    change ((Borrow.replaceCell exclusiveState handle (account.write ⟨0, 3⟩ [9, 8, 7])).2.lookupCell
        query).map Borrow.Cell.policy =
      (exclusiveState.lookupCell query).map Borrow.Cell.policy
    exact Borrow.replaceCell_policy _ _ _ _
  · intro slot old next live oldPresent nextPresent
    change some ⟨handle, .exclusive, 0, ⟨0, 3⟩⟩ = some slot at live
    cases live
    change some ⟨account, Borrow.Policy.accountView⟩ = some old at oldPresent
    cases oldPresent
    change some ⟨account.write ⟨0, 3⟩ [9, 8, 7], Borrow.Policy.accountView⟩ = some next
      at nextPresent
    cases nextPresent
    exact ⟨rfl, rfl, by intro impossible; cases impossible⟩

/-- A normal callback error is admissible with its actual changed account bytes. -/
theorem error_safe : profile.CallbackSafe before errorArgs := by
  intro slot cell live _ produced step
  change produced = .returned (.error (9 : Nat)) changed at step
  subst produced
  change some ⟨handle, .exclusive, 0, ⟨0, 3⟩⟩ = some slot at live
  cases live
  exact ⟨callback_frame, written_ready.1, _, rfl, by change 3 ≤ 3; decide⟩

theorem error_precondition :
    (Solanalib.Specs.SolanaAccountView.RefMut.try_map_contract.contract profile).requires before
      errorArgs :=
  ⟨⟨_, _, rfl, rfl, rfl⟩, error_safe⟩

/-- The named generic source reference has this actual error execution. -/
theorem error_reference_runs :
    Solanalib.Specs.SolanaAccountView.RefMut.try_map_model profile before errorArgs
      (.returned (.error (nextGuard guard, (9 : Nat))) after) := by
  exact genericTryMap_of_callback profile (before := before) (args := errorArgs)
    (slot := ⟨handle, .exclusive, 0, ⟨0, 3⟩⟩) (cell := ⟨account, Borrow.Policy.accountView⟩)
    (produced := .returned (.error (9 : Nat)) changed) rfl rfl error_safe rfl

theorem error_contract :
    (Solanalib.Specs.SolanaAccountView.RefMut.try_map_contract.contract profile).ensures before
      errorArgs
      (.error (nextGuard guard, (9 : Nat))) after :=
  (FamilyReference.at Solanalib.Specs.SolanaAccountView.RefMut.try_map_reference profile)
    before errorArgs _ error_precondition error_reference_runs

/-- Err returns the transferred original view and every callback write. -/
theorem error_keeps_mutation :
    guardRead after.1 (nextGuard guard) = .ok [9, 8, 7] ∧ after.2 = (8 : Nat) ∧
    guardRead after.1 guard = .error .invalidGuard ∧
    after.1.lease handle = .exclusive := ⟨rfl, rfl, rfl, rfl⟩

theorem returned_error_guard_ready :
    profile.target.Ready .exclusive after (nextGuard guard) ∧ Borrow.Retired after.1 guard :=
  tryMap_returned_guardReady profile .exclusive error_precondition error_contract

/-- The returned Err guard can be released normally; its writes are not copied
back at release because they are already part of the current cell. -/
theorem release_after_error :
    (Solanalib.Specs.SolanaAccountView.RefMut.release_contract.contract profile.target).ensures
      after (nextGuard guard) () ((Borrow.release after.1 (nextGuard guard)).2, after.2) := by
  apply (FamilyReference.at Solanalib.Specs.SolanaAccountView.RefMut.release_reference
    profile.target)
    after (nextGuard guard) (.returned () ((Borrow.release after.1 (nextGuard guard)).2, after.2))
  · exact ⟨_, rfl⟩
  · rfl

/-- A callback that mutates the world before a finite unwinding exit. -/
def unwindArgs : TryMapArgs profile :=
  ⟨guard, fun _ _ _ outcome => outcome = .unwound (() : Unit) changed⟩

theorem unwind_safe : profile.CallbackSafe before unwindArgs := by
  intro slot cell _ _ produced step
  change produced = .unwound (() : Unit) changed at step
  subst produced
  exact ⟨callback_frame, written_ready.1⟩

theorem unwind_precondition :
    (Solanalib.Specs.SolanaAccountView.RefMut.try_map_contract.contract profile).requires before
      unwindArgs :=
  ⟨⟨_, _, rfl, rfl, rfl⟩, unwind_safe⟩

/-- ManuallyDrop prevents release of the original lease on a modeled callback
unwind. The source binding must separately justify whether unwinding is enabled. -/
theorem unwind_reference_runs :
    Solanalib.Specs.SolanaAccountView.RefMut.try_map_model profile before unwindArgs
      (.unwound (() : Unit) after) := by
  exact genericTryMap_of_callback profile (before := before) (args := unwindArgs)
    (slot := ⟨handle, .exclusive, 0, ⟨0, 3⟩⟩) (cell := ⟨account, Borrow.Policy.accountView⟩)
    (produced := .unwound (() : Unit) changed) rfl rfl unwind_safe rfl

theorem unwind_contract :
    (Solanalib.Specs.SolanaAccountView.RefMut.try_map_contract.contract profile).post before
      unwindArgs
      (.unwound (() : Unit) after) :=
  (FamilyReference.at Solanalib.Specs.SolanaAccountView.RefMut.try_map_reference profile)
    before unwindArgs _ unwind_precondition unwind_reference_runs

theorem unwind_consumes_token_retains_lease :
    Borrow.Retired after.1 guard ∧ after.1.lease handle = .exclusive ∧ after.2 = (8 : Nat) :=
  ⟨(tryMap_unwind_retired profile .exclusive unwind_contract).2, rfl, rfl⟩

/-- A callback with a terminal outcome and no resulting world. -/
def terminalArgs : TryMapArgs profile :=
  ⟨guard, fun _ _ _ outcome => outcome = .terminated (() : Unit)⟩

theorem terminal_precondition :
    (Solanalib.Specs.SolanaAccountView.RefMut.try_map_contract.contract profile).requires before
      terminalArgs := by
  refine ⟨⟨_, _, rfl, rfl, rfl⟩, ?_⟩
  intro slot cell _ _ produced step
  change produced = .terminated (() : Unit) at step
  subst produced
  exact ⟨trivial, trivial⟩

/-- A terminal callback outcome is forwarded without fabricating a final state. -/
theorem terminal_reference_runs :
    Solanalib.Specs.SolanaAccountView.RefMut.try_map_model profile before terminalArgs
      (.terminated (() : Unit)) := by
  exact genericTryMap_of_callback profile (before := before) (args := terminalArgs)
    (slot := ⟨handle, .exclusive, 0, ⟨0, 3⟩⟩) (cell := ⟨account, Borrow.Policy.accountView⟩)
    (produced := .terminated (() : Unit)) rfl rfl terminal_precondition.2 rfl

theorem terminal_contract :
    (Solanalib.Specs.SolanaAccountView.RefMut.try_map_contract.contract profile).post before
      terminalArgs
      (.terminated (() : Unit)) :=
  (FamilyReference.at Solanalib.Specs.SolanaAccountView.RefMut.try_map_reference profile)
    before terminalArgs _ terminal_precondition terminal_reference_runs

end SolanalibTest.Specs.SolanaAccountView.Mapping.Fallible
