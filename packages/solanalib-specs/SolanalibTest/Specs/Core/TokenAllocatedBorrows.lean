/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessBorrows
public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessResources
public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessPrepare
public import Solanalib.Specs.Core.TokenRequestAllocatedOnchain

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.TokenAllocatedBorrows

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Token Token.AllocatedControl Token.OnchainAllocated
open Token.OnchainAllocated.Admission Token.OnchainAllocated.Witness

/-- Only the account-borrow world changes between these input controls. -/
def worldAt (world : AccountInfo.State) (state : State) : State := (world, state.2)

/-- The ordinary constructor and four Rc clones actually run with either
input world; they do not perform a premature data read or require data typing. -/
theorem base_in_world (world : AccountInfo.State) :
    base sampleTypes Onchain.witnessArgs (worldAt world initialState)
      (.returned (.ok prepared) (worldAt world infosState)) := by
  have infos : initialInfos sampleTypes Onchain.witnessArgs (worldAt world instructionState)
      (.returned (.ok (0 : Nat)) (worldAt world infosState)) := by
    refine ⟨.returned (0 : Nat) (worldAt world infosState), ?_, rfl⟩
    refine ⟨.returned (0 : Nat) (worldAt world infosState), ?_, rfl⟩
    refine .next [] (worldAt world instructionState) (worldAt world instructionState)
      (worldAt world clone1) Onchain.witnessInfo _ (by decide) rfl ?_ ?_
    · exact clone_lift_returns _ _ (by
        unfold cloneReady rcReady; dsimp [worldAt, rcAfter]; decide +kernel)
    refine .next _ (worldAt world clone1) (worldAt world clone1)
      (worldAt world clone2) Onchain.witnessInfo _ (by decide) rfl ?_ ?_
    · exact clone_lift_returns _ _ (by
        unfold cloneReady rcReady; dsimp [worldAt, rcAfter]; decide +kernel)
    refine .next _ (worldAt world clone2) (worldAt world clone2)
      (worldAt world clone3) Onchain.witnessInfo _ (by decide) rfl ?_ ?_
    · exact clone_lift_returns _ _ (by
        unfold cloneReady rcReady; dsimp [worldAt, rcAfter]; decide +kernel)
    refine .next _ (worldAt world clone3) (worldAt world clone3)
      (worldAt world clone4) Onchain.witnessInfo _ (by decide) rfl ?_ ?_
    · exact clone_lift_returns _ _ (by
        unfold cloneReady rcReady; dsimp [worldAt, rcAfter]; decide +kernel)
    exact .finishReturn accounts (worldAt world clone4) (worldAt world clone4)
      (worldAt world infosState) (0 : Nat) rfl ⟨rfl, rfl⟩
      ⟨.returned (0 : Nat) [some accounts], rfl, rfl⟩
  refine ⟨.returned (.ok (ownedInstruction plan)) (worldAt world instructionState),
    constructor_returns (worldAt world initialState) plan rfl rfl (by rfl), ?_⟩
  refine ⟨.returned (.ok prepared) (worldAt world infosState), ?_, rfl⟩
  refine ⟨.returned (.ok (0 : Nat)) (worldAt world infosState), infos, ?_⟩
  exact ⟨.returned (.ok prepared) (worldAt world infosState),
    ⟨.returned (.ok ()) (worldAt world infosState),
      ⟨.returned (.ok false) (worldAt world infosState), rfl, rfl⟩, rfl⟩, rfl⟩

/-- The selected mint cell exists, but contains lamports instead of data. -/
def wrongWorld : AccountInfo.State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.lamports 40, AccountInfo.sampleProfile.policy⟩], []⟩

/-- The untyped primitive can acquire the selected existing cell. -/
theorem wrong_mint_acquires :
    (AccountInfo.tryBorrow .shared Onchain.witnessInfo.data wrongWorld).1 = .ok ⟨0, 0⟩ := rfl

/-- Its immediately following data read has no represented outcome. -/
theorem wrong_mint_read_absent
    (pending : Outcome State (Except Error DataRef) Nat Nat) :
    ¬ borrow sampleTypes.raise true Onchain.witnessArgs.mint (worldAt wrongWorld infosState)
      pending := by
  exact id

/-- The new family input gate rejects a real reached malformed mint before
its missing local read can erase every later preparation outcome. -/
theorem wrong_mint_rejected (deps : Dependencies sampleTypes)
    (protocol : AllocatedCollect.Protocol Extra Nat Nat Nat) :
    ¬ BorrowReady sampleTypes deps protocol (worldAt wrongWorld initialState) Onchain.witnessArgs
      := by
  intro ready
  obtain ⟨result, after, called⟩ := ready.mint_continue (base_in_world wrongWorld)
  exact wrong_mint_read_absent (.returned result after) called

/-- These opaque dependencies are unused by the actual base prefix above. -/
def controlDeps : Dependencies sampleTypes where
  collect := { run := fun _ _ _ _ => False }
  invoke := fun _ _ _ => False

/-- The old provider-only gates hold for these unchanged providers, including
when the separate source input contains the malformed selected mint. -/
theorem provider_gates_hold :
    Admitted sampleTypes controlDeps sampleGuardProtocol ∧
      ResourceReady sampleTypes controlDeps sampleGuardProtocol := by
  refine ⟨sample_admitted controlDeps (fun _ _ _ _ impossible => impossible),
    sample_resources controlDeps ?_⟩
  intro _ _ _ _ _ _ impossible
  exact False.elim impossible

/-- The primary contract rejects the reached wrong-typed mint even though
the ordinary provider interpretations satisfy both provider gates. -/
theorem wrong_mint_family_rejected :
    ¬ (family.contract ⟨sampleTypes, controlDeps⟩).requires
      (worldAt wrongWorld initialState) Onchain.witnessArgs := by
  rintro ⟨protocol, _, _, borrows⟩
  exact wrong_mint_rejected controlDeps protocol borrows

/-- A selected real conflict and an unrelated invalid slot are independent. -/
def conflictWorld : AccountInfo.State := { Onchain.witnessState with
  slots := [some ⟨⟨1⟩, .exclusive, 0, .whole⟩, some ⟨⟨99⟩, .shared, 0, .whole⟩] }

/-- The unrelated slot points outside the actual cell store. -/
theorem conflict_world_invalid : ¬ conflictWorld.Valid := by
  intro valid
  obtain ⟨cell, current⟩ := valid.1 1 ⟨⟨99⟩, .shared, 0, .whole⟩ rfl
  cases current

/-- The selected live exclusive guard causes the real checked borrow error. -/
theorem conflict_actual_failure :
    AccountInfo.tryBorrow .shared Onchain.witnessArgs.mint.data conflictWorld =
      (.error .accountBorrowFailed, conflictWorld) := rfl

/-- The exact checked-error branch imposes neither current-data nor valid
store obligations. It retains AccountBorrowFailed in the actual current state. -/
theorem conflict_domain_and_exit :
    BorrowDomain .mint conflictWorld Onchain.witnessArgs.mint ∧
      borrow sampleTypes.raise true Onchain.witnessArgs.mint (worldAt conflictWorld infosState)
        (.returned (.error .AccountBorrowFailed) (worldAt conflictWorld infosState)) := by
  refine ⟨⟨?_, ?_, fun impossible => nomatch impossible⟩, rfl⟩
  · simp only [AccountInfo.DataBorrow.Ready, conflict_actual_failure]
  · intro _ guard during acquired
    rw [conflict_actual_failure] at acquired
    cases acquired

private theorem no_validation (world : AccountInfo.State) : ∀ helperArgs execute info before,
    ¬ ValidationPrefix sampleTypes (worldAt world initialState) Onchain.witnessArgs
      helperArgs execute info before := by
  intro helperArgs execute info before reached
  cases reached with
  | reached _ _ _ entered _ _ =>
    obtain ⟨_, ⟨_, ⟨_, source⟩, _⟩, _⟩ := entered
    obtain ⟨_, ⟨_, impossible, _⟩, _⟩ := source
    exact impossible

/-- All reached sites of this input are admitted despite its unrelated
invalid slot: its only data acquisition always takes the checked-error branch. -/
theorem conflict_input_ready :
    BorrowReady sampleTypes controlDeps sampleGuardProtocol
      (worldAt conflictWorld initialState) Onchain.witnessArgs := by
  intro kind before info reached
  cases reached with
  | authorityLength _ owned =>
    have nonToken : Solanalib.Runtime.Pubkey.zero ≠ token2022ProgramId ∧
      Solanalib.Runtime.Pubkey.zero ≠ legacyProgramId := by
      decide +kernel
    rcases owned with token | legacy
    · exact False.elim (nonToken.1 token)
    · exact False.elim (nonToken.2 legacy)
  | authorityUnchecked _ selected _ =>
    change (Outcome.returned (.ok true) _ : Outcome State (Except Error Bool) Nat Nat) =
      .returned (.ok false) _ at selected
    cases selected
  | mint based =>
    have same : before.1 = conflictWorld := sample_base_accounts based
    exact same.symm ▸ conflict_domain_and_exit.1
  | validation reached => exact False.elim (no_validation conflictWorld _ _ _ _ reached)
  | collection reached _ _ _ _ _ _ _ _ => exact False.elim (no_validation conflictWorld _ _ _ _
    reached)

/-- The same primary contract admits the actual checked-conflict path with
its unrelated invalid slot, retaining the AccountBorrowFailed exit of the source. -/
theorem conflict_family_admitted :
    (family.contract ⟨sampleTypes, controlDeps⟩).requires
      (worldAt conflictWorld initialState) Onchain.witnessArgs :=
  ⟨sampleGuardProtocol, provider_gates_hold.1, provider_gates_hold.2, conflict_input_ready⟩

/-- An actual sample mint acquisition reaches its current read and checked
release using only the input gate supplied by the same closed sample. -/
theorem sample_mint_read_drop :
    ∃ bytes : Bytes, withData sampleTypes.raise sampleTypes.doubleUnwind true
      Onchain.witnessArgs.mint
      (fun reference => inspect reference.read) infosState (.returned (.ok bytes)
        guardReleasedState) :=
  (sample_borrows controlDeps sampleGuardProtocol).acquired_read_scope
    (.mint base_returns) (by decide)
    (show AccountInfo.tryBorrow .shared Onchain.witnessArgs.mint.data infosState.1 =
      (.ok mintReference.guard, mintBorrowWorld) from rfl)

end SolanalibTest.Specs.Core.TokenAllocatedBorrows
