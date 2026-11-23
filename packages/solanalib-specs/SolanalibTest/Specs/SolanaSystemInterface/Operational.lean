/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaSystemInterface

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaSystemInterface

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaSystemInterface.instruction

theorem create_operational_allocation_then_serialization :
    create_account_operational_run create_account_operational_sample
      ({} : InstructionBuilder.Sample.State) createAccountSampleArgs
      (.returned ⟨.zero, (0 : Nat), (0 : Nat)⟩ createAccountSampleAfter) ∧
    createAccountSampleAfter.events = [10, 20] ∧
    InstructionBuilder.observe _ createAccountSampleArgs.providers createAccountSampleAfter
      ⟨.zero, (0 : Nat), (0 : Nat)⟩ =
        some (create_account_model () createAccountSampleArgs.source).1 := by
  refine ⟨?_, rfl, rfl⟩
  apply InstructionBuilder.allocateRun_of_returned _ _ _ createAccountSampleMiddle _ (0 : Nat)
  · rfl
  · exact InstructionBuilder.run_of_serialized _ _ _ _ _ _ rfl

theorem transfer_operational_preserves_flags_and_wincode_selection :
    transfer_operational_run transfer_operational_sample
      ({} : InstructionBuilder.Sample.State) transferSampleArgs
      (.returned ⟨.zero, (0 : Nat), (0 : Nat)⟩ transferSampleAfter) ∧
    transferSampleAfter.events = [10, 21] ∧
    InstructionBuilder.observe _ transferSampleArgs.providers transferSampleAfter
      ⟨.zero, (0 : Nat), (0 : Nat)⟩ = some (transfer_model () transferSampleArgs.source).1 := by
  refine ⟨?_, rfl, rfl⟩
  apply InstructionBuilder.allocateRun_of_returned _ _ _ transferSampleMiddle _ (0 : Nat)
  · rfl
  · exact InstructionBuilder.run_of_serialized _ _ _ _ _ _ rfl

def allocationUnwindArgs : TransferOperationalArgs transfer_operational_sample :=
  { transferSampleArgs with
    providers := { transferSampleArgs.providers with
      metaVec := { InstructionBuilder.Sample.metaVec with
        fromList := Callback.ofFunction fun (before : InstructionBuilder.Sample.State) _ =>
          .unwound (71 : Nat) { before with events := before.events ++ [12] }
        drop := fun _ _ _ => False }
      serialize := fun _ _ _ => False } }

theorem allocation_unwind_does_not_serialize_or_drop_unowned_vec :
    transfer_operational_run transfer_operational_sample
      ({} : InstructionBuilder.Sample.State) allocationUnwindArgs
      (.unwound (71 : Nat) ({ events := [12] } : InstructionBuilder.Sample.State)) :=
  ⟨.unwound (71 : Nat) ({ events := [12] } : InstructionBuilder.Sample.State), rfl, rfl⟩

def allocationTerminalArgs : TransferOperationalArgs transfer_operational_sample :=
  { allocationUnwindArgs with
    providers := { allocationUnwindArgs.providers with
      metaVec := { allocationUnwindArgs.providers.metaVec with
        fromList := Callback.ofFunction fun _ _ => .terminated (74 : Nat) } } }

theorem allocation_terminal_has_no_later_callbacks :
    transfer_operational_run transfer_operational_sample
      ({} : InstructionBuilder.Sample.State) allocationTerminalArgs
      (.terminated (74 : Nat)) := ⟨.terminated (74 : Nat), rfl, rfl⟩

def priorResources : InstructionBuilder.Sample.State where
  metas := [some [Instruction.accountMeta (_root_.Solanalib.Runtime.Pubkey.ofNat 8) false false]]
  bytes := [some [9, 8]]

def freshMiddle : InstructionBuilder.Sample.State :=
  InstructionBuilder.Sample.allocateMetas priorResources
    (transferAllocation _ transferSampleArgs).accounts

def freshAfter : InstructionBuilder.Sample.State :=
  InstructionBuilder.Sample.afterSerialize SystemData.bytes .wincode freshMiddle
    (transferAllocation _ transferSampleArgs).data

theorem returned_handles_are_actual_fresh_provider_results :
    transfer_operational_run transfer_operational_sample priorResources transferSampleArgs
      (.returned ⟨.zero, (1 : Nat), (1 : Nat)⟩ freshAfter) ∧
    InstructionBuilder.observe _ transferSampleArgs.providers freshAfter
      ⟨.zero, (1 : Nat), (1 : Nat)⟩ = some (transfer_model () transferSampleArgs.source).1 ∧
    InstructionBuilder.Sample.bytesAt freshAfter 0 = some [9, 8] := by
  refine ⟨?_, rfl, rfl⟩
  apply InstructionBuilder.allocateRun_of_returned _ _ _ freshMiddle _ (1 : Nat)
  · rfl
  · exact InstructionBuilder.run_of_serialized _ _ _ _ _ _ rfl

def systemSerializerErrorArgs : TransferOperationalArgs transfer_operational_sample :=
  { transferSampleArgs with
    providers := { transferSampleArgs.providers with
      serialize := Callback.ofFunction fun (before : InstructionBuilder.Sample.State) _ =>
        .returned (.error (5 : Nat)) { before with events := before.events ++ [25] } } }

def freshAfterError : InstructionBuilder.Sample.State :=
  { freshMiddle with events := [10, 25] }

def freshAfterUnwrap : InstructionBuilder.Sample.State :=
  { freshAfterError with events := [10, 25, 30] }

def freshAfterCleanup : InstructionBuilder.Sample.State :=
  InstructionBuilder.Sample.retireMetas freshAfterUnwrap 1

theorem error_cleanup_drops_only_new_metadata_resource :
    transfer_operational_run transfer_operational_sample priorResources systemSerializerErrorArgs
      (.unwound (105 : Nat) freshAfterCleanup) ∧
    freshAfterCleanup.events = [10, 25, 30, 40] ∧
    InstructionBuilder.Sample.metasAt freshAfterCleanup 1 = none ∧
    InstructionBuilder.Sample.metasAt freshAfterCleanup 0 =
      InstructionBuilder.Sample.metasAt priorResources 0 ∧
    InstructionBuilder.Sample.bytesAt freshAfterCleanup 0 = some [9, 8] := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  apply InstructionBuilder.allocateRun_of_returned _ _ _ freshMiddle _ (1 : Nat)
  · rfl
  · refine ⟨.unwound (105 : Nat) freshAfterUnwrap, ?_, ?_⟩
    · exact ⟨.returned (.error (5 : Nat)) freshAfterError, rfl,
        .unwound (105 : Nat) freshAfterUnwrap, rfl, rfl⟩
    · exact ⟨.returned () freshAfterCleanup, rfl, rfl⟩

end SolanalibTest.Specs.SolanaSystemInterface
