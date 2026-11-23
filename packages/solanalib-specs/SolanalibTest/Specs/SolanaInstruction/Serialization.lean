/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaInstruction

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaInstruction

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.InstructionBuilder
open Solanalib.Specs.SolanaInstruction.Instruction

theorem bincode_success_moves_both_resources :
    new_with_bincode_run new_with_bincode_sample Sample.constructorBefore Sample.constructorArgs
      (.returned ⟨.zero, (0 : Nat), (0 : Nat)⟩ (Sample.constructorAfter .bincode)) ∧
    (Sample.constructorAfter .bincode).events = [10, 20] :=
  ⟨Sample.constructorSuccess .bincode, rfl⟩

theorem wincode_success_observes_current_vectors :
    new_with_wincode_run new_with_wincode_sample Sample.constructorBefore Sample.constructorArgs
      (.returned ⟨.zero, (0 : Nat), (0 : Nat)⟩ (Sample.constructorAfter .wincode)) ∧
    observe _ Sample.constructorArgs.providers (Sample.constructorAfter .wincode)
      ⟨.zero, (0 : Nat), (0 : Nat)⟩ = some
        (Instruction.make .zero
          [Instruction.accountMeta .zero true true, Instruction.accountMeta .zero false true]
          [2, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0]) ∧
    (Sample.constructorAfter .wincode).events = [10, 21] :=
  ⟨Sample.constructorSuccess .wincode, rfl, rfl⟩

def serializationErrorArgs : Args (Sample.types _root_.Solanalib.Runtime.Bytes) :=
  { Sample.constructorArgs with
    providers := { Sample.constructorArgs.providers with
      serialize := Callback.ofFunction fun (before : Sample.State) _ =>
        .returned (.error (5 : Nat)) { before with events := before.events ++ [25] } } }

def afterSerializationError : Sample.State :=
  { Sample.constructorBefore with events := [10, 25] }

def afterUnwrapError : Sample.State :=
  { afterSerializationError with events := [10, 25, 30] }

def afterErrorCleanup : Sample.State := Sample.retireMetas afterUnwrapError 0

theorem serializer_error_unwraps_then_drops_accounts :
    new_with_bincode_run new_with_bincode_sample Sample.constructorBefore serializationErrorArgs
      (.unwound (105 : Nat) afterErrorCleanup) ∧
    afterErrorCleanup.events = [10, 25, 30, 40] ∧
    Sample.metasAt afterErrorCleanup 0 = none ∧ afterErrorCleanup.bytes = [] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  refine ⟨.unwound (105 : Nat) afterUnwrapError, ?_, ?_⟩
  · refine ⟨.returned (.error (5 : Nat)) afterSerializationError, rfl, ?_⟩
    exact ⟨.unwound (105 : Nat) afterUnwrapError, rfl, rfl⟩
  · exact ⟨.returned () afterErrorCleanup, rfl, rfl⟩

theorem serializer_error_cannot_return_instruction
    (value : Value (Sample.types _root_.Solanalib.Runtime.Bytes)) (after : Sample.State) :
    ¬ new_with_bincode_run new_with_bincode_sample Sample.constructorBefore
      serializationErrorArgs (.returned value after) := by
  simp [new_with_bincode_run, new_with_bincode_sample, familyRun, run, rawRun,
    Owned.protect, Owned.onUnwind, Owned.cleanup, Owned.VectorOps.dropAction,
    Callback.bind, Callback.map, Callback.ofFunction, serializationErrorArgs,
    Sample.constructorArgs, Sample.providers, Sample.metaVec, Outcome.map]
  intro cleanupOutcome returned
  cases returned
  trivial

def serializerUnwindArgs : Args (Sample.types _root_.Solanalib.Runtime.Bytes) :=
  { Sample.constructorArgs with
    providers := { Sample.constructorArgs.providers with
      serialize := Callback.ofFunction fun (before : Sample.State) _ =>
        .unwound (17 : Nat) { before with events := before.events ++ [26] }
      metaVec := { Sample.metaVec with
        drop := fun (before : Sample.State) (resource : Nat) outcome =>
          before.events = [10, 26] ∧ resource = 0 ∧
          outcome = .returned () (Sample.retireMetas before resource) } } }

def afterSerializerUnwind : Sample.State :=
  { Sample.constructorBefore with events := [10, 26] }

theorem unwind_cleanup_receives_serializer_state :
    new_with_wincode_run new_with_wincode_sample Sample.constructorBefore serializerUnwindArgs
      (.unwound (17 : Nat) (Sample.retireMetas afterSerializerUnwind 0)) := by
  refine ⟨.unwound (17 : Nat) afterSerializerUnwind, ?_, ?_⟩
  · exact ⟨.unwound (17 : Nat) afterSerializerUnwind, rfl, rfl⟩
  · exact ⟨.returned () (Sample.retireMetas afterSerializerUnwind 0), ⟨rfl, rfl, rfl⟩, rfl⟩

def terminalSerializerArgs : Args (Sample.types _root_.Solanalib.Runtime.Bytes) :=
  { Sample.constructorArgs with
    providers := { Sample.constructorArgs.providers with
      serialize := Callback.ofFunction fun _ _ => .terminated (77 : Nat)
      metaVec := { Sample.metaVec with drop := fun _ _ _ => False } } }

theorem terminal_serializer_skips_retained_drop :
    new_with_bincode_run new_with_bincode_sample Sample.constructorBefore terminalSerializerArgs
      (.terminated (77 : Nat)) :=
  ⟨.terminated (77 : Nat), ⟨.terminated (77 : Nat), rfl, rfl⟩, rfl⟩

def terminalUnwrapArgs : Args (Sample.types _root_.Solanalib.Runtime.Bytes) :=
  { serializationErrorArgs with
    providers := { serializationErrorArgs.providers with
      unwrapFailure := Callback.ofFunction fun (before : Sample.State) (error : Nat) =>
        .terminated (error + before.events.length)
      metaVec := { Sample.metaVec with drop := fun _ _ _ => False } } }

theorem terminal_unwrap_uses_error_state_and_skips_drop :
    new_with_wincode_run new_with_wincode_sample Sample.constructorBefore terminalUnwrapArgs
      (.terminated (7 : Nat)) := by
  refine ⟨.terminated (7 : Nat), ?_, rfl⟩
  exact ⟨.returned (.error (5 : Nat)) afterSerializationError, rfl,
    .terminated (7 : Nat), rfl, rfl⟩

def doubleUnwindArgs : Args (Sample.types _root_.Solanalib.Runtime.Bytes) :=
  { serializationErrorArgs with
    providers := { serializationErrorArgs.providers with
      metaVec := { Sample.metaVec with
        drop := Callback.ofFunction fun (before : Sample.State) (resource : Nat) =>
          .unwound (31 : Nat) (Sample.retireMetas before resource) }
      doubleUnwind := fun (before : Sample.State) (first later terminal : Nat) =>
        before.events = [10, 25, 30, 40] ∧ Sample.metasAt before 0 = none ∧
        first = 105 ∧ later = 31 ∧ terminal = 999 } }

theorem cleanup_double_unwind_uses_actual_drop_state :
    new_with_bincode_run new_with_bincode_sample Sample.constructorBefore doubleUnwindArgs
      (.terminated (999 : Nat)) := by
  refine ⟨.unwound (105 : Nat) afterUnwrapError, ?_, ?_⟩
  · exact ⟨.returned (.error (5 : Nat)) afterSerializationError, rfl,
      .unwound (105 : Nat) afterUnwrapError, rfl, rfl⟩
  · exact ⟨.unwound (31 : Nat) afterErrorCleanup, rfl, (999 : Nat),
      ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

end SolanalibTest.Specs.SolanaInstruction
