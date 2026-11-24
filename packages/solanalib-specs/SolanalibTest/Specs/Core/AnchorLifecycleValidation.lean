/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleProfiles
public import Solanalib.Specs.Core.ProgramErrorOwnedValues

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AnchorLifecycleValidation

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

/-- Scripted trait and allocation events expose source scheduling. Resource
numbers name the particular values returned by these dependency calls. -/
def validation (storage : AnchorErrorOperations.Storage) : ValidationTypes where
  Aux := List Nat
  Unwind := String
  Terminal := String
  StringResource := Nat
  BoxResource := Nat
  Program := ProgramErrorOwned.Value Nat
  errorStorage := storage
  errors := {
    currentString := fun _ resource => if resource = 41 then some "owned legacy error" else none
    currentBox := fun _ _ => none
    programStrings := ProgramErrorOwned.strings
    copyLiteral := Callback.ofFunction fun state _ => .returned 1 (state.1, state.2 ++ [10])
    formatLiteral := Callback.ofFunction fun state _ => .returned 2 (state.1, state.2 ++ [20])
    newBox := Callback.ofFunction fun state _ => .returned 3 (state.1, state.2 ++ [30])
    writeBox := fun _ _ _ => none
    dropString := Callback.ofFunction fun state resource => .returned () (state.1, state.2 ++ [100
      + resource])
    freeBox := Callback.ofFunction fun state resource => .returned () (state.1, state.2 ++ [200 +
      resource]) }
  programValue := fun _ => .accountBorrowFailed
  Payload := Nat
  ownerAt := fun _ _ => .zero
  id := Callback.ofFunction fun state _ => .returned .zero state
  checkId := Callback.ofFunction fun state _ => .returned (.ok ()) state
  fromAccountInfo := Callback.ofFunction fun state reference =>
    .returned (.error (.borshIoError 41)) (state.1, state.2 ++ [1000 + reference.identity])
  rc := {
    cloneRc := Callback.ofFunction fun state handle => .returned () (state.1, state.2 ++ [300 +
      handle.2.cell])
    dropRc := Callback.ofFunction fun state handle => .returned () (state.1, state.2 ++ [400 +
      handle.2.cell]) }

def before : AnchorAccount.World (List Nat) := (AccountInfo.sampleState, [])

def sysvarError (storage : AnchorErrorOperations.Storage) : (validation storage).toBase.Error :=
  errorAt storage (.anchor ⟨(1 : Nat), 3015, (2 : Nat), none, none⟩) (3 : Nat)

theorem sysvar_legacy_string_after_inline_error :
    validate .sysvar .owned (validation .inline) before validationArgs
      (.returned (.error (sysvarError .inline)) (before.1, [1019, 10, 20, 141])) := by
  refine ⟨.returned (.error (.borshIoError (41 : Nat))) (before.1, [1019]), ⟨_, rfl, rfl⟩,
    .returned (.error (sysvarError .inline)) (before.1, [1019, 10, 20]), ?_, ?_⟩
  · refine ⟨.returned (sysvarError .inline) (before.1, [1019, 10, 20]), ?_, rfl⟩
    exact ⟨_, ⟨_, ⟨.returned (1 : Nat) (before.1, [1019, 10]), rfl,
      .returned (2 : Nat) (before.1, [1019, 10, 20]), rfl, rfl⟩, rfl⟩, rfl⟩
  · exact ⟨.returned () (before.1, [1019, 10, 20, 141]),
      ⟨_, ⟨_, ⟨.returned () (before.1, [1019, 10, 20, 141]), rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

theorem sysvar_legacy_string_after_boxed_error :
    validate .sysvar .borrowed (validation .boxed) before validationArgs
      (.returned (.error (sysvarError .boxed)) (before.1, [1019, 10, 20, 30, 141])) := by
  refine ⟨.returned (.error (.borshIoError (41 : Nat))) (before.1, [1019]), ⟨_, rfl, rfl⟩,
    .returned (.error (sysvarError .boxed)) (before.1, [1019, 10, 20, 30]), ?_, ?_⟩
  · refine ⟨.returned (sysvarError .boxed) (before.1, [1019, 10, 20, 30]), ?_, rfl⟩
    exact ⟨_, ⟨_, ⟨.returned (1 : Nat) (before.1, [1019, 10]), rfl,
      .returned (2 : Nat) (before.1, [1019, 10, 20]), rfl,
      .returned (3 : Nat) (before.1, [1019, 10, 20, 30]), rfl, rfl⟩, rfl⟩, rfl⟩
  · exact ⟨.returned () (before.1, [1019, 10, 20, 30, 141]),
      ⟨_, ⟨_, ⟨.returned () (before.1, [1019, 10, 20, 30, 141]), rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

theorem sysvar_uses_original_record :
    (validation .boxed).fromAccountInfo before ⟨20, validationArgs.info⟩
      (.returned (.error (.borshIoError 41)) (before.1, [1020])) ∧
    validationArgs.reference.info = (⟨20, validationArgs.info⟩ : AccountReference).info ∧
    validationArgs.reference.identity ≠ 20 := by
  exact ⟨rfl, rfl, by decide⟩

theorem legacy_error_retains_string :
    ProgramErrorOwned.available .solana1_15_2 (.borshIoError (41 : Nat)) ∧
    ProgramErrorOwned.strings (.borshIoError (41 : Nat)) = [41] := by decide

theorem legacy_error_rejects_later_variant :
    ¬ ProgramErrorOwned.available .solana1_15_2
      (ProgramErrorOwned.Value.arithmeticOverflow : ProgramErrorOwned.Value Nat) := by decide

def terminalValidation : ValidationTypes :=
  { validation .boxed with errors := { (validation .boxed).errors with
      formatLiteral := Callback.ofFunction fun _ _ => .terminated "formatter abort" } }

theorem sysvar_factory_terminal_skips_cleanup :
    validate .sysvar .borrowed terminalValidation before validationArgs
      (.terminated (.inr "formatter abort")) := by
  refine ⟨.returned (.error (.borshIoError (41 : Nat))) (before.1, [1019]), ⟨_, rfl, rfl⟩,
    .terminated (.inr "formatter abort"), ?_, rfl⟩
  refine ⟨.terminated (.inr "formatter abort"), ?_, rfl⟩
  exact ⟨_, ⟨_, ⟨.returned (1 : Nat) (before.1, [1019, 10]), rfl,
    .terminated "formatter abort", rfl, rfl⟩, rfl⟩, rfl⟩

theorem borrowed_unchecked_preserves_reference :
    uncheckedFromRun .borrowed Unit () validationArgs.reference
      (.returned validationArgs.reference ()) := rfl

theorem borrowed_unchecked_rejects_equal_alias_different_record :
    ¬ uncheckedFromRun .borrowed Unit () validationArgs.reference
      (.returned ⟨20, validationArgs.info⟩ ()) := by
  intro wrong
  have identity := congrArg (fun result => result.1.identity) wrong
  contradiction

end SolanalibTest.Specs.Core.AnchorLifecycleValidation
