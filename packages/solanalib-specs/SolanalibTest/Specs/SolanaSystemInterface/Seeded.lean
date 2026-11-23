/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaSystemInterface.Seeded
public import Solanalib.Specs.SolanaSystemInterface.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaSystemInterface.Seeded

open Solanalib.Contracts.Model Solanalib.Specs.Core InstructionSystemExtended
open InstructionSystemExtended.Sample

theorem three_aliases_keep_separate_flags :
    seedSource.metas = [Instruction.accountMeta .zero true true,
      Instruction.accountMeta .zero false true, Instruction.accountMeta .zero true false] := rfl

theorem long_seed_is_encoded_without_validation :
    (seedBytes .zero (List.replicate 33 97) 7 32 .zero).take 44 =
      [3, 0, 0, 0] ++ List.replicate 32 0 ++ [33, 0, 0, 0, 0, 0, 0, 0] := by decide

theorem success_retires_temporary_and_keeps_result :
    InstructionBuilder.observe seedTypes.builder seedProviders seedAfter
      ⟨.zero, (0 : Nat), (1 : Nat)⟩ = some seedSource.value ∧
    InstructionBuilder.Sample.bytesAt seedAfter 0 = none ∧
    seedAfter.events = [10, 11, 20, 41] := ⟨rfl, rfl, rfl⟩

def copyFailure : SeedArgs seedTypes :=
  { seedArgs with
    strings := { seedArgs.strings with
      fromList := Callback.ofFunction fun (state : InstructionBuilder.Sample.State) _ =>
        .unwound (51 : Nat) { state with events := state.events ++ [13] }
      drop := fun _ _ _ => False }
    providers := { seedProviders with serialize := fun _ _ _ => False } }

def copyFailureState : InstructionBuilder.Sample.State :=
  { seedAllocated with events := [10, 13] }

def copyFailureAfter : InstructionBuilder.Sample.State :=
  InstructionBuilder.Sample.retireMetas copyFailureState 0

theorem copy_failure_drops_only_returned_metadata_owner :
    seedRun seedTypes {} copyFailure (.unwound (51 : Nat) copyFailureAfter) ∧
    copyFailureAfter.events = [10, 13, 40] ∧ copyFailureAfter.bytes = [] := by
  refine ⟨?_, rfl, rfl⟩
  refine ⟨.returned (0 : Nat) seedAllocated, rfl, ?_⟩
  refine ⟨.unwound (51 : Nat) copyFailureAfter, ?_, rfl⟩
  exact ⟨.unwound (51 : Nat) copyFailureState, rfl,
    .returned () copyFailureAfter, rfl, rfl⟩

def serializerError : SeedArgs seedTypes :=
  { seedArgs with
    providers := { seedProviders with
    serialize := Callback.ofFunction fun (state : InstructionBuilder.Sample.State) _ =>
      .returned (.error (5 : Nat)) { state with events := state.events ++ [25] } } }

def errorState : InstructionBuilder.Sample.State := { seedCopied with events := [10, 11, 25] }
def unwrapState : InstructionBuilder.Sample.State := { errorState with events := [10, 11, 25, 30] }
def metaDropState : InstructionBuilder.Sample.State := InstructionBuilder.Sample.retireMetas
  unwrapState 0
def stringDropState : InstructionBuilder.Sample.State := InstructionBuilder.Sample.retireBytes
  metaDropState 0

theorem serialization_error_unwraps_then_drops_accounts_then_string :
    seedRun seedTypes {} serializerError (.unwound (105 : Nat) stringDropState) ∧
    stringDropState.events = [10, 11, 25, 30, 40, 41] ∧
    stringDropState.metas = [none] ∧ stringDropState.bytes = [none] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  refine ⟨.returned (0 : Nat) seedAllocated, rfl, .returned (0 : Nat) seedCopied, ?_, ?_⟩
  · exact ⟨.returned (0 : Nat) seedCopied, rfl, rfl⟩
  · refine ⟨.unwound (105 : Nat) metaDropState, ?_, ?_⟩
    · refine ⟨.unwound (105 : Nat) unwrapState, ?_, ?_⟩
      · exact ⟨.returned (.error (5 : Nat)) errorState, rfl,
          .unwound (105 : Nat) unwrapState, rfl, rfl⟩
      · exact ⟨.returned () metaDropState, rfl, rfl⟩
    · exact ⟨.returned () stringDropState, rfl, rfl⟩

def serializationTerminal : SeedArgs seedTypes :=
  { seedArgs with
    providers := { seedProviders with
      serialize := Callback.ofFunction fun _ _ => .terminated (63 : Nat)
      metaVec := { seedProviders.metaVec with drop := fun _ _ _ => False } }
    strings := { seedArgs.strings with drop := fun _ _ _ => False } }

theorem serializer_terminal_skips_both_cleanup_scopes :
    seedRun seedTypes {} serializationTerminal (.terminated (63 : Nat)) := by
  refine ⟨.returned (0 : Nat) seedAllocated, rfl, .returned (0 : Nat) seedCopied, ?_, ?_⟩
  · exact ⟨.returned (0 : Nat) seedCopied, rfl, rfl⟩
  · exact ⟨.terminated (63 : Nat),
      ⟨.terminated (63 : Nat), ⟨.terminated (63 : Nat), rfl, rfl⟩, rfl⟩, rfl⟩

def cratesIo : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def selectedBuild : Versioning.Build where
  package := "solana-system-interface"
  version := "1.0.0"
  source := cratesIo
  features := some ["bincode"]
  dependencies := [⟨"solana-instruction", "2.3.3", cratesIo⟩, ⟨"bincode", "1.3.3", cratesIo⟩]

theorem compatible_seeded_identities :
    ["1.0.0", "1.1.0", "1.9.0"].all (fun version => decide
      ((Solanalib.Specs.SolanaSystemInterface.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities .instruction_create_account_with_seed
          =
        [⟨"solana-system-interface", version,
          "solana_system_interface::instruction::create_account_with_seed",
          "solana_system_interface::instruction::create_account_with_seed"⟩])) = true := by
            decide +kernel

theorem compatible_seeded_providers_admitted :
    ["2.2.1", "2.3.3", "2.4.0"].all (fun version => decide
      ((Solanalib.Specs.SolanaSystemInterface.Capabilities.catalog.forBuild { selectedBuild with
        version := "1.1.0"
        dependencies := [⟨"solana-instruction", version, cratesIo⟩, ⟨"bincode", "1.3.4", cratesIo⟩]
        }).identities .instruction_create_account_with_seed ≠ [])) = true := by decide +kernel

theorem outside_seeded_range_rejected :
    ["0.9.0", "2.0.0", "3.2.0", "1.1.0-rc.1"].all (fun version => decide
      ((Solanalib.Specs.SolanaSystemInterface.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities .instruction_create_account_with_seed
          = [])) =
      true := by decide +kernel

theorem seeded_bincode_feature_required :
    [none, some []].all (fun features => decide
      ((Solanalib.Specs.SolanaSystemInterface.Capabilities.catalog.forBuild
        { selectedBuild with version := "1.1.0", features := features }).identities
          .instruction_create_account_with_seed = [])) = true := by decide +kernel

theorem outside_seeded_provider_ranges_rejected :
    [("solana-instruction", "2.2.0"), ("solana-instruction", "3.0.0"),
      ("bincode", "1.3.2"), ("bincode", "2.0.0")].all (fun (package, version) => decide
      ((Solanalib.Specs.SolanaSystemInterface.Capabilities.catalog.forBuild { selectedBuild with
        version := "1.1.0"
        dependencies := selectedBuild.dependencies.map fun dependency =>
          if dependency.package = package then { dependency with version := version } else
            dependency
        }).identities .instruction_create_account_with_seed = [])) = true := by decide +kernel

theorem missing_seeded_providers_rejected :
    ["solana-instruction", "bincode"].all (fun package => decide
      ((Solanalib.Specs.SolanaSystemInterface.Capabilities.catalog.forBuild { selectedBuild with
        version := "1.1.0"
        dependencies := selectedBuild.dependencies.filter fun dependency => dependency.package !=
          package
        }).identities .instruction_create_account_with_seed = [])) = true := by decide +kernel

theorem ambiguous_or_forked_seeded_provider_rejected :
    let duplicate := { selectedBuild with
      version := "1.1.0"
      dependencies := selectedBuild.dependencies ++ [⟨"bincode", "1.3.4", cratesIo⟩] }
    let forked := { selectedBuild with
      version := "1.1.0"
      dependencies := selectedBuild.dependencies.map fun dependency =>
        if dependency.package = "solana-instruction" then
          { dependency with source := ⟨"git", "https://example.invalid/instruction", "fork"⟩ } else dependency }
    (Solanalib.Specs.SolanaSystemInterface.Capabilities.catalog.forBuild duplicate).identities
      .instruction_create_account_with_seed = [] ∧
    (Solanalib.Specs.SolanaSystemInterface.Capabilities.catalog.forBuild forked).identities
      .instruction_create_account_with_seed = [] := by decide +kernel

end SolanalibTest.Specs.SolanaSystemInterface.Seeded
