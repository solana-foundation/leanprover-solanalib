/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaProgram.Instruction
public import Solanalib.Specs.Core.InstructionCloneSample
public import Solanalib.Specs.SolanaProgram.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaProgram.InstructionClone

open Solanalib.Contracts.Model Solanalib.Specs.Core

open InstructionClone
open InstructionClone.Sample

theorem cloned_vectors_are_distinct_and_source_survives :
    Solanalib.Specs.SolanaProgram.instruction.Instruction.clone_run types before args
      (.returned ⟨.ofNat 9, (1 : Nat), (1 : Nat)⟩ after) ∧
    InstructionBuilder.Sample.metasAt after 0 = InstructionBuilder.Sample.metasAt before 0 ∧
    InstructionBuilder.Sample.bytesAt after 0 = InstructionBuilder.Sample.bytesAt before 0 ∧
    InstructionBuilder.Sample.metasAt after 1 = InstructionBuilder.Sample.metasAt before 0 ∧
    InstructionBuilder.Sample.bytesAt after 1 = InstructionBuilder.Sample.bytesAt before 0 := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  exact ⟨source, rfl,
    copyRun_returned types providers source before middle after (1 : Nat) (1 : Nat) rfl rfl⟩

def byteFailure : Args types :=
  { args with providers := { providers with bytes := { providers.bytes with
      copy := Callback.ofFunction fun (state : InstructionBuilder.Sample.State) _ =>
        .unwound (77 : Nat) { state with events := state.events ++ [22] } } } }

def byteFailureState : InstructionBuilder.Sample.State :=
  { middle with events := middle.events ++ [22] }

def byteFailureAfter : InstructionBuilder.Sample.State :=
  InstructionBuilder.Sample.retireMetas byteFailureState 1

theorem second_clone_unwind_drops_only_new_metadata :
    run types before byteFailure (.unwound (77 : Nat) byteFailureAfter) ∧
    InstructionBuilder.Sample.metasAt byteFailureAfter 1 = none ∧
    InstructionBuilder.Sample.metasAt byteFailureAfter 0 =
      InstructionBuilder.Sample.metasAt before 0 ∧
    byteFailureAfter.bytes = before.bytes ∧ byteFailureAfter.events = [10, 22, 40] := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  refine ⟨source, rfl, .returned (1 : Nat) middle, rfl, ?_⟩
  refine ⟨.unwound (77 : Nat) byteFailureState, ?_, ?_⟩
  · exact ⟨.unwound (77 : Nat) byteFailureState, rfl, rfl⟩
  · exact ⟨.returned () byteFailureAfter, rfl, rfl⟩

def metaTerminal : Args types :=
  { args with providers := { providers with
    metas := { providers.metas with copy := Callback.ofFunction fun _ _ => .terminated (81 : Nat) }
    bytes := { providers.bytes with copy := fun _ _ _ => False } } }

theorem first_clone_terminal_skips_second_clone :
    run types before metaTerminal (.terminated (81 : Nat)) :=
  ⟨source, rfl, .terminated (81 : Nat), rfl, rfl⟩

def byteTerminal : Args types :=
  { args with providers := { providers with
    metas := { providers.metas with vectors := { providers.metas.vectors with
      drop := fun _ _ _ => False } }
    bytes := { providers.bytes with copy := Callback.ofFunction fun _ _ => .terminated (82 : Nat) }
      } }

theorem second_clone_terminal_skips_cleanup :
    run types before byteTerminal (.terminated (82 : Nat)) :=
  ⟨source, rfl, .returned (1 : Nat) middle, rfl,
    .terminated (82 : Nat), ⟨.terminated (82 : Nat), rfl, rfl⟩, rfl⟩

theorem cannot_return_borrowed_vectors (state : InstructionBuilder.Sample.State) :
    ¬ run types before args (.returned source state) := by
  simp [run, copyRun, args, providers, source, before,
    InstructionBuilder.Sample.metasAt, InstructionBuilder.Sample.bytesAt,
    InstructionBuilder.Sample.allocateMetas, InstructionBuilder.Sample.allocateBytes,
    Callback.bind, Callback.map, Callback.ofFunction, Outcome.map,
    Owned.protect, Owned.onUnwind]
  intro impossible
  cases impossible

end SolanalibTest.Specs.SolanaProgram.InstructionClone

/- Per-operation compatibility selection. Synthetic versions carry no native or ABI credit. -/
namespace SolanalibTest.Specs.SolanaProgram.InstructionClone.LegacyCompatibility

@[expose] public section

set_option autoImplicit false

namespace InstructionClone

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "solana-program"
  version := "1.15.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "1.15.3" }

def identityCases (version : String) : List (Solanalib.Specs.SolanaProgram.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.instruction_Instruction_clone, [⟨"solana-program", version, "core::clone::Clone::clon\
      e",
      "<solana_program::instruction::Instruction as core::clone::Clone>::clone"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["1.15.1", "1.16.0", "1.15.3-rc.1"].all (fun version =>
      (identityCases version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with version := version }).identities
          entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_origin_rejected :
    (identityCases compatibleBuild.version).all (fun entry =>
      ((catalog.forBuild { compatibleBuild with source :=
        ⟨"git", "https://example.org/source-fork", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
          a"⟩ }).identities entry.1).isEmpty) = true := by decide +kernel

end InstructionClone

end

end SolanalibTest.Specs.SolanaProgram.InstructionClone.LegacyCompatibility
