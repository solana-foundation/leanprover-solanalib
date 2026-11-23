/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaDefineSyscall.Cpi
public import Solanalib.Specs.SolanaDefineSyscall.Capabilities
public import SolanalibTest.Specs.Core.OpaqueCpi

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaDefineSyscall.Cpi

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi
open SolanalibTest.Specs.Core.OpaqueCpi (registry onchainTarget)
open Solanalib.Specs.SolanaDefineSyscall.Capabilities (catalog)

/-- Every registered signature uses the same exact closed finite execution
witness, while its source identity and ABI remain separate review obligations. -/
theorem signature_has_execution : FamilyHasExecution
    Solanalib.Specs.SolanaDefineSyscall.definitions.sol_invoke_signed_rust_contract
      Solanalib.Specs.SolanaDefineSyscall.definitions.sol_invoke_signed_rust_run
    Solanalib.Specs.SolanaDefineSyscall.definitions.sol_invoke_signed_rust_sample :=
  Solanalib.Specs.SolanaDefineSyscall.definitions.sol_invoke_signed_rust_has_execution

def reviewedBuild : Versioning.Build where
  package := "solana-define-syscall"
  version := "2.3.0"
  source := registry
  target := onchainTarget
  targetFeatures := some []

/-- Synthetic compatible versions exercise declared selection assumptions;
they are not additional inspected or native-tested releases. -/
def compatibleBuild : Versioning.Build :=
  { reviewedBuild with version := "2.3.1" }

/-- The inspected raw declaration retains its exact provider, reference release
and complete function name. Its extern-C boundary remains opaque. -/
theorem reviewed_build_admitted :
    (catalog.forBuild reviewedBuild).identities .definitions_sol_invoke_signed_rust =
      [⟨"solana-define-syscall", "2.3.0",
        "solana_define_syscall::definitions::sol_invoke_signed_rust",
        "solana_define_syscall::definitions::sol_invoke_signed_rust"⟩] := by decide +kernel

/-- Compatibility keeps the actual calling-package version and exact source name. -/
theorem compatible_build_actual_identity :
    (catalog.forBuild compatibleBuild).identities .definitions_sol_invoke_signed_rust =
      [⟨"solana-define-syscall", "2.3.1",
        "solana_define_syscall::definitions::sol_invoke_signed_rust",
        "solana_define_syscall::definitions::sol_invoke_signed_rust"⟩] := by decide +kernel

theorem lower_bound_and_prerelease_rejected :
    ["2.2.9", "2.3.1-rc.1"].all (fun version =>
      ((catalog.forBuild { compatibleBuild with version := version }).identities
        .definitions_sol_invoke_signed_rust).isEmpty) = true := by decide +kernel

theorem outside_range_releases_rejected :
    (catalog.forBuild { reviewedBuild with version := "5.1.0" }
      ).identities .definitions_sol_invoke_signed_rust = [] ∧
    (catalog.forBuild { reviewedBuild with version := "4.0.0" }
      ).identities .definitions_sol_invoke_signed_rust = [] := by decide +kernel

/-- The original reference profile retains its own upper boundary even when
another inspected declaration has a separate compatible range. -/
theorem original_profile_retains_its_upper_bound :
    let profiles := (catalog.applicability .definitions_sol_invoke_signed_rust).filter
      (fun profile => profile.id == "raw-cpi-rust-solana-define-syscall-2.3.0")
    profiles.length = 1 ∧
      profiles.all (fun profile =>
        decide (profile.releases = ["2.3.0"] ∧
          profile.compatibleRanges = [⟨"2.3.0", "3.0.0"⟩]) &&
        !(profile.matches { reviewedBuild with version := "3.0.0" })) = true := by
  decide +kernel

/-- The separately inspected modern declaration retains its actual identity. -/
theorem modern_reference_has_its_own_identity :
    (catalog.forBuild { reviewedBuild with version := "3.0.0" }
      ).identities .definitions_sol_invoke_signed_rust =
      [⟨"solana-define-syscall", "3.0.0",
        "solana_define_syscall::definitions::sol_invoke_signed_rust",
        "solana_define_syscall::definitions::sol_invoke_signed_rust"⟩] := by decide +kernel

theorem same_release_fork_rejected :
    (catalog.forBuild { reviewedBuild with source :=
      ⟨"git", "https://example.org/syscall-fork", "0123456789012345678901234567890123456789"⟩
      }).identities .definitions_sol_invoke_signed_rust = [] := by decide +kernel

theorem every_target_fact_is_required :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.target.all (fun fact =>
        ((catalog.forBuild { build with target :=
          (build.target.filter (fun kept => kept.field != fact.field)) }).identities
          .definitions_sol_invoke_signed_rust).isEmpty)) = true := by decide +kernel

theorem changed_target_facts_rejected :
    [reviewedBuild, compatibleBuild].all (fun build =>
      ([⟨"os", "linux"⟩, ⟨"pointer_width", "32"⟩, ⟨"endian", "big"⟩, ⟨"panic", "unwind"⟩] :
        List Versioning.TargetFact).all (fun changed =>
          ((catalog.forBuild { build with target :=
            (build.target.map (fun fact => if fact.field = changed.field then changed else fact))
              }).identities
            .definitions_sol_invoke_signed_rust).isEmpty)) = true := by decide +kernel

theorem static_or_unknown_dispatch_rejected :
    [reviewedBuild, compatibleBuild].all (fun build =>
      [none, some ["static-syscalls"]].all (fun targetFeatures =>
        ((catalog.forBuild { build with targetFeatures := targetFeatures }).identities
          .definitions_sol_invoke_signed_rust).isEmpty)) = true := by decide +kernel

/-- Duplicate target facts remain unresolved even when their values agree. -/
theorem ambiguous_target_facts_rejected :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.target.all (fun fact =>
        ((catalog.forBuild { build with target := build.target ++ [fact] }).identities
          .definitions_sol_invoke_signed_rust).isEmpty)) = true := by decide +kernel

theorem compatible_source_fork_rejected :
    (catalog.forBuild { compatibleBuild with source :=
      ⟨"git", "https://example.org/cpi-fork", "0123456789012345678901234567890123456789"⟩ }).identities
        .definitions_sol_invoke_signed_rust = [] := by decide +kernel

end SolanalibTest.Specs.SolanaDefineSyscall.Cpi
