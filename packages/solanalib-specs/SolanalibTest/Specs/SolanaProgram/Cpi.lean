/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.Core.OpaqueCpi
public import Solanalib.Specs.SolanaProgram.Cpi
public import Solanalib.Specs.SolanaProgram.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaProgram.Cpi

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi
open SolanalibTest.Specs.Core.OpaqueCpi (registry onchainTarget dependency)
open Solanalib.Specs.SolanaProgram.Capabilities (catalog)

theorem signature_has_execution :
    FamilyHasExecution Solanalib.Specs.SolanaProgram.program.invoke_signed_contract
      Solanalib.Specs.SolanaProgram.program.invoke_signed_run
      Solanalib.Specs.SolanaProgram.program.invoke_signed_sample :=
  Solanalib.Specs.SolanaProgram.program.invoke_signed_has_execution

theorem clone_abort_retained : Sdk.Owned.Run OwnedWitness.index OwnedWitness.before
    Witness.signedArgs (.terminated (.local ())) := OwnedWitness.allocation_terminal

theorem cleanup_abort_retained : Sdk.Owned.Run OwnedWitness.index OwnedWitness.before
    Witness.signedArgs (.terminated (.local ())) := OwnedWitness.cleanup_terminal

theorem borrow_failure_before_clone :
    ¬ Sdk.Owned.Run OwnedWitness.index
      ⟨⟨Witness.before, SolanalibTest.Specs.Core.OpaqueCpi.lamportsBorrowed⟩, none⟩
      SolanalibTest.Specs.Core.OpaqueCpi.signed (.terminated (.local ())) :=
  Sdk.Owned.borrow_error_blocks_local_terminal rfl

def reviewedBuild : Versioning.Build where
  package := "solana-program"
  version := "2.3.0"
  source := registry
  target := onchainTarget
  targetFeatures := some []
  dependencies :=
    [dependency "solana-account-info" "2.3.0", dependency "solana-instruction" "2.3.3",
     dependency "solana-stable-layout" "2.2.1", dependency "solana-program-error" "2.2.2",
     dependency "solana-cpi" "2.2.1"]

/-- Synthetic compatible versions exercise declared selection assumptions;
they are not additional inspected or native-tested releases. -/
def compatibleBuild : Versioning.Build :=
  { reviewedBuild with version := "2.3.1", dependencies := (reviewedBuild.dependencies.map (fun dep
    => { dep with version := "2.9.0" })) }

/-- The inspected reference retains its exact defining package, release and
function name within the declared compatibility line. -/
theorem reviewed_build_admitted :
    (catalog.forBuild reviewedBuild).identities .program_invoke_signed =
      [⟨"solana-program", "2.3.0", "solana_program::program::invoke_signed",
        "solana_program::program::invoke_signed"⟩] := by decide +kernel

/-- Compatibility keeps the actual calling-package version and exact source name. -/
theorem compatible_build_actual_identity :
    [{ reviewedBuild with version := "2.3.1" }, compatibleBuild].all (fun build => decide
      ((catalog.forBuild build).identities .program_invoke_signed =
        [⟨"solana-program", "2.3.1", "solana_program::program::invoke_signed",
          "solana_program::program::invoke_signed"⟩])) = true := by decide +kernel

theorem lower_bound_and_prerelease_rejected :
    ["2.2.0", "2.3.1-rc.1"].all (fun version =>
      ((catalog.forBuild { compatibleBuild with version := version }).identities
        .program_invoke_signed).isEmpty) = true := by decide +kernel

/-- The monolithic 1.18.26 implementation has its own reviewed profile and
does not require the split dependencies of the later wrapper. -/
theorem program_1_18_26_build_admitted :
    (catalog.forBuild { reviewedBuild with version := "1.18.26", dependencies := [] }
      ).identities .program_invoke_signed =
      [⟨"solana-program", "1.18.26", "solana_program::program::invoke_signed",
        "solana_program::program::invoke_signed"⟩] := by decide +kernel

theorem historical_or_new_major_release_rejected :
    (catalog.forBuild { reviewedBuild with version := "1.18.25" }
      ).identities .program_invoke_signed = [] ∧
    (catalog.forBuild { reviewedBuild with version := "3.0.0" }
      ).identities .program_invoke_signed = [] := by decide +kernel

theorem reviewed_instruction_alternative_admitted :
    (catalog.forBuild { reviewedBuild with dependencies :=
      (reviewedBuild.dependencies.map (fun dep => if dep.package = "solana-instruction" then { dep
        with version := "2.2.1" }
        else dep)) }).identities .program_invoke_signed =
      (catalog.forBuild reviewedBuild).identities .program_invoke_signed := by decide +kernel

theorem same_release_fork_rejected :
    (catalog.forBuild { reviewedBuild with source :=
      ⟨"git", "https://example.org/program-fork", "0123456789012345678901234567890123456789"⟩
      }).identities .program_invoke_signed = [] := by decide +kernel

/-- The owned stable clone depends on each listed provider, including the
exact solana-cpi implementation selected by this wrapper. -/
theorem every_dependency_is_required :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        ((catalog.forBuild { build with dependencies :=
          (build.dependencies.filter (fun kept => kept.package != dep.package)) }).identities
          .program_invoke_signed).isEmpty)) = true := by decide +kernel

theorem every_dependency_rejects_outside_range_versions :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        ((catalog.forBuild { build with dependencies :=
          (build.dependencies.map (fun kept => if kept.package = dep.package then
            { kept with version := "99.0.0" } else kept)) }).identities
          .program_invoke_signed).isEmpty)) = true := by decide +kernel

theorem every_dependency_rejects_ambiguous_resolution :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        ((catalog.forBuild { build with dependencies := build.dependencies ++ [dep] }).identities
          .program_invoke_signed).isEmpty)) = true := by decide +kernel

theorem every_dependency_rejects_a_fork :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        ((catalog.forBuild { build with dependencies :=
          (build.dependencies.map (fun kept => if kept.package = dep.package then { kept with
            source :=
            ⟨"git", "https://example.org/dependency-fork",
              "0123456789012345678901234567890123456789"⟩ } else kept)) }).identities
          .program_invoke_signed).isEmpty)) = true := by decide +kernel

theorem every_target_fact_is_required :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.target.all (fun fact =>
        ((catalog.forBuild { build with target :=
          (build.target.filter (fun kept => kept.field != fact.field)) }).identities
          .program_invoke_signed).isEmpty)) = true := by decide +kernel

theorem changed_target_facts_rejected :
    [reviewedBuild, compatibleBuild].all (fun build =>
      ([⟨"os", "linux"⟩, ⟨"pointer_width", "32"⟩, ⟨"endian", "big"⟩, ⟨"panic", "unwind"⟩] :
        List Versioning.TargetFact).all (fun changed =>
          ((catalog.forBuild { build with target :=
            (build.target.map (fun fact => if fact.field = changed.field then changed else fact))
              }).identities
            .program_invoke_signed).isEmpty)) = true := by decide +kernel

theorem static_or_unknown_dispatch_rejected :
    [reviewedBuild, compatibleBuild].all (fun build =>
      [none, some ["static-syscalls"]].all (fun targetFeatures =>
        ((catalog.forBuild { build with targetFeatures := targetFeatures }).identities
          .program_invoke_signed).isEmpty)) = true := by decide +kernel

/-- Duplicate target facts remain unresolved even when their values agree. -/
theorem ambiguous_target_facts_rejected :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.target.all (fun fact =>
        ((catalog.forBuild { build with target := build.target ++ [fact] }).identities
          .program_invoke_signed).isEmpty)) = true := by decide +kernel

theorem compatible_source_fork_rejected :
    (catalog.forBuild { compatibleBuild with source :=
      ⟨"git", "https://example.org/cpi-fork", "0123456789012345678901234567890123456789"⟩ }).identities
        .program_invoke_signed = [] := by decide +kernel

/-- Each provider has its own lower boundary; all these SDK 2 providers also
reject the exclusive next-major boundary and a prerelease inside the numeric interval. -/
theorem dependency_boundaries_and_prereleases_rejected :
    let below : List (String × String) :=
      [("solana-account-info", "2.2.9"),
      ("solana-instruction", "2.2.0"),
      ("solana-stable-layout", "2.2.0"),
      ("solana-program-error", "2.2.1"),
      ("solana-cpi", "2.2.0")]
    below.all (fun changed =>
      ((catalog.forBuild { compatibleBuild with dependencies :=
        (compatibleBuild.dependencies.map (fun dep => if dep.package = changed.1 then
          { dep with version := changed.2 } else dep)) }).identities
            .program_invoke_signed).isEmpty) = true ∧
    compatibleBuild.dependencies.all (fun dep =>
      ["3.0.0", "2.9.0-rc.1"].all (fun version =>
        ((catalog.forBuild { compatibleBuild with dependencies :=
          (compatibleBuild.dependencies.map (fun kept => if kept.package = dep.package then
            { kept with version := version } else kept)) }).identities
              .program_invoke_signed).isEmpty)) = true := by
  decide +kernel

/-- Forwarded native inputs retain a manual conditional Entry. No build is
automatically admitted for either partial interface. -/
theorem forwarded_inputs_have_no_automatic_identity (build : Versioning.Build) :
    (catalog.forBuild build).identities .program_invoke_forwarded_inputs = [] := by rfl

theorem signed_forwarded_inputs_have_no_automatic_identity (build : Versioning.Build) :
    (catalog.forBuild build).identities .program_invoke_signed_forwarded_inputs = [] := by rfl

end SolanalibTest.Specs.SolanaProgram.Cpi

namespace SolanalibTest.Specs.SolanaProgram.Cpi.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def program_invokeBuild : Versioning.Build where
  package := "solana-program"
  version := "2.2.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "ab\
    ort"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-account-info", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-stable-layout", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-cpi", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def program_invokeCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-2.2.1; eligible
  (program_invokeBuild, true),
  -- inspected-reference-2.3.0; eligible
  ({ program_invokeBuild with version := "2.3.0" }, true),
  -- lower; eligible
  (program_invokeBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ program_invokeBuild with version := "2.2.98" }, true),
  -- exclusive-upper; unsupported
  ({ program_invokeBuild with version := "3.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ program_invokeBuild with version := "2.2.1-rc.1" }, false),
  -- wrong-package; unsupported
  ({ program_invokeBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ program_invokeBuild with source := ⟨"git", "https://example.invalid/review-fork", "bbb\
    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ program_invokeBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"p\
    anic",
    "abort"⟩] }, false),
  -- wrong-target-os; unsupported
  ({ program_invokeBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian",
    "little"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ program_invokeBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩, ⟨"panic",
    "abort"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ program_invokeBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "linux"⟩, ⟨"en\
    dian",
    "little"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ program_invokeBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"panic",
    "abort"⟩] }, false),
  -- wrong-target-endian; unsupported
  ({ program_invokeBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endia\
    n",
    "linux"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-panic; unresolved
  ({ program_invokeBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endia\
    n",
    "little"⟩] }, false),
  -- wrong-target-panic; unsupported
  ({ program_invokeBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endia\
    n",
    "little"⟩, ⟨"panic", "linux"⟩] }, false),
  -- missing-target_features; unresolved
  ({ program_invokeBuild with targetFeatures := none }, false),
  -- wrong-target_features; unsupported
  ({ program_invokeBuild with targetFeatures := some ["static-syscalls"] }, false),
  -- dependency-reference-solana-account-info-2.2.1; eligible
  (program_invokeBuild, true),
  -- dependency-reference-solana-account-info-2.3.0; eligible
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-account-info" then { dependency with version := "2.\
      3.0" }
    else dependency)) }, true),
  -- dependency-solana-account-info-lower; eligible
  (program_invokeBuild, true),
  -- dependency-solana-account-info-hypothetical-declaration-probe; eligible
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-account-info" then { dependency with version := "2.\
      2.98" }
    else dependency)) }, true),
  -- dependency-solana-account-info-exclusive-upper; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-account-info" then { dependency with version := "3.\
      0.0" }
    else dependency)) }, false),
  -- dependency-solana-account-info-unlisted-prerelease; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-account-info" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-account-info; unresolved
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.filter (fun
    dependency => dependency.package != "solana-account-info")) }, false),
  -- wrong-dependency-origin-solana-account-info; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package ==
    "solana-account-info" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-account-info; ValueError containing Ambiguous dependency
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies ++ [⟨"solan\
    a-account-info", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
      ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (program_invokeBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-instruction" then { dependency with version := "2.3\
      .3" }
    else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (program_invokeBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-instruction" then { dependency with version := "2.2\
      .98" }
    else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-instruction" then { dependency with version := "3.0\
      .0" }
    else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-instruction" then { dependency with version := "2.2\
      .1-rc.1"
    } else dependency)) }, false),
  -- missing-dependency-solana-instruction; unresolved
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.filter (fun
    dependency => dependency.package != "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies ++ [⟨"solan\
    a-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- dependency-reference-solana-stable-layout-2.2.1; eligible
  (program_invokeBuild, true),
  -- dependency-solana-stable-layout-lower; eligible
  (program_invokeBuild, true),
  -- dependency-solana-stable-layout-hypothetical-declaration-probe; eligible
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-stable-layout" then { dependency with version := "2\
      .2.98" }
    else dependency)) }, true),
  -- dependency-solana-stable-layout-exclusive-upper; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-stable-layout" then { dependency with version := "3\
      .0.0" }
    else dependency)) }, false),
  -- dependency-solana-stable-layout-unlisted-prerelease; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-stable-layout" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-stable-layout; unresolved
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.filter (fun
    dependency => dependency.package != "solana-stable-layout")) }, false),
  -- wrong-dependency-origin-solana-stable-layout; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package ==
    "solana-stable-layout" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-stable-layout; ValueError containing Ambiguous dependency
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies ++ [⟨"solan\
    a-stable-layout", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
      ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (program_invokeBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-program-error" then { dependency with version := "2\
      .2.2" }
    else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (program_invokeBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-program-error" then { dependency with version := "2\
      .2.98" }
    else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-program-error" then { dependency with version := "3\
      .0.0" }
    else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-program-error" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-program-error; unresolved
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.filter (fun
    dependency => dependency.package != "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies ++ [⟨"solan\
    a-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
      ""⟩⟩]) }, false),
  -- dependency-reference-solana-cpi-2.2.1; eligible
  (program_invokeBuild, true),
  -- dependency-solana-cpi-lower; eligible
  (program_invokeBuild, true),
  -- dependency-solana-cpi-hypothetical-declaration-probe; eligible
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-cpi" then { dependency with version := "2.2.98" } else
    dependency)) }, true),
  -- dependency-solana-cpi-exclusive-upper; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-cpi" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-cpi-unlisted-prerelease; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-cpi" then { dependency with version := "2.2.1-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-solana-cpi; unresolved
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.filter (fun
    dependency => dependency.package != "solana-cpi")) }, false),
  -- wrong-dependency-origin-solana-cpi; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package ==
    "solana-cpi" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-cpi; ValueError containing Ambiguous dependency
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies ++ [⟨"solan\
    a-cpi", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invokeBuild with version := "2.2.0" }, false),
  -- dependency-solana-account-info-below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-account-info" then { dependency with version := "2.\
      2.0" }
    else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-instruction" then { dependency with version := "2.2\
      .0" }
    else dependency)) }, false),
  -- dependency-solana-stable-layout-below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-stable-layout" then { dependency with version := "2\
      .2.0" }
    else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-program-error" then { dependency with version := "2\
      .2.0" }
    else dependency)) }, false),
  -- dependency-solana-cpi-below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invokeBuild with dependencies := (program_invokeBuild.dependencies.map (fun dependency
    => if dependency.package == "solana-cpi" then { dependency with version := "2.2.0" } else
    dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem program_invoke_profile_controls :
    program_invokeCases.all (fun test =>
      (((Solanalib.Specs.SolanaProgram.Capabilities.catalog.applicability .program_invoke).any
        (fun profile => ["program-2.2.1-owned-invoke"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem program_invoke_callable_identities :
    ["2.2.1", "2.3.0", "2.2.98"].all (fun version =>
      (((Solanalib.Specs.SolanaProgram.Capabilities.catalog.forBuild
        { program_invokeBuild with version := version }).identities .program_invoke).eraseDups ==
        [⟨"solana-program", version, "solana_program::program::invoke",
          "solana_program::program::invoke"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def program_invoke_signedBuild : Versioning.Build where
  package := "solana-program"
  version := "2.2.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "ab\
    ort"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-account-info", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-stable-layout", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-cpi", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def program_invoke_signedCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-2.2.1; eligible
  (program_invoke_signedBuild, true),
  -- lower; eligible
  (program_invoke_signedBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ program_invoke_signedBuild with version := "2.2.98" }, true),
  -- exclusive-upper; unsupported
  ({ program_invoke_signedBuild with version := "2.3.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ program_invoke_signedBuild with version := "2.2.1-rc.1" }, false),
  -- wrong-package; unsupported
  ({ program_invoke_signedBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ program_invoke_signedBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ program_invoke_signedBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩,
    ⟨"panic", "abort"⟩] }, false),
  -- wrong-target-os; unsupported
  ({ program_invoke_signedBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ program_invoke_signedBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩, ⟨"p\
    anic",
    "abort"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ program_invoke_signedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "linux"⟩,
    ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ program_invoke_signedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"panic", "abort"⟩] }, false),
  -- wrong-target-endian; unsupported
  ({ program_invoke_signedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "linux"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-panic; unresolved
  ({ program_invoke_signedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- wrong-target-panic; unsupported
  ({ program_invoke_signedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩, ⟨"panic", "linux"⟩] }, false),
  -- missing-target_features; unresolved
  ({ program_invoke_signedBuild with targetFeatures := none }, false),
  -- wrong-target_features; unsupported
  ({ program_invoke_signedBuild with targetFeatures := some ["static-syscalls"] }, false),
  -- dependency-reference-solana-account-info-2.2.1; eligible
  (program_invoke_signedBuild, true),
  -- dependency-reference-solana-account-info-2.3.0; eligible
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-account-info" then { dependency with
    version := "2.3.0" } else dependency)) }, true),
  -- dependency-solana-account-info-lower; eligible
  (program_invoke_signedBuild, true),
  -- dependency-solana-account-info-hypothetical-declaration-probe; eligible
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-account-info" then { dependency with
    version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-account-info-exclusive-upper; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-account-info" then { dependency with
    version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-account-info-unlisted-prerelease; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-account-info" then { dependency with
    version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-account-info; unresolved
  ({ program_invoke_signedBuild with dependencies :=
    (program_invoke_signedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-account-info")) }, false),
  -- wrong-dependency-origin-solana-account-info; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package ==
    "solana-account-info" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-account-info; ValueError containing Ambiguous dependency
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies ++ [⟨
    "solana-account-info", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (program_invoke_signedBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-instruction" then { dependency with version
    := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (program_invoke_signedBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-instruction" then { dependency with version
    := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-instruction" then { dependency with version
    := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-instruction" then { dependency with version
    := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-instruction; unresolved
  ({ program_invoke_signedBuild with dependencies :=
    (program_invoke_signedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-stable-layout-2.2.1; eligible
  (program_invoke_signedBuild, true),
  -- dependency-solana-stable-layout-lower; eligible
  (program_invoke_signedBuild, true),
  -- dependency-solana-stable-layout-hypothetical-declaration-probe; eligible
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-stable-layout" then { dependency with
    version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-stable-layout-exclusive-upper; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-stable-layout" then { dependency with
    version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-stable-layout-unlisted-prerelease; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-stable-layout" then { dependency with
    version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-stable-layout; unresolved
  ({ program_invoke_signedBuild with dependencies :=
    (program_invoke_signedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-stable-layout")) }, false),
  -- wrong-dependency-origin-solana-stable-layout; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package ==
    "solana-stable-layout" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-stable-layout; ValueError containing Ambiguous dependency
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies ++ [⟨
    "solana-stable-layout", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (program_invoke_signedBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-program-error" then { dependency with
    version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (program_invoke_signedBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-program-error" then { dependency with
    version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-program-error" then { dependency with
    version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-program-error" then { dependency with
    version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-program-error; unresolved
  ({ program_invoke_signedBuild with dependencies :=
    (program_invoke_signedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-cpi-2.2.1; eligible
  (program_invoke_signedBuild, true),
  -- dependency-solana-cpi-lower; eligible
  (program_invoke_signedBuild, true),
  -- dependency-solana-cpi-hypothetical-declaration-probe; eligible
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-cpi" then { dependency with version :=
    "2.2.98" } else dependency)) }, true),
  -- dependency-solana-cpi-exclusive-upper; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-cpi" then { dependency with version :=
    "3.0.0" } else dependency)) }, false),
  -- dependency-solana-cpi-unlisted-prerelease; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-cpi" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-cpi; unresolved
  ({ program_invoke_signedBuild with dependencies :=
    (program_invoke_signedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-cpi")) }, false),
  -- wrong-dependency-origin-solana-cpi; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package ==
    "solana-cpi" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-cpi; ValueError containing Ambiguous dependency
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies ++ [⟨
    "solana-cpi", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invoke_signedBuild with version := "2.2.0" }, false),
  -- dependency-solana-account-info-below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-account-info" then { dependency with
    version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-instruction" then { dependency with version
    := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-stable-layout-below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-stable-layout" then { dependency with
    version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-program-error" then { dependency with
    version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-cpi-below-lower-bound-fixture-2.2.0; unsupported
  ({ program_invoke_signedBuild with dependencies := (program_invoke_signedBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-cpi" then { dependency with version :=
    "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem program_invoke_signed_profile_controls :
    program_invoke_signedCases.all (fun test =>
      (((Solanalib.Specs.SolanaProgram.Capabilities.catalog.applicability
        .program_invoke_signed).any
        (fun profile => ["program-2.2.1-owned-invoke_signed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem program_invoke_signed_callable_identities :
    ["2.2.1", "2.2.9", "2.2.98"].all (fun version =>
      (((Solanalib.Specs.SolanaProgram.Capabilities.catalog.forBuild
        { program_invoke_signedBuild with version := version }).identities
          .program_invoke_signed).eraseDups ==
        [⟨"solana-program", version, "solana_program::program::invoke_signed",
          "solana_program::program::invoke_signed"⟩])) = true := by
  decide +kernel

/-- The earlier profile remains usable alongside the incoming interval. -/
def program_invoke_signed_inheritedBuild : Versioning.Build where
  package := "solana-program"
  version := "2.3.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "ab\
    ort"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-account-info", "2.3.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-stable-layout", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-cpi", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

set_option maxRecDepth 8192 in
theorem program_invoke_signed_inherited_callable_identity :
    ((Solanalib.Specs.SolanaProgram.Capabilities.catalog.forBuild
      program_invoke_signed_inheritedBuild).identities .program_invoke_signed).eraseDups =
      [⟨"solana-program", "2.3.0", "solana_program::program::invoke_signed",
        "solana_program::program::invoke_signed"⟩] := by
  decide +kernel

end SolanalibTest.Specs.SolanaProgram.Cpi.Pr575Compatibility

namespace SolanalibTest.Specs.SolanaProgram.LegacyCpiCompatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (Key catalog)

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal Rust identities are independent of generated profile selection. -/
def referenceRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.syscalls_definitions_sol_create_program_address, {
    package := "solana-program", version :=
    "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
    targetFeatures := some [] },
      [("solana_program::syscalls::definitions::sol_create_program_address",
        "solana_program::syscalls::definitions::sol_create_program_address")]),
    (.syscalls_definitions_sol_get_clock_sysvar, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
      targetFeatures := some [] },
      [("solana_program::syscalls::definitions::sol_get_clock_sysvar",
        "solana_program::syscalls::definitions::sol_get_clock_sysvar")]),
    (.syscalls_definitions_sol_get_rent_sysvar, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
      targetFeatures := some [] },
      [("solana_program::syscalls::definitions::sol_get_rent_sysvar",
        "solana_program::syscalls::definitions::sol_get_rent_sysvar")]),
    (.syscalls_definitions_sol_invoke_signed_rust, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
      ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩], targetFeatures := some [] },
      [("solana_program::syscalls::definitions::sol_invoke_signed_rust",
        "solana_program::syscalls::definitions::sol_invoke_signed_rust")]),
    (.syscalls_definitions_sol_memcpy_, {
      package := "solana-program", version := "1.18.26", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩], targetFeatures := some []
      },
      [("solana_program::syscalls::definitions::sol_memcpy_",
        "solana_program::syscalls::definitions::sol_memcpy_")]),
    (.syscalls_definitions_sol_memset_, {
      package := "solana-program", version := "1.18.26", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩], targetFeatures := some []
      },
      [("solana_program::syscalls::definitions::sol_memset_",
        "solana_program::syscalls::definitions::sol_memset_")]),
    (.syscalls_definitions_sol_sha256, {
      package := "solana-program", version := "1.18.26", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩], targetFeatures := some []
      },
      [("solana_program::syscalls::definitions::sol_sha256",
        "solana_program::syscalls::definitions::sol_sha256")]),
    (.syscalls_definitions_sol_try_find_program_address, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
      targetFeatures := some [] },
      [("solana_program::syscalls::definitions::sol_try_find_program_address",
        "solana_program::syscalls::definitions::sol_try_find_program_address")]),
    (.system_instruction_create_account_with_seed, {
      package := "solana-program", version :=
      "1.15.2", source := registry, dependencies := [⟨"bincode", "1.3.3", registry⟩] },
      [("solana_program::system_instruction::create_account_with_seed",
        "solana_program::system_instruction::create_account_with_seed")]),
    (.system_instruction_create_account_with_seed, {
      package := "solana-program", version :=
      "1.18.26", source := registry, dependencies := [⟨"bincode", "1.3.3", registry⟩] },
      [("solana_program::system_instruction::create_account_with_seed",
        "solana_program::system_instruction::create_account_with_seed")]),
    (.program_invoke_signed, {
      package := "solana-program", version := "1.18.26", source :=
      registry, target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩,
      ⟨"panic", "abort"⟩], targetFeatures := some [] },
      [("solana_program::program::invoke_signed", "solana_program::program::invoke_signed")])]

/-- These uninspected patch versions exercise compatibility assumptions only. -/
def compatibleRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.syscalls_definitions_sol_create_program_address, {
    package := "solana-program", version :=
    "1.18.27", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
    targetFeatures := some [] },
      [("solana_program::syscalls::definitions::sol_create_program_address",
        "solana_program::syscalls::definitions::sol_create_program_address")]),
    (.syscalls_definitions_sol_get_clock_sysvar, {
      package := "solana-program", version :=
      "1.18.27", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
      targetFeatures := some [] },
      [("solana_program::syscalls::definitions::sol_get_clock_sysvar",
        "solana_program::syscalls::definitions::sol_get_clock_sysvar")]),
    (.syscalls_definitions_sol_get_rent_sysvar, {
      package := "solana-program", version :=
      "1.18.27", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
      targetFeatures := some [] },
      [("solana_program::syscalls::definitions::sol_get_rent_sysvar",
        "solana_program::syscalls::definitions::sol_get_rent_sysvar")]),
    (.syscalls_definitions_sol_invoke_signed_rust, {
      package := "solana-program", version :=
      "1.18.27", source := registry, target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
      ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩], targetFeatures := some [] },
      [("solana_program::syscalls::definitions::sol_invoke_signed_rust",
        "solana_program::syscalls::definitions::sol_invoke_signed_rust")]),
    (.syscalls_definitions_sol_memcpy_, {
      package := "solana-program", version := "1.18.27", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩], targetFeatures := some []
      },
      [("solana_program::syscalls::definitions::sol_memcpy_",
        "solana_program::syscalls::definitions::sol_memcpy_")]),
    (.syscalls_definitions_sol_memset_, {
      package := "solana-program", version := "1.18.27", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩], targetFeatures := some []
      },
      [("solana_program::syscalls::definitions::sol_memset_",
        "solana_program::syscalls::definitions::sol_memset_")]),
    (.syscalls_definitions_sol_sha256, {
      package := "solana-program", version := "1.18.27", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩], targetFeatures := some []
      },
      [("solana_program::syscalls::definitions::sol_sha256",
        "solana_program::syscalls::definitions::sol_sha256")]),
    (.syscalls_definitions_sol_try_find_program_address, {
      package := "solana-program", version :=
      "1.18.27", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
      targetFeatures := some [] },
      [("solana_program::syscalls::definitions::sol_try_find_program_address",
        "solana_program::syscalls::definitions::sol_try_find_program_address")]),
    (.system_instruction_create_account_with_seed, {
      package := "solana-program", version :=
      "1.15.3", source := registry, dependencies := [⟨"bincode", "1.3.3", registry⟩] },
      [("solana_program::system_instruction::create_account_with_seed",
        "solana_program::system_instruction::create_account_with_seed")]),
    (.system_instruction_create_account_with_seed, {
      package := "solana-program", version :=
      "1.18.27", source := registry, dependencies := [⟨"bincode", "1.3.3", registry⟩] },
      [("solana_program::system_instruction::create_account_with_seed",
        "solana_program::system_instruction::create_account_with_seed")]),
    (.program_invoke_signed, {
      package := "solana-program", version := "1.18.27", source :=
      registry, target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩,
      ⟨"panic", "abort"⟩], targetFeatures := some [] },
      [("solana_program::program::invoke_signed", "solana_program::program::invoke_signed")])]

theorem exact_reference_identities :
    referenceRows.length = 11 ∧ referenceRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem compatible_actual_version_identities :
    compatibleRows.length = 11 ∧ compatibleRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem build_metadata_keeps_actual_version :
    compatibleRows.all (fun row =>
      let build := { row.2.1 with version := row.2.1.version ++ "+review" }
      decide ((catalog.forBuild build).identities row.1 =
        row.2.2.map (fun names => ⟨build.package, build.version, names.1, names.2⟩))) = true := by
  decide +kernel

def rejectedVersions : List (Key × Versioning.Build × List String) :=
  [(.syscalls_definitions_sol_create_program_address, {
    package := "solana-program", version :=
    "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
    targetFeatures := some [] }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.syscalls_definitions_sol_get_clock_sysvar, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
      targetFeatures := some [] }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.syscalls_definitions_sol_get_rent_sysvar, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
      targetFeatures := some [] }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.syscalls_definitions_sol_invoke_signed_rust, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
      ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩], targetFeatures := some [] }, ["1.18.25",
        "2.0.0",
      "1.18.26-rc.1"]),
    (.syscalls_definitions_sol_memcpy_, {
      package := "solana-program", version := "1.18.26", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩], targetFeatures := some []
      }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.syscalls_definitions_sol_memset_, {
      package := "solana-program", version := "1.18.26", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩], targetFeatures := some []
      }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.syscalls_definitions_sol_sha256, {
      package := "solana-program", version := "1.18.26", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩], targetFeatures := some []
      }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.syscalls_definitions_sol_try_find_program_address, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩],
      targetFeatures := some [] }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.system_instruction_create_account_with_seed, {
      package := "solana-program", version :=
      "1.15.2", source := registry, dependencies := [⟨"bincode", "1.3.3", registry⟩] }, ["1\
        .15.1",
      "2.0.0", "1.15.2-rc.1"]),
    (.system_instruction_create_account_with_seed, {
      package := "solana-program", version :=
      "1.18.26", source := registry, dependencies := [⟨"bincode", "1.3.3", registry⟩] }, [
        "1.15.1",
      "2.0.0", "1.15.2-rc.1"]),
    (.program_invoke_signed, {
      package := "solana-program", version := "1.18.26", source :=
      registry, target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩,
      ⟨"panic", "abort"⟩], targetFeatures := some [] }, ["1.18.25", "2.0.0", "1.18.26-rc.1"])]

theorem bounds_and_prereleases_rejected :
    rejectedVersions.all (fun row => row.2.2.all (fun version =>
      ((catalog.forBuild { row.2.1 with version := version }).identities row.1).isEmpty)) = true :=
        by
  decide +kernel

theorem defining_package_and_fork_rejected :
    (referenceRows ++ compatibleRows).all (fun row =>
      ((catalog.forBuild { row.2.1 with package := "wrong-defining-package" }).identities
        row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with source :=
        ⟨"git", "https://example.invalid/source-fork", "01234567890123456789012345678901234\
          56789"⟩
        }).identities row.1).isEmpty) = true := by
  decide +kernel

/-- Literal provider intervals test selection, without claiming native coverage. -/
def dependencyVersions : List (String × String × List String) :=
  [("bincode", "1.3.4", ["1.3.2", "2.0.0", "1.3.4-rc.1"])]

theorem compatible_dependencies_keep_literal_identities :
    dependencyVersions.length = 1 ∧
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      match dependencyVersions.find? (fun item => item.1 == dep.package) with
      | none => false
      | some item =>
        let build := { row.2.1 with dependencies := row.2.1.dependencies.map (fun d =>
          if d.package = dep.package then { d with version := item.2.1 } else d) }
        decide ((catalog.forBuild build).identities row.1 =
          row.2.2.map (fun names => ⟨build.package, build.version, names.1, names.2⟩)))) = true :=
            by
  decide +kernel

theorem dependency_bounds_prereleases_and_two_compatible_candidates_rejected :
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      match dependencyVersions.find? (fun item => item.1 == dep.package) with
      | none => false
      | some item =>
        item.2.2.all (fun version =>
          ((catalog.forBuild { row.2.1 with dependencies := row.2.1.dependencies.map (fun d =>
            if d.package = dep.package then { d with version } else d) }).identities
              row.1).isEmpty) &&
        ((catalog.forBuild { row.2.1 with dependencies :=
          row.2.1.dependencies ++ [{ dep with version := item.2.1 }] }).identities row.1).isEmpty))
            = true := by
  decide +kernel

theorem required_dependency_cannot_be_omitted :
    referenceRows.any (fun row => !row.2.1.dependencies.isEmpty) = true ∧
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.filter (fun d => d.package != dep.package)) }).identities
          row.1).isEmpty)) = true := by
  decide +kernel

theorem dependency_generation_fork_and_ambiguity_rejected :
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.map (fun d => if d.package = dep.package then
          { d with version := "99.0.0" } else d)) }).identities row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.map (fun d => if d.package = dep.package then
          { d with source := ⟨"git", "https://example.invalid/provider-fork",
            "0123456789012345678901234567890123456789"⟩ } else d)) }).identities row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with dependencies := row.2.1.dependencies ++ [dep] }).identities
        row.1).isEmpty)) = true := by
  decide +kernel

theorem every_selected_target_fact_is_required :
    referenceRows.any (fun row => !row.2.1.target.isEmpty) = true ∧
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.target.all (fun fact =>
      ((catalog.forBuild { row.2.1 with target :=
        (row.2.1.target.filter (fun kept => kept.field != fact.field)) }).identities
          row.1).isEmpty)) = true := by
  decide +kernel

theorem conflicting_or_duplicate_target_facts_rejected :
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.target.all (fun fact =>
      ((catalog.forBuild { row.2.1 with target :=
        (row.2.1.target.map (fun kept => if kept.field = fact.field then
          { kept with value := "incompatible-target" } else kept)) }).identities row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with target := row.2.1.target ++ [fact] }).identities
        row.1).isEmpty)) = true := by
  decide +kernel

theorem external_syscall_dispatch_must_remain_known :
    referenceRows.any (fun row => row.2.1.targetFeatures.isSome) = true ∧
    (referenceRows ++ compatibleRows).all (fun row =>
      if row.2.1.targetFeatures.isSome then
        ((catalog.forBuild { row.2.1 with targetFeatures := none }).identities row.1).isEmpty &&
        ((catalog.forBuild { row.2.1 with targetFeatures := some ["static-syscalls"] }).identities
          row.1).isEmpty
      else true) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaProgram.LegacyCpiCompatibility

/- Per-operation compatibility selection. Synthetic versions carry no native or ABI credit. -/
namespace SolanalibTest.Specs.SolanaProgram.Cpi.LegacyCompatibility

@[expose] public section

set_option autoImplicit false

namespace RawInvoke

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "solana-program"
  version := "1.15.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "ab\
    ort"⟩]
  targetFeatures := some []

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "1.15.3" }

def identityCases (version : String) : List (Solanalib.Specs.SolanaProgram.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.syscalls_definitions_sol_invoke_signed_rust, [⟨"solana-program", version,
      "solana_program::syscalls::definitions::sol_invoke_signed_rust",
      "solana_program::syscalls::definitions::sol_invoke_signed_rust"⟩])
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

theorem required_target_facts_are_not_optional :
    compatibleBuild.target.all (fun fact =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with target := compatibleBuild.target.filter (fun kept
          => kept.field != fact.field) }).identities entry.1).isEmpty &&
        ((catalog.forBuild { compatibleBuild with target := compatibleBuild.target ++ [fact]
          }).identities entry.1).isEmpty)) = true := by decide +kernel

theorem conflicting_target_facts_rejected :
    ([⟨"os", "linux"⟩, ⟨"pointer_width", "32"⟩, ⟨"endian", "big"⟩, ⟨"panic", "unwind"⟩] : List
      Versioning.TargetFact).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with target := compatibleBuild.target.map (fun fact =>
          if fact.field = change.field then change else fact) }).identities entry.1).isEmpty)) =
            true := by decide +kernel

theorem target_features_unknown_or_wrong_rejected :
    [none, some ["static-syscalls"]].all (fun value =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with targetFeatures := value }).identities
          entry.1).isEmpty)) = true := by decide +kernel

end RawInvoke

end

end SolanalibTest.Specs.SolanaProgram.Cpi.LegacyCompatibility
