/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.system_program
public import Solanalib.Specs.AnchorLang.Capabilities
public import SolanalibTest.Specs.Core.AnchorSystem

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.SystemProgram

open Solanalib.Contracts.Model.Versioning
open Solanalib.Specs.AnchorLang.Capabilities (catalog)

def registrySource : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def forkSource : Source :=
  ⟨"git", "https://example.org/anchor-fork", "0123456789012345678901234567890123456789"⟩

def reviewedBuild : Build where
  package := "anchor-lang"
  version := "0.32.1"
  source := registrySource
  dependencies := [⟨"solana-system-interface", "1.0.0", registrySource⟩,
    ⟨"solana-account-info", "2.3.0", registrySource⟩,
    ⟨"solana-program-error", "2.2.2", registrySource⟩,
    ⟨"solana-pubkey", "2.2.1", registrySource⟩, ⟨"bincode", "1.3.3", registrySource⟩]

def expectedItems : List (Solanalib.Specs.AnchorLang.Capabilities.Key × String) :=
  [(.system_program_allocate, "anchor_lang::system_program::allocate"),
    (.system_program_assign, "anchor_lang::system_program::assign"),
    (.system_program_create_account, "anchor_lang::system_program::create_account"),
    (.system_program_transfer, "anchor_lang::system_program::transfer")]

/-- Expected identities come from the literal source paths, not the catalog. -/
def identitiesMatch (build : Build) : Bool :=
  expectedItems.all fun (key, item) => decide
    ((catalog.forBuild build).identities key = [⟨"anchor-lang", build.version, item, item⟩])

/-- Rejections concern this profile even when a later release gains another one. -/
def admitted (key : Solanalib.Specs.AnchorLang.Capabilities.Key) (build : Build) : Bool :=
  (catalog.applicability key).any fun profile =>
    profile.id == "anchor-system-0-32-1" && profile.matches build

def rejected (build : Build) : Bool :=
  expectedItems.all fun (key, _) => !admitted key build

def withDependencyVersion (build : Build) (package version : String) : Build :=
  { build with dependencies := build.dependencies.map fun dependency =>
      if dependency.package == package then { dependency with version } else dependency }

theorem named_profiles_are_present_and_admitted :
    expectedItems.length = 4 ∧
      ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "0.32.4"].all (fun version =>
        expectedItems.all (fun (key, _) => admitted key { reviewedBuild with version })) =
      true := by
  decide +kernel

/-- Four inspected releases and one compatible patch fixture use their actual
version in the full catalog. The fixture adds no source-review claim. -/
theorem inspected_and_compatible_identities :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "0.32.4"].all (fun version =>
      identitiesMatch { reviewedBuild with version }) = true := by
  decide +kernel

theorem outside_minor_range_and_prerelease_rejected :
    ["0.31.999", "0.33.0", "1.0.0", "0.32.4-rc.1"].all (fun version =>
      rejected { reviewedBuild with version }) = true := by
  decide +kernel

/-- Each provider is varied separately; the last version in each row is a
compatibility fixture, while preceding versions were inspected. -/
theorem inspected_and_compatible_providers :
    ([ ("solana-system-interface", ["1.0.0", "1.0.1"]),
       ("solana-account-info", ["2.3.0", "2.3.1"]),
       ("solana-program-error", ["2.2.0", "2.2.1", "2.2.2", "2.2.3"]),
       ("solana-pubkey", ["2.2.1", "2.4.0", "2.4.1"]),
       ("bincode", ["1.3.3", "1.3.4"]) ] : List (String × List String)).all
      (fun (package, versions) => versions.all fun version =>
        identitiesMatch (withDependencyVersion reviewedBuild package version)) = true := by
  decide +kernel

theorem provider_bounds_and_prereleases_rejected :
    ["0.32.1", "0.32.4"].all (fun version =>
      ([ ("solana-system-interface", ["0.999.0", "2.0.0", "1.0.1-rc.1"]),
         ("solana-account-info", ["2.2.999", "3.0.0", "2.3.1-rc.1"]),
         ("solana-program-error", ["2.1.999", "3.0.0", "2.2.3-rc.1"]),
         ("solana-pubkey", ["2.2.0", "3.0.0", "2.4.1-rc.1"]),
         ("bincode", ["1.3.2", "2.0.0", "1.3.4-rc.1"]) ] : List (String × List String)).all
        (fun (package, versions) => versions.all fun provider =>
          rejected (withDependencyVersion { reviewedBuild with version } package provider))) =
      true := by
  decide +kernel

theorem each_provider_is_required_unique_and_registry_bound :
    ["0.32.1", "0.32.4"].all (fun version =>
      reviewedBuild.dependencies.all fun selected =>
        let build := { reviewedBuild with version }
        [ { build with dependencies := (build.dependencies.filter
              (fun dependency => dependency.package != selected.package)) },
          { build with dependencies := selected :: build.dependencies },
          { build with dependencies := { selected with version := "99.0.0" } :: build.dependencies
            },
          { build with dependencies := build.dependencies.map fun dependency =>
              if dependency.package == selected.package then { dependency with source := forkSource
                }
              else dependency } ].all rejected) = true := by
  decide +kernel

theorem wrapper_package_and_source_rejected :
    ["0.32.1", "0.32.4"].all (fun version =>
      [ { reviewedBuild with version, package := "anchor-spl" },
        { reviewedBuild with version, source := forkSource },
        { reviewedBuild with version, source := ⟨"registry", "https://example.org/index", ""⟩ } ].all
          rejected) = true := by
  decide +kernel

/-- These profiles add no target or feature gate; invocation stays opaque. -/
theorem target_and_features_do_not_narrow_identities :
    [ { reviewedBuild with
        target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩],
        features := some [], targetFeatures := some [] },
      { reviewedBuild with
        version := "0.32.4",
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩],
        features := some ["cpi"], targetFeatures := some ["static-syscalls"] } ].all
          identitiesMatch = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.SystemProgram

namespace SolanalibTest.Specs.AnchorLang.system_program.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def system_program_System_idBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.32.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def system_program_System_idCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.32.0; eligible
  (system_program_System_idBuild, true),
  -- inspected-reference-0.32.1; eligible
  ({ system_program_System_idBuild with version := "0.32.1" }, true),
  -- inspected-reference-0.32.2; eligible
  ({ system_program_System_idBuild with version := "0.32.2" }, true),
  -- inspected-reference-0.32.3; eligible
  ({ system_program_System_idBuild with version := "0.32.3" }, true),
  -- lower; eligible
  (system_program_System_idBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ system_program_System_idBuild with version := "0.32.97" }, true),
  -- exclusive-upper; unsupported
  ({ system_program_System_idBuild with version := "0.33.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ system_program_System_idBuild with version := "0.32.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ system_program_System_idBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ system_program_System_idBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.31.999; unsupported
  ({ system_program_System_idBuild with version := "0.31.999" }, false)
]

set_option maxRecDepth 8192 in
theorem system_program_System_id_profile_controls :
    system_program_System_idCases.all (fun test =>
      (((Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability
        .system_program_System_id).any
        (fun profile => ["anchor-system-id-0-32-1"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem system_program_System_id_callable_identities :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "0.32.97"].all (fun version =>
      (((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        { system_program_System_idBuild with version := version }).identities
          .system_program_System_id).eraseDups ==
        [⟨"anchor-lang", version, "anchor_lang::Id::id",
          "<anchor_lang::system_program::System as anchor_lang::Id>::id"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.system_program.Pr575Compatibility

@[expose] public section

namespace SolanalibTest.Specs.AnchorLang.V1_0_2system_program

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.AnchorLang.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

def build0 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-system-1-0-2").forBuild
        { build0 with version := version }).identities .system_program_allocate_unit_borsh =
          [⟨"anchor-lang", version, "anchor_lang::system_program::allocate",
            "anchor_lang::system_program::allocate"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::system_program::allocate",
            "anchor_lang::system_program::allocate"⟩] : List Capabilities.RustIdentity).all (fun
              identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build0).identities .system_program_allocate_unit_borsh)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "anchor-system-1-0-2").applicability
      .system_program_allocate_unit_borsh).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-system-1-0-2").forBuild { build0 with version := version
        }).identities
        .system_program_allocate_unit_borsh).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "anchor-lang-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://example.invalid/registry", ""⟩⟩, ⟨
        "bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://example.invalid/registry", ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "anchor-system-1-0-2").forBuild build).identities
        .system_program_allocate_unit_borsh).isEmpty) = true := by
  decide +kernel

def build1 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile1_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-system-1-0-2").forBuild
        { build1 with version := version }).identities .system_program_assign_unit_borsh =
          [⟨"anchor-lang", version, "anchor_lang::system_program::assign",
            "anchor_lang::system_program::assign"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile1_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::system_program::assign",
            "anchor_lang::system_program::assign"⟩] : List Capabilities.RustIdentity).all (fun
              identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build1).identities .system_program_assign_unit_borsh)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile1_range_rejections :
    ((selectedProfile "anchor-system-1-0-2").applicability
      .system_program_assign_unit_borsh).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-system-1-0-2").forBuild { build1 with version := version
        }).identities
        .system_program_assign_unit_borsh).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile1_build_rejections :
    ([{ build1 with package := "anchor-lang-other" },
      { build1 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build1 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://example.invalid/registry", ""⟩⟩, ⟨
        "bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://example.invalid/registry", ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "anchor-system-1-0-2").forBuild build).identities
        .system_program_assign_unit_borsh).isEmpty) = true := by
  decide +kernel

def build2 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile2_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-system-1-0-2").forBuild
        { build2 with version := version }).identities .system_program_create_account_unit_borsh =
          [⟨"anchor-lang", version, "anchor_lang::system_program::create_account",
            "anchor_lang::system_program::create_account"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile2_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::system_program::create_account",
            "anchor_lang::system_program::create_account"⟩] : List Capabilities.RustIdentity).all
              (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build2).identities .system_program_create_account_unit_borsh)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile2_range_rejections :
    ((selectedProfile "anchor-system-1-0-2").applicability
      .system_program_create_account_unit_borsh).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-system-1-0-2").forBuild { build2 with version := version
        }).identities
        .system_program_create_account_unit_borsh).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile2_build_rejections :
    ([{ build2 with package := "anchor-lang-other" },
      { build2 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build2 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build2 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://example.invalid/registry", ""⟩⟩, ⟨
        "bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://example.invalid/registry", ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "anchor-system-1-0-2").forBuild build).identities
        .system_program_create_account_unit_borsh).isEmpty) = true := by
  decide +kernel

def build3 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile3_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-system-1-0-2").forBuild
        { build3 with version := version }).identities .system_program_transfer_unit_borsh =
          [⟨"anchor-lang", version, "anchor_lang::system_program::transfer",
            "anchor_lang::system_program::transfer"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile3_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::system_program::transfer",
            "anchor_lang::system_program::transfer"⟩] : List Capabilities.RustIdentity).all (fun
              identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build3).identities .system_program_transfer_unit_borsh)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile3_range_rejections :
    ((selectedProfile "anchor-system-1-0-2").applicability
      .system_program_transfer_unit_borsh).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-system-1-0-2").forBuild { build3 with version := version
        }).identities
        .system_program_transfer_unit_borsh).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile3_build_rejections :
    ([{ build3 with package := "anchor-lang-other" },
      { build3 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build3 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build3 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://example.invalid/registry", ""⟩⟩, ⟨
        "bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"solana-system-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://example.invalid/registry", ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "anchor-system-1-0-2").forBuild build).identities
        .system_program_transfer_unit_borsh).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.V1_0_2system_program

namespace SolanalibTest.Specs.AnchorLang.LegacySystemCompatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorLang.Capabilities (Key catalog)

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal Rust identities are independent of generated profile selection. -/
def referenceRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.system_program_allocate, {
    package := "anchor-lang", version := "0.29.0", source := registry,
    dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.3", registry⟩] },
      [("anchor_lang::system_program::allocate", "anchor_lang::system_program::allocate")]),
    (.system_program_assign, {
      package := "anchor-lang", version := "0.29.0", source := registry,
      dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.3", registry⟩] },
      [("anchor_lang::system_program::assign", "anchor_lang::system_program::assign")]),
    (.system_program_create_account, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.\
        3",
      registry⟩] },
      [("anchor_lang::system_program::create_account",
        "anchor_lang::system_program::create_account")]),
    (.system_program_transfer, {
      package := "anchor-lang", version := "0.29.0", source := registry,
      dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.3", registry⟩] },
      [("anchor_lang::system_program::transfer", "anchor_lang::system_program::transfer")])]

/-- These uninspected patch versions exercise compatibility assumptions only. -/
def compatibleRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.system_program_allocate, {
    package := "anchor-lang", version := "0.29.1", source := registry,
    dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.3", registry⟩] },
      [("anchor_lang::system_program::allocate", "anchor_lang::system_program::allocate")]),
    (.system_program_assign, {
      package := "anchor-lang", version := "0.29.1", source := registry,
      dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.3", registry⟩] },
      [("anchor_lang::system_program::assign", "anchor_lang::system_program::assign")]),
    (.system_program_create_account, {
      package := "anchor-lang", version := "0.29.1", source :=
      registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.\
        3",
      registry⟩] },
      [("anchor_lang::system_program::create_account",
        "anchor_lang::system_program::create_account")]),
    (.system_program_transfer, {
      package := "anchor-lang", version := "0.29.1", source := registry,
      dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.3", registry⟩] },
      [("anchor_lang::system_program::transfer", "anchor_lang::system_program::transfer")])]

theorem exact_reference_identities :
    referenceRows.length = 4 ∧ referenceRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem compatible_actual_version_identities :
    compatibleRows.length = 4 ∧ compatibleRows.all (fun row => decide
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
  [(.system_program_allocate, {
    package := "anchor-lang", version := "0.29.0", source := registry,
    dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.3", registry⟩] },
    ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.system_program_assign, {
      package := "anchor-lang", version := "0.29.0", source := registry,
      dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.3", registry⟩] },
      ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.system_program_create_account, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.\
        3",
      registry⟩] }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.system_program_transfer, {
      package := "anchor-lang", version := "0.29.0", source := registry,
      dependencies := [⟨"solana-program", "1.18.26", registry⟩, ⟨"bincode", "1.3.3", registry⟩] },
      ["0.28.999", "0.30.0", "0.29.0-rc.1"])]

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
  [("bincode", "1.3.4", ["1.3.2", "2.0.0", "1.3.4-rc.1"]),
    ("solana-program", "1.18.27", ["1.18.25", "2.0.0", "1.18.27-rc.1"])]

theorem compatible_dependencies_keep_literal_identities :
    dependencyVersions.length = 2 ∧
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

end SolanalibTest.Specs.AnchorLang.LegacySystemCompatibility

/- Per-operation compatibility selection. Synthetic versions carry no native or ABI credit. -/
namespace SolanalibTest.Specs.AnchorLang.system_program.LegacyCompatibility

@[expose] public section

set_option autoImplicit false

namespace SystemCpi

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorLang.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  dependencies := [⟨"solana-program", "1.15.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (Solanalib.Specs.AnchorLang.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.system_program_allocate_inline_borsh, [⟨"anchor-lang", version,
      "anchor_lang::system_program::allocate", "anchor_lang::system_program::allocate"⟩]),
    (.system_program_assign_inline_borsh, [⟨"anchor-lang", version,
      "anchor_lang::system_program::assign", "anchor_lang::system_program::assign"⟩]),
    (.system_program_create_account_inline_borsh, [⟨"anchor-lang", version,
      "anchor_lang::system_program::create_account",
      "anchor_lang::system_program::create_account"⟩]),
    (.system_program_transfer_inline_borsh, [⟨"anchor-lang", version,
      "anchor_lang::system_program::transfer", "anchor_lang::system_program::transfer"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["0.26.9", "0.28.0", "0.27.1-rc.1"].all (fun version =>
      (identityCases version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with version := version }).identities
          entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_origin_rejected :
    (identityCases compatibleBuild.version).all (fun entry =>
      ((catalog.forBuild { compatibleBuild with source :=
        ⟨"git", "https://example.org/source-fork", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
          a"⟩ }).identities entry.1).isEmpty) = true := by decide +kernel

theorem every_dependency_is_required_and_unambiguous :
    [referenceBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        (identityCases build.version).all (fun entry =>
          ((catalog.forBuild { build with dependencies := build.dependencies.filter (fun kept =>
            kept.package != dep.package) }).identities entry.1).isEmpty &&
          ((catalog.forBuild { build with dependencies := build.dependencies ++ [dep] }).identities
            entry.1).isEmpty))) = true := by decide +kernel

theorem every_dependency_rejects_wrong_release_or_origin :
    compatibleBuild.dependencies.all (fun dep =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun kept =>
              if kept.package = dep.package then { kept with version := "99.0.0" } else kept)
            }).identities entry.1).isEmpty &&
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun kept =>
              if kept.package = dep.package then { kept with source := ⟨"git", "https://example.org/provider-fork",
                "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else kept) }).identities
                  entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_dependency_actual_identities :
    ([("solana-program", "1.15.3")] : List (String × String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry => decide
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1 = entry.2))) = true := by decide +kernel

theorem exact_codecs_and_dependency_boundaries_retained :
    ([("solana-program", "1.16.0"), ("solana-program", "1.15.3-rc.1"), ("bincode", "1.3.4")] : List
      (String × String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1).isEmpty)) = true := by decide +kernel

end SystemCpi

end

end SolanalibTest.Specs.AnchorLang.system_program.LegacyCompatibility
