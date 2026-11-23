/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.AnchorSpl.Token
public import SolanalibTest.Specs.AnchorSpl.OwnedTransfer
public import SolanalibTest.Specs.AnchorSpl.OwnedContextTransfer
public import SolanalibTest.Specs.AnchorSpl.OwnedAmount

public import SolanalibTest.Specs.Core.AnchorSplSupport

public import Solanalib.Specs.AnchorSpl
public import SolanalibTest.Specs.Core.AnchorSplTokenOperations
public import Solanalib.Specs.AnchorSpl.token_2022
public import SolanalibTest.Specs.Core.AnchorSplTokenAdmission
public import Solanalib.Specs.AnchorSpl.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorSpl.Support

open Solanalib.Contracts.Model.Versioning
open Solanalib.Specs.AnchorSpl.Capabilities (catalog)

/-- Only the token-interface module feature and its decoded-state provider
are constrained by this field projection. -/
def tokenAccountBuild : Build where
  package := "anchor-spl"
  version := "0.32.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  features := some ["token_2022"]
  dependencies :=
    [⟨"spl-token-2022", "8.0.1",
      ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]

/-- These fixtures include the three inspected wrappers and a synthetic patch,
paired with the reference provider and a synthetic compatible provider. -/
theorem token_account_actual_identities :
    ["0.32.1", "0.32.2", "0.32.3", "0.32.4"].all (fun version =>
      ["8.0.1", "8.1.0"].all (fun provider => decide
        ((catalog.forBuild { tokenAccountBuild with version := version, dependencies :=
          (tokenAccountBuild.dependencies.map
            (fun dependency => { dependency with version := provider })) }).identities
            .token_interface_TokenAccount_deref =
          [⟨"anchor-spl", version, "core::ops::deref::Deref::deref",
            "<anchor_spl::token_interface::TokenAccount as core::ops::deref::Deref>::deref"⟩]))) =
      true := by
  decide +kernel

theorem token_account_boundaries_and_prerelease_rejected :
    ["0.32.0", "0.33.0", "0.32.4-rc.1"].all (fun version =>
      ((catalog.forBuild { tokenAccountBuild with version := version }).identities
        .token_interface_TokenAccount_deref).isEmpty) = true := by
  decide +kernel

/-- Neither an absent/unknown feature list nor the distinct legacy-token feature
compiles the token-interface module, including at a compatible patch. -/
theorem token_account_feature_required :
    ["0.32.1", "0.32.4"].all (fun version =>
      [none, some [], some ["token"]].all (fun features =>
        ((catalog.forBuild { tokenAccountBuild with version := version, features := features
          }).identities
          .token_interface_TokenAccount_deref).isEmpty)) = true := by
  decide +kernel

theorem token_account_provider_boundaries_rejected :
    ["0.32.1", "0.32.4"].all (fun version =>
      ["8.0.0", "9.0.0", "8.1.0-rc.1"].all (fun provider =>
        ((catalog.forBuild { tokenAccountBuild with version := version, dependencies :=
          (tokenAccountBuild.dependencies.map
            (fun dependency => { dependency with version := provider })) }).identities
          .token_interface_TokenAccount_deref).isEmpty)) = true := by
  decide +kernel

/-- A lockfile list with two matching candidates does not identify the used state provider. -/
theorem token_account_provider_required_and_unique :
    ["0.32.1", "0.32.4"].all (fun version =>
      [[], tokenAccountBuild.dependencies ++ tokenAccountBuild.dependencies].all
        (fun dependencies =>
          ((catalog.forBuild { tokenAccountBuild with version := version, dependencies :=
            dependencies }).identities .token_interface_TokenAccount_deref).isEmpty)) =
      true := by
  decide +kernel

theorem token_account_wrapper_and_provider_forks_rejected :
    ["0.32.1", "0.32.4"].all (fun version =>
      let fork : Source := ⟨"git", "https://example.org/token-account-fork",
        "0123456789012345678901234567890123456789"⟩
      [ { tokenAccountBuild with version := version, source := fork },
        { tokenAccountBuild with version := version, dependencies :=
          (tokenAccountBuild.dependencies.map
            (fun dependency => { dependency with source := fork })) } ].all (fun build =>
        ((catalog.forBuild build).identities .token_interface_TokenAccount_deref).isEmpty)) =
      true := by
  decide +kernel

end SolanalibTest.Specs.AnchorSpl.Support

namespace SolanalibTest.Specs.AnchorSpl.CheckedTransfer

open Solanalib.Contracts.Model.Versioning
open Solanalib.Specs.AnchorSpl.Capabilities (catalog)

def registrySource : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def forkSource : Source :=
  ⟨"git", "https://example.org/anchor-fork", "0123456789012345678901234567890123456789"⟩

def reviewedBuild : Build where
  package := "anchor-spl"
  version := "0.32.1"
  source := registrySource
  features := some ["token_2022"]
  dependencies := [⟨"anchor-lang", "0.32.1", registrySource⟩,
    ⟨"spl-token-2022", "8.0.1", registrySource⟩,
    ⟨"solana-account-info", "2.3.0", registrySource⟩,
    ⟨"solana-program-error", "2.2.2", registrySource⟩]

def identitiesMatch (build : Build) : Bool := decide
  ((catalog.forBuild build).identities .token_2022_transfer_checked =
    [⟨"anchor-spl", build.version, "anchor_spl::token_2022::transfer_checked",
      "anchor_spl::token_2022::transfer_checked"⟩])

/-- Keep negative checks on this owned-program, boxed-legacy-error profile. -/
def admitted (build : Build) : Bool :=
  (catalog.applicability .token_2022_transfer_checked).any fun profile =>
    profile.id == "anchor-spl-token-0-32-1-token2022TransferChecked0321" && profile.matches build

def withDependencyVersion (build : Build) (package version : String) : Build :=
  { build with dependencies := build.dependencies.map fun dependency =>
      if dependency.package == package then { dependency with version } else dependency }

theorem named_profile_is_present_and_admitted :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "0.32.4"].all (fun version =>
      admitted { reviewedBuild with version }) = true := by
  decide +kernel

/-- Four inspected wrappers and one compatible patch fixture retain literal
function identities with the actual selected package version. -/
theorem inspected_and_compatible_identities :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "0.32.4"].all (fun version =>
      identitiesMatch { reviewedBuild with version }) = true := by
  decide +kernel

theorem outside_minor_range_and_prerelease_rejected :
    ["0.31.999", "0.33.0", "1.0.0", "0.32.4-rc.1"].all (fun version =>
      !admitted { reviewedBuild with version }) = true := by
  decide +kernel

/-- The last provider in each row is a compatibility fixture; the other
entries are the inspected references. No provider changes the wrapper identity. -/
theorem inspected_and_compatible_providers :
    ([ ("anchor-lang", ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "0.32.4"]),
       ("spl-token-2022", ["8.0.0", "8.0.1", "8.0.2"]),
       ("solana-account-info", ["2.3.0", "2.3.1"]),
       ("solana-program-error", ["2.2.0", "2.2.1", "2.2.2", "2.2.3"]) ] :
        List (String × List String)).all (fun (package, versions) => versions.all fun version =>
          identitiesMatch (withDependencyVersion reviewedBuild package version)) = true := by
  decide +kernel

theorem provider_bounds_and_prereleases_rejected :
    ["0.32.1", "0.32.4"].all (fun version =>
      ([ ("anchor-lang", ["0.31.999", "0.33.0", "0.32.4-rc.1"]),
         ("spl-token-2022", ["7.999.0", "9.0.0", "8.0.2-rc.1"]),
         ("solana-account-info", ["2.2.999", "3.0.0", "2.3.1-rc.1"]),
         ("solana-program-error", ["2.1.999", "3.0.0", "2.2.3-rc.1"]) ] :
          List (String × List String)).all (fun (package, versions) => versions.all fun provider =>
            !admitted (withDependencyVersion { reviewedBuild with version } package provider))) =
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
              else dependency } ].all (fun candidate => !admitted candidate)) = true := by
  decide +kernel

theorem wrapper_package_and_source_rejected :
    ["0.32.1", "0.32.4"].all (fun version =>
      [ { reviewedBuild with version, package := "anchor-lang" },
        { reviewedBuild with version, source := forkSource },
        { reviewedBuild with version, source := ⟨"registry", "https://example.org/index", ""⟩ } ].all
          (fun build => !admitted build)) = true := by
  decide +kernel

theorem token_2022_feature_is_required :
    ["0.32.1", "0.32.4"].all (fun version =>
      [none, some [], some ["token"]].all (fun features =>
        !admitted { reviewedBuild with version, features })) = true := by
  decide +kernel

/-- Extra token features and known host/Solana facts introduce no new gate. -/
theorem target_and_extra_features_preserve_identities :
    [ { reviewedBuild with
        target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩],
        targetFeatures := some [] },
      { reviewedBuild with
        version := "0.32.4",
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩],
        features := some ["token_2022", "token"],
        targetFeatures := some ["static-syscalls"] } ].all identitiesMatch = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorSpl.CheckedTransfer

namespace SolanalibTest.Specs.AnchorSpl.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def memo_build_memoBuild : Versioning.Build where
  package := "anchor-spl"
  version := "0.32.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩]
  features := some ["memo"]
  targetFeatures := some []
  dependencies := [⟨"anchor-lang", "0.32.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"spl-memo", "6.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def memo_build_memoCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.32.0; eligible
  (memo_build_memoBuild, true),
  -- inspected-reference-0.32.1; eligible
  ({ memo_build_memoBuild with version := "0.32.1" }, true),
  -- inspected-reference-0.32.2; eligible
  ({ memo_build_memoBuild with version := "0.32.2" }, true),
  -- inspected-reference-0.32.3; eligible
  ({ memo_build_memoBuild with version := "0.32.3" }, true),
  -- lower; eligible
  (memo_build_memoBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ memo_build_memoBuild with version := "0.32.97" }, true),
  -- exclusive-upper; unsupported
  ({ memo_build_memoBuild with version := "0.33.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ memo_build_memoBuild with version := "0.32.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ memo_build_memoBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ memo_build_memoBuild with source := ⟨"git", "https://example.invalid/review-fork", "bb\
    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ memo_build_memoBuild with target := [] }, false),
  -- wrong-target-os; unsupported
  ({ memo_build_memoBuild with target := [⟨"os", "linux"⟩] }, false),
  -- missing-features; unresolved
  ({ memo_build_memoBuild with features := none }, false),
  -- wrong-features; unsupported
  ({ memo_build_memoBuild with features := some [] }, false),
  -- dependency-reference-anchor-lang-0.32.0; eligible
  (memo_build_memoBuild, true),
  -- dependency-reference-anchor-lang-0.32.1; eligible
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package == "anchor-lang" then { dependency with version :=
      "0.32.1"
    } else dependency)) }, true),
  -- dependency-reference-anchor-lang-0.32.2; eligible
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package == "anchor-lang" then { dependency with version :=
      "0.32.2"
    } else dependency)) }, true),
  -- dependency-reference-anchor-lang-0.32.3; eligible
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package == "anchor-lang" then { dependency with version :=
      "0.32.3"
    } else dependency)) }, true),
  -- dependency-anchor-lang-lower; eligible
  (memo_build_memoBuild, true),
  -- dependency-anchor-lang-hypothetical-declaration-probe; eligible
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package == "anchor-lang" then { dependency with version :=
    "0.32.97" } else dependency)) }, true),
  -- dependency-anchor-lang-exclusive-upper; unsupported
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package == "anchor-lang" then { dependency with version :=
      "0.33.0"
    } else dependency)) }, false),
  -- dependency-anchor-lang-unlisted-prerelease; unsupported
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package == "anchor-lang" then { dependency with version :=
    "0.32.0-rc.1" } else dependency)) }, false),
  -- missing-dependency-anchor-lang; unresolved
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.filter (fun
    dependency => dependency.package != "anchor-lang")) }, false),
  -- wrong-dependency-origin-anchor-lang; unsupported
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package ==
    "anchor-lang" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-anchor-lang; ValueError containing Ambiguous dependency
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies ++ [⟨"anc\
    hor-lang", "0.32.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- dependency-reference-spl-memo-6.0.0; eligible
  (memo_build_memoBuild, true),
  -- dependency-spl-memo-lower; eligible
  (memo_build_memoBuild, true),
  -- dependency-spl-memo-hypothetical-declaration-probe; eligible
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package == "spl-memo" then { dependency with version := "6.\
      0.97" }
    else dependency)) }, true),
  -- dependency-spl-memo-exclusive-upper; unsupported
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package == "spl-memo" then { dependency with version := "7.\
      0.0" }
    else dependency)) }, false),
  -- dependency-spl-memo-unlisted-prerelease; unsupported
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package == "spl-memo" then { dependency with version :=
    "6.0.0-rc.1" } else dependency)) }, false),
  -- missing-dependency-spl-memo; unresolved
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.filter (fun
    dependency => dependency.package != "spl-memo")) }, false),
  -- wrong-dependency-origin-spl-memo; unsupported
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package ==
    "spl-memo" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-spl-memo; ValueError containing Ambiguous dependency
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies ++ [⟨"spl\
    -memo", "6.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-0.31.999; unsupported
  ({ memo_build_memoBuild with version := "0.31.999" }, false),
  -- dependency-anchor-lang-below-lower-bound-fixture-0.31.999; unsupported
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package == "anchor-lang" then { dependency with version :=
    "0.31.999" } else dependency)) }, false),
  -- dependency-spl-memo-below-lower-bound-fixture-5.999.999; unsupported
  ({ memo_build_memoBuild with dependencies := (memo_build_memoBuild.dependencies.map (fun
    dependency => if dependency.package == "spl-memo" then { dependency with version := "5.\
      999.999"
    } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem memo_build_memo_profile_controls :
    memo_build_memoCases.all (fun test =>
      (((Solanalib.Specs.AnchorSpl.Capabilities.catalog.applicability .memo_build_memo).any
        (fun profile => ["anchor-spl-support-0.32.1-memo-build_memo"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem memo_build_memo_callable_identities :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "0.32.97"].all (fun version =>
      (((Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild
        { memo_build_memoBuild with version := version }).identities .memo_build_memo).eraseDups ==
        [⟨"anchor-spl", version, "anchor_spl::memo::build_memo", "anchor_spl::memo::build_m\
          emo"⟩]))
          = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorSpl.Pr575Compatibility

/- Per-operation compatibility selection. Synthetic versions carry no native or ABI credit. -/
namespace SolanalibTest.Specs.AnchorSpl.LegacyCompatibility

@[expose] public section

set_option autoImplicit false

namespace StakeView

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorSpl.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-spl"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  dependencies := [⟨"solana-program", "1.15.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]
  features := some ["stake"]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (Solanalib.Specs.AnchorSpl.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.stake_StakeAccount_deref, [⟨"anchor-spl", version, "core::ops::deref::Deref::deref",
      "<anchor_spl::stake::StakeAccount as core::ops::deref::Deref>::deref"⟩])
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
    ([("solana-program", "1.16.0"), ("solana-program", "1.15.3-rc.1")] : List (String ×
      String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1).isEmpty)) = true := by decide +kernel

theorem features_unknown_or_wrong_rejected :
    [none, some []].all (fun value =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with features := value }).identities
          entry.1).isEmpty)) = true := by decide +kernel

end StakeView

namespace StakeCpi

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorSpl.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-spl"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  dependencies := [⟨"anchor-lang", "0.27.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program", "1.15.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]
  target := [⟨"os", "solana"⟩]
  features := some ["stake"]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (Solanalib.Specs.AnchorSpl.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.stake_deactivate_stake, [⟨"anchor-spl", version, "anchor_spl::stake::deactivate_stake",
      "anchor_spl::stake::deactivate_stake"⟩]),
    (.stake_withdraw, [⟨"anchor-spl", version, "anchor_spl::stake::withdraw",
      "anchor_spl::stake::withdraw"⟩])
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
    ([("anchor-lang", "0.27.1"), ("solana-program", "1.15.3")] : List (String × String)).all (fun
      change =>
      (identityCases compatibleBuild.version).all (fun entry => decide
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1 = entry.2))) = true := by decide +kernel

theorem exact_codecs_and_dependency_boundaries_retained :
    ([("anchor-lang", "0.28.0"), ("anchor-lang", "0.27.1-rc.1"), ("solana-program", "1.16.0"),
      ("solana-program", "1.15.3-rc.1")] : List (String × String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1).isEmpty)) = true := by decide +kernel

theorem required_target_facts_are_not_optional :
    compatibleBuild.target.all (fun fact =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with target := compatibleBuild.target.filter (fun kept
          => kept.field != fact.field) }).identities entry.1).isEmpty &&
        ((catalog.forBuild { compatibleBuild with target := compatibleBuild.target ++ [fact]
          }).identities entry.1).isEmpty)) = true := by decide +kernel

theorem conflicting_target_facts_rejected :
    ([⟨"os", "linux"⟩] : List Versioning.TargetFact).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with target := compatibleBuild.target.map (fun fact =>
          if fact.field = change.field then change else fact) }).identities entry.1).isEmpty)) =
            true := by decide +kernel

theorem features_unknown_or_wrong_rejected :
    [none, some []].all (fun value =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with features := value }).identities
          entry.1).isEmpty)) = true := by decide +kernel

end StakeCpi

namespace TokenCpi

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorSpl.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-spl"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  dependencies := [⟨"anchor-lang", "0.27.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"spl-token", "3.5.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program", "1.15.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]
  features := some ["token"]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (Solanalib.Specs.AnchorSpl.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.token_burn, [⟨"anchor-spl", version, "anchor_spl::token::burn", "anchor_spl::token::b\
      urn"⟩]),
    (.token_mint_to, [⟨"anchor-spl", version, "anchor_spl::token::mint_to",
      "anchor_spl::token::mint_to"⟩]),
    (.token_transfer_inline_error, [⟨"anchor-spl", version, "anchor_spl::token::transfer",
      "anchor_spl::token::transfer"⟩])
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
    ([("anchor-lang", "0.27.1"), ("solana-program", "1.15.3")] : List (String × String)).all (fun
      change =>
      (identityCases compatibleBuild.version).all (fun entry => decide
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1 = entry.2))) = true := by decide +kernel

theorem exact_codecs_and_dependency_boundaries_retained :
    ([("anchor-lang", "0.28.0"), ("anchor-lang", "0.27.1-rc.1"), ("spl-token", "3.5.1"),
      ("solana-program", "1.16.0"), ("solana-program", "1.15.3-rc.1")] : List (String ×
      String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1).isEmpty)) = true := by decide +kernel

theorem features_unknown_or_wrong_rejected :
    [none, some []].all (fun value =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with features := value }).identities
          entry.1).isEmpty)) = true := by decide +kernel

end TokenCpi

namespace TokenView

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorSpl.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-spl"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  dependencies := [⟨"spl-token", "3.5.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]
  features := some ["token"]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (Solanalib.Specs.AnchorSpl.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.token_TokenAccount_deref, [⟨"anchor-spl", version, "core::ops::deref::Deref::deref",
      "<anchor_spl::token::TokenAccount as core::ops::deref::Deref>::deref"⟩])
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

theorem exact_codecs_and_dependency_boundaries_retained :
    ([("spl-token", "3.5.1")] : List (String × String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1).isEmpty)) = true := by decide +kernel

theorem features_unknown_or_wrong_rejected :
    [none, some []].all (fun value =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with features := value }).identities
          entry.1).isEmpty)) = true := by decide +kernel

end TokenView

end

end SolanalibTest.Specs.AnchorSpl.LegacyCompatibility
