/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaSdkIds.AdditionalIds
public import Solanalib.Specs.SolanaSdkIds.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaSdkIds.AdditionalIds

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Both selected functions return their own canonical 32-byte keys. -/
theorem exact_ids :
    Solanalib.Specs.SolanaSdkIds.bpf_loader_upgradeable.id_model () () =
      (Solanalib.Runtime.Ids.bpfLoaderUpgradeable, ()) ∧
    Solanalib.Specs.SolanaSdkIds.ed25519_program.id_model () () =
      (Solanalib.Runtime.Ids.ed25519Program, ()) := ⟨rfl, rfl⟩

/-- Swapping the two selected providers violates both contracts. -/
theorem reject_cross_wiring :
    ¬ Solanalib.Specs.SolanaSdkIds.bpf_loader_upgradeable.id_contract.ensures
      () () Solanalib.Runtime.Ids.ed25519Program () ∧
    ¬ Solanalib.Specs.SolanaSdkIds.ed25519_program.id_contract.ensures
      () () Solanalib.Runtime.Ids.bpfLoaderUpgradeable () := by
  unfold Solanalib.Specs.SolanaSdkIds.bpf_loader_upgradeable.id_contract
    Solanalib.Specs.SolanaSdkIds.ed25519_program.id_contract
    SdkValue.idContract Solanalib.Contracts.Model.ensures
  decide +kernel

end SolanalibTest.Specs.SolanaSdkIds.AdditionalIds

namespace SolanalibTest.Specs.SolanaSdkIds.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SolanaSdkIds.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SolanaSdkIds.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

abbrev Row := Solanalib.Specs.SolanaSdkIds.Capabilities.Key × String × String × String

def identifies (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 =
    [⟨build.package, build.version, row.2.2.1, row.2.2.2⟩])

def rejects (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 = [])

def registry : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def dependencyVersion (build : Build) (package version : String) : Build :=
  { build with dependencies := (build.dependencies.map (fun dep =>
      if dep.package == package then { dep with version := version } else dep)) }

def build0 : Build where
  package := "solana-sdk-ids"
  version := "3.1.0"
  source := registry
  dependencies := [
    ⟨"solana-address", "2.6.0", registry⟩]

def rows0 : List Row := [
    (.ed25519_program_id, "reviewed-3-1-0",
      "solana_sdk_ids::ed25519_program::id", "solana_sdk_ids::ed25519_program::id"),
    (.bpf_loader_upgradeable_id, "reviewed-3-1-0",
      "solana_sdk_ids::bpf_loader_upgradeable::id", "solana_sdk_ids::bpf_loader_upgradeable\
        ::id")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 2 ∧
    ["3.1.0", "3.1.1"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def accepted0 : List Build := [
  dependencyVersion build0 "solana-address" "2.6.1"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_0 :
    accepted0.length = 1 ∧
    accepted0.all (fun build => rows0.all (identifies build)) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "3.0.999" },
  { build0 with version := "4.0.0" },
  { build0 with version := "3.1.1-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build0 "solana-address" "3.0.0",
  { build0 with dependencies := (build0.dependencies.filter (fun dep => dep.package !=
    "solana-address")) },
  { build0 with dependencies := (build0.dependencies ++ [⟨"solana-address", "2.6.0", registry⟩]) },
  { build0 with dependencies := (build0.dependencies.map (fun dep =>
        if dep.package == "solana-address" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 9 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaSdkIds.UpdatedProfiles

@[expose] public section

namespace SolanalibTest.Specs.SolanaSdkIds.V3AdditionalIds

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.SolanaSdkIds.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.SolanaSdkIds.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

def build0 : Versioning.Build where
  package := "solana-sdk-ids"
  version := "3.1.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["3.1.0", "3.2.0"].all (fun version =>
      decide (((selectedProfile "reviewed-3-1-0").forBuild
        { build0 with version := version }).identities .sysvar_instructions_id =
          [⟨"solana-sdk-ids", version, "solana_sdk_ids::sysvar::instructions::id",
            "solana_sdk_ids::sysvar::instructions::id"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"solana-sdk-ids", "3.1.0", "solana_sdk_ids::sysvar::instructions::id",
            "solana_sdk_ids::sysvar::instructions::id"⟩] : List Capabilities.RustIdentity).all (fun
              identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaSdkIds.Capabilities.catalog.forBuild
        build0).identities .sysvar_instructions_id)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "reviewed-3-1-0").applicability .sysvar_instructions_id).length = 1 ∧
    ["3.0.999", "4.0.0", "3.2.0-rc.1"].all (fun version =>
      (((selectedProfile "reviewed-3-1-0").forBuild { build0 with version := version }).identities
        .sysvar_instructions_id).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "solana-sdk-ids-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with dependencies := [] },
      { build0 with dependencies := [⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-address", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-address", "2.6.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "reviewed-3-1-0").forBuild build).identities
        .sysvar_instructions_id).isEmpty) = true := by
  decide +kernel

def build1 : Versioning.Build where
  package := "solana-sdk-ids"
  version := "3.1.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile1_literal_identities :
    ["3.1.0", "3.2.0"].all (fun version =>
      decide (((selectedProfile "reviewed-3-1-0").forBuild
        { build1 with version := version }).identities .vote_id =
          [⟨"solana-sdk-ids", version, "solana_sdk_ids::vote::id",
            "solana_sdk_ids::vote::id"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile1_present_in_full_catalog :
    ([⟨"solana-sdk-ids", "3.1.0", "solana_sdk_ids::vote::id",
            "solana_sdk_ids::vote::id"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaSdkIds.Capabilities.catalog.forBuild
        build1).identities .vote_id)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile1_range_rejections :
    ((selectedProfile "reviewed-3-1-0").applicability .vote_id).length = 1 ∧
    ["3.0.999", "4.0.0", "3.2.0-rc.1"].all (fun version =>
      (((selectedProfile "reviewed-3-1-0").forBuild { build1 with version := version }).identities
        .vote_id).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile1_build_rejections :
    ([{ build1 with package := "solana-sdk-ids-other" },
      { build1 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build1 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build1 with dependencies := [] },
      { build1 with dependencies := [⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-address", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-address", "2.6.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "reviewed-3-1-0").forBuild build).identities
        .vote_id).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaSdkIds.V3AdditionalIds
