/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaProgram
public import SolanalibTest.Specs.Core.AddressOperations
public import Solanalib.Specs.SolanaProgram.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaProgram.PubkeyCompatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (Key catalog)

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal Rust identities are independent of generated profile selection. -/
def referenceRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.pubkey_Pubkey_as_ref, {
    package := "solana-program", version := "1.15.2", source := registry },
      [("core::convert::AsRef::as_ref",
        "<solana_program::pubkey::Pubkey as core::convert::AsRef<[u8]>>::as_ref")]),
    (.pubkey_Pubkey_as_ref, {
      package := "solana-program", version := "1.18.26", source := registry
      },
      [("core::convert::AsRef::as_ref",
        "<solana_program::pubkey::Pubkey as core::convert::AsRef<[u8]>>::as_ref")]),
    (.pubkey_Pubkey_clone, {
      package := "solana-program", version := "1.15.2", source := registry },
      [("core::clone::Clone::clone",
        "<solana_program::pubkey::Pubkey as core::clone::Clone>::clone")]),
    (.pubkey_Pubkey_clone, {
      package := "solana-program", version := "1.18.26", source := registry
      },
      [("core::clone::Clone::clone",
        "<solana_program::pubkey::Pubkey as core::clone::Clone>::clone")]),
    (.pubkey_Pubkey_create_program_address_solana, {
      package := "solana-program", version :=
      "1.15.2", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::create_program_address",
        "solana_program::pubkey::Pubkey::create_program_address")]),
    (.pubkey_Pubkey_create_program_address_solana, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::create_program_address",
        "solana_program::pubkey::Pubkey::create_program_address")]),
    (.pubkey_Pubkey_create_with_seed, {
      package := "solana-program", version := "1.15.2", source :=
      registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::create_with_seed",
        "solana_program::pubkey::Pubkey::create_with_seed")]),
    (.pubkey_Pubkey_create_with_seed, {
      package := "solana-program", version := "1.18.26", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::create_with_seed",
        "solana_program::pubkey::Pubkey::create_with_seed")]),
    (.pubkey_Pubkey_default, {
      package := "solana-program", version := "1.15.2", source := registry
      },
      [("core::default::Default::default",
        "<solana_program::pubkey::Pubkey as core::default::Default>::default")]),
    (.pubkey_Pubkey_default, {
      package := "solana-program", version := "1.18.26", source :=
      registry },
      [("core::default::Default::default",
        "<solana_program::pubkey::Pubkey as core::default::Default>::default")]),
    (.pubkey_Pubkey_deserialize_reader, {
      package := "solana-program", version := "1.18.26", source
      := registry, dependencies := [⟨"borsh", "0.10.4", registry⟩] },
      [("borsh::de::BorshDeserialize::deserialize_reader",
        "<solana_program::pubkey::Pubkey as \
          borsh::de::BorshDeserialize>::deserialize_reader")]),
    (.pubkey_Pubkey_eq, {
      package := "solana-program", version := "1.15.2", source := registry },
      [("core::cmp::PartialEq::eq",
        "<solana_program::pubkey::Pubkey as core::cmp::PartialEq>::eq")]),
    (.pubkey_Pubkey_eq, {
      package := "solana-program", version := "1.18.26", source := registry },
      [("core::cmp::PartialEq::eq",
        "<solana_program::pubkey::Pubkey as core::cmp::PartialEq>::eq")]),
    (.pubkey_Pubkey_find_program_address_solana, {
      package := "solana-program", version :=
      "1.15.2", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::find_program_address",
        "solana_program::pubkey::Pubkey::find_program_address")]),
    (.pubkey_Pubkey_find_program_address_solana, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::find_program_address",
        "solana_program::pubkey::Pubkey::find_program_address")]),
    (.pubkey_Pubkey_serialize, {
      package := "solana-program", version := "1.18.26", source :=
      registry, dependencies := [⟨"borsh", "0.10.4", registry⟩] },
      [("borsh::ser::BorshSerialize::serialize",
        "<solana_program::pubkey::Pubkey as borsh::ser::BorshSerialize>::serialize")]),
    (.pubkey_Pubkey_to_bytes, {
      package := "solana-program", version := "1.15.2", source :=
      registry },
      [("solana_program::pubkey::Pubkey::to_bytes", "solana_program::pubkey::Pubkey::to_byt\
        es")]),
    (.pubkey_Pubkey_to_bytes, {
      package := "solana-program", version := "1.18.26", source :=
      registry },
      [("solana_program::pubkey::Pubkey::to_bytes", "solana_program::pubkey::Pubkey::to_byt\
        es")])]

/-- These uninspected patch versions exercise compatibility assumptions only. -/
def compatibleRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.pubkey_Pubkey_as_ref, {
    package := "solana-program", version := "1.15.3", source := registry },
      [("core::convert::AsRef::as_ref",
        "<solana_program::pubkey::Pubkey as core::convert::AsRef<[u8]>>::as_ref")]),
    (.pubkey_Pubkey_as_ref, {
      package := "solana-program", version := "1.18.27", source := registry
      },
      [("core::convert::AsRef::as_ref",
        "<solana_program::pubkey::Pubkey as core::convert::AsRef<[u8]>>::as_ref")]),
    (.pubkey_Pubkey_clone, {
      package := "solana-program", version := "1.15.3", source := registry },
      [("core::clone::Clone::clone",
        "<solana_program::pubkey::Pubkey as core::clone::Clone>::clone")]),
    (.pubkey_Pubkey_clone, {
      package := "solana-program", version := "1.18.27", source := registry
      },
      [("core::clone::Clone::clone",
        "<solana_program::pubkey::Pubkey as core::clone::Clone>::clone")]),
    (.pubkey_Pubkey_create_program_address_solana, {
      package := "solana-program", version :=
      "1.15.3", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::create_program_address",
        "solana_program::pubkey::Pubkey::create_program_address")]),
    (.pubkey_Pubkey_create_program_address_solana, {
      package := "solana-program", version :=
      "1.18.27", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::create_program_address",
        "solana_program::pubkey::Pubkey::create_program_address")]),
    (.pubkey_Pubkey_create_with_seed, {
      package := "solana-program", version := "1.15.3", source :=
      registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::create_with_seed",
        "solana_program::pubkey::Pubkey::create_with_seed")]),
    (.pubkey_Pubkey_create_with_seed, {
      package := "solana-program", version := "1.18.27", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::create_with_seed",
        "solana_program::pubkey::Pubkey::create_with_seed")]),
    (.pubkey_Pubkey_default, {
      package := "solana-program", version := "1.15.3", source := registry
      },
      [("core::default::Default::default",
        "<solana_program::pubkey::Pubkey as core::default::Default>::default")]),
    (.pubkey_Pubkey_default, {
      package := "solana-program", version := "1.18.27", source :=
      registry },
      [("core::default::Default::default",
        "<solana_program::pubkey::Pubkey as core::default::Default>::default")]),
    (.pubkey_Pubkey_deserialize_reader, {
      package := "solana-program", version := "1.18.27", source
      := registry, dependencies := [⟨"borsh", "0.10.4", registry⟩] },
      [("borsh::de::BorshDeserialize::deserialize_reader",
        "<solana_program::pubkey::Pubkey as \
          borsh::de::BorshDeserialize>::deserialize_reader")]),
    (.pubkey_Pubkey_eq, {
      package := "solana-program", version := "1.15.3", source := registry },
      [("core::cmp::PartialEq::eq",
        "<solana_program::pubkey::Pubkey as core::cmp::PartialEq>::eq")]),
    (.pubkey_Pubkey_eq, {
      package := "solana-program", version := "1.18.27", source := registry },
      [("core::cmp::PartialEq::eq",
        "<solana_program::pubkey::Pubkey as core::cmp::PartialEq>::eq")]),
    (.pubkey_Pubkey_find_program_address_solana, {
      package := "solana-program", version :=
      "1.15.3", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::find_program_address",
        "solana_program::pubkey::Pubkey::find_program_address")]),
    (.pubkey_Pubkey_find_program_address_solana, {
      package := "solana-program", version :=
      "1.18.27", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      [("solana_program::pubkey::Pubkey::find_program_address",
        "solana_program::pubkey::Pubkey::find_program_address")]),
    (.pubkey_Pubkey_serialize, {
      package := "solana-program", version := "1.18.27", source :=
      registry, dependencies := [⟨"borsh", "0.10.4", registry⟩] },
      [("borsh::ser::BorshSerialize::serialize",
        "<solana_program::pubkey::Pubkey as borsh::ser::BorshSerialize>::serialize")]),
    (.pubkey_Pubkey_to_bytes, {
      package := "solana-program", version := "1.15.3", source :=
      registry },
      [("solana_program::pubkey::Pubkey::to_bytes", "solana_program::pubkey::Pubkey::to_byt\
        es")]),
    (.pubkey_Pubkey_to_bytes, {
      package := "solana-program", version := "1.18.27", source :=
      registry },
      [("solana_program::pubkey::Pubkey::to_bytes", "solana_program::pubkey::Pubkey::to_byt\
        es")])]

theorem exact_reference_identities :
    referenceRows.length = 18 ∧ referenceRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem compatible_actual_version_identities :
    compatibleRows.length = 18 ∧ compatibleRows.all (fun row => decide
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
  [(.pubkey_Pubkey_as_ref, {
    package := "solana-program", version := "1.15.2", source := registry
    }, ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_as_ref, {
      package := "solana-program", version := "1.18.26", source := registry
      }, ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_clone, {
      package := "solana-program", version := "1.15.2", source := registry
      }, ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_clone, {
      package := "solana-program", version := "1.18.26", source := registry
      }, ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_create_program_address_solana, {
      package := "solana-program", version :=
      "1.15.2", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_create_program_address_solana, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_create_with_seed, {
      package := "solana-program", version := "1.15.2", source :=
      registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] }, ["1.15.1", "2.0.0",
      "1.15.2-rc.1"]),
    (.pubkey_Pubkey_create_with_seed, {
      package := "solana-program", version := "1.18.26", source
      := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] }, ["1.15.1", "2.0\
        .0",
      "1.15.2-rc.1"]),
    (.pubkey_Pubkey_default, {
      package := "solana-program", version := "1.15.2", source := registry
      }, ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_default, {
      package := "solana-program", version := "1.18.26", source :=
      registry }, ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_deserialize_reader, {
      package := "solana-program", version := "1.18.26", source
      := registry, dependencies := [⟨"borsh", "0.10.4", registry⟩] }, ["1.18.25", "2.0.0",
      "1.18.26-rc.1"]),
    (.pubkey_Pubkey_eq, {
      package := "solana-program", version := "1.15.2", source := registry },
      ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_eq, {
      package := "solana-program", version := "1.18.26", source := registry },
      ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_find_program_address_solana, {
      package := "solana-program", version :=
      "1.15.2", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_find_program_address_solana, {
      package := "solana-program", version :=
      "1.18.26", source := registry, target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩] },
      ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_serialize, {
      package := "solana-program", version := "1.18.26", source :=
      registry, dependencies := [⟨"borsh", "0.10.4", registry⟩] }, ["1.18.25", "2.0.0",
      "1.18.26-rc.1"]),
    (.pubkey_Pubkey_to_bytes, {
      package := "solana-program", version := "1.15.2", source :=
      registry }, ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.pubkey_Pubkey_to_bytes, {
      package := "solana-program", version := "1.18.26", source :=
      registry }, ["1.15.1", "2.0.0", "1.15.2-rc.1"])]

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
  [("borsh", "0.10.5", ["0.10.3", "0.11.0", "0.10.5-rc.1"])]

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

end SolanalibTest.Specs.SolanaProgram.PubkeyCompatibility

/- Per-operation compatibility selection. Synthetic versions carry no native or ABI credit. -/
namespace SolanalibTest.Specs.SolanaProgram.Address.LegacyCompatibility

@[expose] public section

set_option autoImplicit false

namespace BorshCodec

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "solana-program"
  version := "1.15.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  dependencies := [⟨"borsh", "0.9.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"borsh-derive", "0.9.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "1.15.3" }

def identityCases (version : String) : List (Solanalib.Specs.SolanaProgram.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.pubkey_Pubkey_deserialize, [⟨"solana-program", version,
      "borsh::de::BorshDeserialize::deserialize",
      "<solana_program::pubkey::Pubkey as borsh::de::BorshDeserialize>::deserialize"⟩]),
    (.pubkey_Pubkey_serialize, [⟨"solana-program", version,
      "borsh::ser::BorshSerialize::serialize",
      "<solana_program::pubkey::Pubkey as borsh::ser::BorshSerialize>::serialize"⟩])
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
    ([("borsh", "0.10.4"), ("borsh-derive", "0.10.4")] : List (String × String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1).isEmpty)) = true := by decide +kernel

theorem simultaneous_borsh_generations_rejected :
    let build : Versioning.Build := { compatibleBuild with dependencies :=
      compatibleBuild.dependencies ++
      [⟨"borsh", "0.10.4", referenceBuild.source⟩, ⟨"borsh", "1.6.0", referenceBuild.source⟩] }
    (identityCases build.version).all (fun entry =>
      ((catalog.forBuild build).identities entry.1).isEmpty) = true := by decide +kernel

end BorshCodec

end

end SolanalibTest.Specs.SolanaProgram.Address.LegacyCompatibility
