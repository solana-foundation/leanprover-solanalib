/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaPubkey
public import SolanalibTest.Specs.Core.AddressOperations
public import Solanalib.Specs.SolanaPubkey.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaPubkey.Address

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Contracts.Model.Versioning
open Solanalib.Specs.SolanaPubkey.Capabilities

def cratesIo : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- All source facts required by the selected Pubkey operations, including
the actual Borsh dependency edge. This is a matcher fixture, not a build receipt. -/
def reviewedBuild : Build where
  package := "solana-pubkey"
  version := "2.4.0"
  source := cratesIo
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩]
  features := some ["borsh"]
  dependencies := [⟨"borsh", "0.10.4", cratesIo⟩]

theorem reviewed_build_admits_all (key : Key) :
    (catalog.forBuild reviewedBuild).identities key =
      ((catalog.identities key).map fun identity =>
        { identity with crateVersion := "2.4.0" }).eraseDups := by
  cases key <;> decide +kernel

def members : List (Key × String × String) :=
  [(.Pubkey_as_ref, "core::convert::AsRef::as_ref",
      "<solana_pubkey::Pubkey as core::convert::AsRef<[u8]>>::as_ref"),
    (.Pubkey_clone, "core::clone::Clone::clone",
      "<solana_pubkey::Pubkey as core::clone::Clone>::clone"),
    (.Pubkey_create_program_address_solana, "solana_pubkey::Pubkey::create_program_address",
      "solana_pubkey::Pubkey::create_program_address"),
    (.Pubkey_create_with_seed, "solana_pubkey::Pubkey::create_with_seed",
      "solana_pubkey::Pubkey::create_with_seed"),
    (.Pubkey_default, "core::default::Default::default",
      "<solana_pubkey::Pubkey as core::default::Default>::default"),
    (.Pubkey_deserialize_reader, "borsh::de::BorshDeserialize::deserialize_reader",
      "<solana_pubkey::Pubkey as borsh::de::BorshDeserialize>::deserialize_reader"),
    (.Pubkey_eq, "core::cmp::PartialEq::eq",
      "<solana_pubkey::Pubkey as core::cmp::PartialEq>::eq"),
    (.Pubkey_find_program_address_solana, "solana_pubkey::Pubkey::find_program_address",
      "solana_pubkey::Pubkey::find_program_address"),
    (.Pubkey_serialize, "borsh::ser::BorshSerialize::serialize",
      "<solana_pubkey::Pubkey as borsh::ser::BorshSerialize>::serialize"),
    (.Pubkey_to_bytes, "solana_pubkey::Pubkey::to_bytes", "solana_pubkey::Pubkey::to_bytes")]

/-- Synthetic compatible versions select the actual queried identity, without
turning those fixtures into claims of native execution. -/
theorem compatible_pubkey_identities :
    ["2.4.0", "2.4.1", "2.9.0"].all (fun version => members.all (fun (key, item, implementation) =>
      decide ((catalog.forBuild { reviewedBuild with version := version }).identities key =
        [⟨"solana-pubkey", version, item, implementation⟩]))) = true := by
  decide +kernel

/-- The new `to_bytes` range admits 2.3.0; its exact identity is checked
below. All other inherited gap, upper-bound and prerelease rejections remain. -/
theorem outside_pubkey_ranges_rejected :
    ["2.3.0", "3.0.0", "2.4.1-rc.1"].all (fun version =>
      (members.filter (fun (key, _, _) => decide (key ≠ .Pubkey_to_bytes ∨ version ≠ "2.3.0"))).all
        (fun (key, _, _) =>
          decide ((catalog.forBuild { reviewedBuild with version := version }).identities key =
            []))) =
      true := by decide +kernel

theorem compatible_borsh_dependency_admitted :
    ([.Pubkey_serialize, .Pubkey_deserialize_reader] : List Key).all (fun key => decide
      ((catalog.forBuild { reviewedBuild with
        version := "2.4.1"
        dependencies := [⟨"borsh", "0.10.5", cratesIo⟩] }).identities key ≠ [])) = true := by
  decide +kernel

theorem incompatible_borsh_dependencies_rejected :
    ["0.10.3", "0.11.0", "1.6.0", "0.10.5-rc.1"].all (fun version =>
      ([.Pubkey_serialize, .Pubkey_deserialize_reader] : List Key).all (fun key => decide
        ((catalog.forBuild { reviewedBuild with
          version := "2.4.1"
          dependencies := [⟨"borsh", version, cratesIo⟩] }).identities key = []))) = true := by
  decide +kernel

theorem forked_borsh_dependency_rejected :
    (catalog.forBuild { reviewedBuild with
      version := "2.4.1"
      dependencies := [⟨"borsh", "0.10.5", ⟨"git", "https://example.invalid/borsh", "fork"⟩⟩] }).identities
        .Pubkey_serialize = [] := by decide +kernel

theorem value_operations_do_not_require_runtime_target :
    ([.Pubkey_default, .Pubkey_clone, .Pubkey_eq, .Pubkey_to_bytes, .Pubkey_as_ref] : List Key).all
      (fun key =>
      decide ((catalog.forBuild { reviewedBuild with version := "2.4.1", target := [] }).identities
        key ≠ [])) =
      true := by decide +kernel

theorem unreviewed_release_is_rejected (key : Key) :
    (catalog.forBuild { reviewedBuild with version := "2.2.0" }).identities key = [] := by
  cases key <;> decide +kernel

/-- The newly reviewed release admits precisely its per-operation subset. -/
theorem reviewed_221_retains_operation_scope (key : Key) :
    (catalog.forBuild { reviewedBuild with version := "2.2.1" }).identities key =
      match key with
      | .Pubkey_clone => []
      | _ => ((catalog.identities key).map fun identity =>
          { identity with crateVersion := "2.2.1" }).eraseDups := by
  cases key <;> decide +kernel

/-- The exact 2.2.1 additions do not extend this inherited member. -/
theorem unextended_members_stay_outside_the_added_reference :
    ([Key.Pubkey_clone]).all (fun key =>
      ((catalog.forBuild { reviewedBuild with version := "2.2.1" }).identities key).isEmpty) = true
        := by
  decide +kernel

theorem same_version_from_another_source_is_rejected (key : Key) :
    (catalog.forBuild { reviewedBuild with version := "2.4.1", source :=
      ⟨"git", "https://example.invalid/pubkey", "0123456789012345678901234567890123456789"⟩
    }).identities key = [] := by
  cases key <;> decide +kernel

theorem runtime_requires_recorded_target :
    (catalog.forBuild { reviewedBuild with version := "2.4.1", target := [] }).identities
      .Pubkey_create_program_address_solana = [] ∧
    (catalog.forBuild { reviewedBuild with
      version := "2.4.1"
      target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩] }).identities
      .Pubkey_find_program_address_solana = [] ∧
    (catalog.forBuild { reviewedBuild with
      version := "2.4.1"
      target := [⟨"os", "solana"⟩, ⟨"pointer_width", "32"⟩] }).identities
      .Pubkey_create_with_seed = [] := by
  decide +kernel

theorem borsh_feature_is_required :
    (catalog.forBuild { reviewedBuild with version := "2.4.1", features := some [] }).identities
      .Pubkey_serialize = [] ∧
    (catalog.forBuild { reviewedBuild with version := "2.4.1", features := none }).identities
      .Pubkey_deserialize_reader = [] := by
  decide +kernel

theorem borsh_generation_is_required :
    (catalog.forBuild { reviewedBuild with version := "2.4.1", dependencies := [] }).identities
      .Pubkey_serialize = [] ∧
    (catalog.forBuild { reviewedBuild with dependencies := [⟨"borsh", "1.6.0", cratesIo⟩]
      }).identities
      .Pubkey_deserialize_reader = [] := by
  decide +kernel

/-- Per-call Borsh mappings must not make this ambiguous whole build eligible. -/
theorem multiple_borsh_generations_reject_whole_build :
    let ambiguous := { reviewedBuild with version := "2.4.1", dependencies :=
      [⟨"borsh", "0.10.4", cratesIo⟩, ⟨"borsh", "1.6.0", cratesIo⟩] }
    (catalog.forBuild ambiguous).identities .Pubkey_serialize = [] ∧
    (catalog.forBuild ambiguous).identities .Pubkey_deserialize_reader = [] ∧
    (catalog.forBuild { ambiguous with version := "2.2.1" }).identities .Pubkey_serialize = [] ∧
    (catalog.forBuild { ambiguous with version := "2.2.1" }).identities .Pubkey_deserialize_reader
      = [] := by
  decide +kernel

end SolanalibTest.Specs.SolanaPubkey.Address

namespace SolanalibTest.Specs.SolanaPubkey.Address.ComparisonProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.SolanaPubkey.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.Pubkey_cmp,
      {
        package := "solana-pubkey",
        version := "2.2.1",
        source := registry },
      [("core::cmp::Ord::cmp", "<solana_pubkey::Pubkey as core::cmp::Ord>::cmp")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"solana-pubkey", build.version, item, implementation⟩))

def members : List Key := [.Pubkey_cmp]

theorem every_member_has_a_literal_case :
    members.length = 1 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["2.2.1", "2.3.0", "2.4.0"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["2.2.2", "2.9.99+fixture"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["2.2.0", "3.0.0", "2.2.2-rc.1"].all (fun version => fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- An interval must not conceal a missing reference or a changed item range. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      !(Solanalib.Specs.SolanaPubkey.Capabilities.catalog.applicability key).isEmpty &&
      (Solanalib.Specs.SolanaPubkey.Capabilities.catalog.applicability key).all (fun profile =>
        decide (profile.releases = ["2.2.1", "2.3.0", "2.4.0"] ∧
          profile.compatibleRanges = [⟨"2.2.1", "3.0.0"⟩]))) = true := by
  decide +kernel

theorem a_version_cannot_replace_the_defining_source :
    fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with package := "wrong-defining-package" } [] &&
      identitiesMatch key { build with source :=
        ⟨"git", "https://example.invalid/library", "012345678901234567890123456789012345678\
          9"⟩ } [] &&
      identitiesMatch key { build with source :=
        ⟨"registry", "https://example.invalid/registry", ""⟩ } []) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaPubkey.Address.ComparisonProfiles

namespace SolanalibTest.Specs.SolanaPubkey.Address.AddedReferences

open Solanalib.Contracts.Model Solanalib.Specs.Core

def members : List (Solanalib.Specs.SolanaPubkey.Capabilities.Key × String × String) :=
  [(.Pubkey_default, "core::default::Default::default",
    "<solana_pubkey::Pubkey as core::default::Default>::default"),
    (.Pubkey_serialize, "borsh::ser::BorshSerialize::serialize",
      "<solana_pubkey::Pubkey as borsh::ser::BorshSerialize>::serialize"),
    (.Pubkey_as_ref, "core::convert::AsRef::as_ref",
      "<solana_pubkey::Pubkey as core::convert::AsRef<[u8]>>::as_ref"),
    (.Pubkey_create_with_seed, "solana_pubkey::Pubkey::create_with_seed",
      "solana_pubkey::Pubkey::create_with_seed"),
    (.Pubkey_create_program_address_solana, "solana_pubkey::Pubkey::create_program_address",
      "solana_pubkey::Pubkey::create_program_address"),
    (.Pubkey_deserialize_reader, "borsh::de::BorshDeserialize::deserialize_reader",
      "<solana_pubkey::Pubkey as borsh::de::BorshDeserialize>::deserialize_reader"),
    (.Pubkey_eq, "core::cmp::PartialEq::eq", "<solana_pubkey::Pubkey as \
      core::cmp::PartialEq>::eq"),
    (.Pubkey_find_program_address_solana, "solana_pubkey::Pubkey::find_program_address",
      "solana_pubkey::Pubkey::find_program_address")]

/-- Add the exact 2.2.1 reference without replacing the inherited 2.4 interval.
Every expected identity is a literal callable/implementation pair. -/
theorem added_reference_and_existing_compatible_identity :
    ["2.2.1", "2.4.0", "2.4.1", "2.9.99+fixture"].all (fun version =>
      members.all (fun (key, item, implementation) => decide
        ((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
          { reviewedBuild with version := version }).identities key =
          [⟨"solana-pubkey", version, item, implementation⟩]))) = true := by
  decide +kernel

theorem exact_addition_does_not_fill_the_gap :
    ["2.2.0", "2.2.2", "2.3.0", "3.0.0", "2.2.1-rc.1"].all (fun version =>
      members.all (fun (key, _, _) =>
        ((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
          { reviewedBuild with version := version }).identities key).isEmpty)) = true := by
  decide +kernel

/-- The new Ord member has its own inspected 2.3.0 reference. It must not make
the other eight members or their Borsh mappings eligible in that gap. -/
theorem comparison_keeps_its_own_release_scope :
    (Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
      { reviewedBuild with version := "2.3.0" }).identities .Pubkey_cmp =
      [⟨"solana-pubkey", "2.3.0", "core::cmp::Ord::cmp",
        "<solana_pubkey::Pubkey as core::cmp::Ord>::cmp"⟩] := by
  decide +kernel

/-- Adding the old Pubkey reference retains the already accepted dependency
range, the error contract of the old reader and full-closure ambiguity rejection. -/
theorem added_reference_preserves_borsh_generation_and_resolution :
    let selected := { reviewedBuild with version := "2.2.1" }
    ["0.10.4", "0.10.5"].all (fun version =>
      ([Solanalib.Specs.SolanaPubkey.Capabilities.Key.Pubkey_serialize,
        .Pubkey_deserialize_reader]).all
        (fun key => !((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
          { selected with dependencies := [⟨"borsh", version, cratesIo⟩] }).identities
            key).isEmpty)) = true ∧
    ["0.10.3", "0.11.0", "1.5.7", "1.6.0", "0.10.5-rc.1"].all (fun version =>
      ([Solanalib.Specs.SolanaPubkey.Capabilities.Key.Pubkey_serialize,
        .Pubkey_deserialize_reader]).all
        (fun key => ((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
          { selected with dependencies := [⟨"borsh", version, cratesIo⟩] }).identities
            key).isEmpty)) = true ∧
    ([Solanalib.Specs.SolanaPubkey.Capabilities.Key.Pubkey_serialize,
      .Pubkey_deserialize_reader]).all
      (fun key => ((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
        { selected with dependencies := [⟨"borsh", "0.10.4", cratesIo⟩,
          ⟨"borsh", "1.6.0", cratesIo⟩] }).identities key).isEmpty &&
        ((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
          { selected with dependencies := [] }).identities key).isEmpty &&
        ((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
          { selected with features := none }).identities key).isEmpty &&
        ((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
          { selected with features := some [] }).identities key).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaPubkey.Address.AddedReferences

namespace SolanalibTest.Specs.SolanaPubkey.Address.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def Pubkey_fromBuild : Versioning.Build where
  package := "solana-pubkey"
  version := "2.2.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def Pubkey_fromCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-2.2.1; eligible
  (Pubkey_fromBuild, true),
  -- inspected-reference-2.3.0; eligible
  ({ Pubkey_fromBuild with version := "2.3.0" }, true),
  -- inspected-reference-2.4.0; eligible
  ({ Pubkey_fromBuild with version := "2.4.0" }, true),
  -- lower; eligible
  (Pubkey_fromBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ Pubkey_fromBuild with version := "2.2.98" }, true),
  -- exclusive-upper; unsupported
  ({ Pubkey_fromBuild with version := "3.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ Pubkey_fromBuild with version := "2.2.1-rc.1" }, false),
  -- wrong-package; unsupported
  ({ Pubkey_fromBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ Pubkey_fromBuild with source := ⟨"git", "https://example.invalid/review-fork", "bbbbbb\
    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-2.2.0; unsupported
  ({ Pubkey_fromBuild with version := "2.2.0" }, false)
]

set_option maxRecDepth 8192 in
theorem Pubkey_from_profile_controls :
    Pubkey_fromCases.all (fun test =>
      (((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.applicability .Pubkey_from).any
        (fun profile => ["solana-pubkey-2.2.1-2.4.0-from"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem Pubkey_from_callable_identities :
    ["2.2.1", "2.3.0", "2.4.0", "2.2.98"].all (fun version =>
      (((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
        { Pubkey_fromBuild with version := version }).identities .Pubkey_from).eraseDups ==
        [⟨"solana-pubkey", version, "core::convert::From::from",
          "<solana_pubkey::Pubkey as core::convert::From<[u8; 32]>>::from"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def Pubkey_new_from_arrayBuild : Versioning.Build where
  package := "solana-pubkey"
  version := "2.2.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def Pubkey_new_from_arrayCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-2.2.1; eligible
  (Pubkey_new_from_arrayBuild, true),
  -- inspected-reference-2.3.0; eligible
  ({ Pubkey_new_from_arrayBuild with version := "2.3.0" }, true),
  -- inspected-reference-2.4.0; eligible
  ({ Pubkey_new_from_arrayBuild with version := "2.4.0" }, true),
  -- lower; eligible
  (Pubkey_new_from_arrayBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ Pubkey_new_from_arrayBuild with version := "2.2.98" }, true),
  -- exclusive-upper; unsupported
  ({ Pubkey_new_from_arrayBuild with version := "3.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ Pubkey_new_from_arrayBuild with version := "2.2.1-rc.1" }, false),
  -- wrong-package; unsupported
  ({ Pubkey_new_from_arrayBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ Pubkey_new_from_arrayBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-2.2.0; unsupported
  ({ Pubkey_new_from_arrayBuild with version := "2.2.0" }, false)
]

set_option maxRecDepth 8192 in
theorem Pubkey_new_from_array_profile_controls :
    Pubkey_new_from_arrayCases.all (fun test =>
      (((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.applicability .Pubkey_new_from_array).any
        (fun profile => ["solana-pubkey-2.2.1-2.4.0-new_from_array"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem Pubkey_new_from_array_callable_identities :
    ["2.2.1", "2.3.0", "2.4.0", "2.2.98"].all (fun version =>
      (((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
        { Pubkey_new_from_arrayBuild with version := version }).identities
          .Pubkey_new_from_array).eraseDups ==
        [⟨"solana-pubkey", version, "solana_pubkey::Pubkey::new_from_array",
          "solana_pubkey::Pubkey::new_from_array"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def Pubkey_to_bytesBuild : Versioning.Build where
  package := "solana-pubkey"
  version := "2.2.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def Pubkey_to_bytesCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-2.2.1; eligible
  (Pubkey_to_bytesBuild, true),
  -- inspected-reference-2.3.0; eligible
  ({ Pubkey_to_bytesBuild with version := "2.3.0" }, true),
  -- inspected-reference-2.4.0; eligible
  ({ Pubkey_to_bytesBuild with version := "2.4.0" }, true),
  -- lower; eligible
  (Pubkey_to_bytesBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ Pubkey_to_bytesBuild with version := "2.2.98" }, true),
  -- exclusive-upper; unsupported
  ({ Pubkey_to_bytesBuild with version := "3.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ Pubkey_to_bytesBuild with version := "2.2.1-rc.1" }, false),
  -- wrong-package; unsupported
  ({ Pubkey_to_bytesBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ Pubkey_to_bytesBuild with source := ⟨"git", "https://example.invalid/review-fork", "bb\
    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-2.2.0; unsupported
  ({ Pubkey_to_bytesBuild with version := "2.2.0" }, false)
]

set_option maxRecDepth 8192 in
theorem Pubkey_to_bytes_profile_controls :
    Pubkey_to_bytesCases.all (fun test =>
      (((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.applicability .Pubkey_to_bytes).any
        (fun profile => ["solana-pubkey-2.4.0-to_bytes"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem Pubkey_to_bytes_callable_identities :
    ["2.2.1", "2.3.0", "2.4.0", "2.2.98"].all (fun version =>
      (((Solanalib.Specs.SolanaPubkey.Capabilities.catalog.forBuild
        { Pubkey_to_bytesBuild with version := version }).identities .Pubkey_to_bytes).eraseDups ==
        [⟨"solana-pubkey", version, "solana_pubkey::Pubkey::to_bytes",
          "solana_pubkey::Pubkey::to_bytes"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaPubkey.Address.Pr575Compatibility
