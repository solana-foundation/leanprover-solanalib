/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplTokenMetadataInterface
public import Solanalib.Specs.SplTokenMetadataInterface.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SplTokenMetadataInterface.Models

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open Solanalib.Specs.SplTokenMetadataInterface.state.TokenMetadata

/-- Every implementation admitted by the interface supplies the complete
empty value, including both zero keys and the ordered additional-entry list. -/
theorem client_empty_metadata (operation : Unit → Unit → Metadata × Unit)
    (correct : default_contract.RealizedBy operation) :
    (operation () ()).1 = ⟨.zero, .zero, "", "", "", []⟩ :=
  correct () () trivial

/-- The closed reference really supplies that result. -/
theorem reference_empty_metadata :
    (defaultReference () ()).1 = ⟨.zero, .zero, "", "", "", []⟩ :=
  client_empty_metadata defaultReference default_reference

end SolanalibTest.Specs.SplTokenMetadataInterface.Models

namespace SolanalibTest.Specs.SplTokenMetadataInterface.Models.Profiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.SplTokenMetadataInterface.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.instruction_initialize,
      {
        package := "spl-token-metadata-interface",
        version := "0.7.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩],
        dependencies := [⟨"solana-pubkey", "2.2.1", registry⟩, ⟨"solana-instruction", "2.2.\
          1",
          registry⟩, ⟨"solana-program-error", "2.2.0", registry⟩, ⟨"borsh", "1.5.7", registry⟩] },
      [("spl_token_metadata_interface::instruction::initialize",
        "spl_token_metadata_interface::instruction::initialize")]),
    (.instruction_initialize,
      {
        package := "spl-token-metadata-interface",
        version := "0.7.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩],
        dependencies := [⟨"solana-pubkey", "2.4.0", registry⟩, ⟨"solana-instruction", "2.3.\
          3",
          registry⟩, ⟨"solana-program-error", "2.2.0", registry⟩, ⟨"borsh", "1.6.0", registry⟩] },
      [("spl_token_metadata_interface::instruction::initialize",
        "spl_token_metadata_interface::instruction::initialize")]),
    (.state_TokenMetadata_default,
      {
        package := "spl-token-metadata-interface",
        version := "0.7.0",
        source := registry,
        dependencies := [⟨"spl-pod", "0.5.1", registry⟩, ⟨"solana-pubkey", "2.2.1", registry⟩] },
      [("core::default::Default::default",
        "<spl_token_metadata_interface::state::TokenMetadata as \
          core::default::Default>::default")]),
    (.state_TokenMetadata_default,
      {
        package := "spl-token-metadata-interface",
        version := "0.7.0",
        source := registry,
        dependencies := [⟨"spl-pod", "0.5.1", registry⟩, ⟨"solana-pubkey", "2.4.0", registry⟩] },
      [("core::default::Default::default",
        "<spl_token_metadata_interface::state::TokenMetadata as \
          core::default::Default>::default")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.SplTokenMetadataInterface.Capabilities.catalog.forBuild
    build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"spl-token-metadata-interface", build.version, item, implementation⟩))

def members : List Key := [.instruction_initialize, .state_TokenMetadata_default]

theorem every_member_has_a_literal_case :
    members.length = 2 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["0.7.0"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["0.7.1", "0.7.99+fixture"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["0.6.0", "0.8.0", "1.0.0", "0.7.1-rc.1"].all (fun version => fixtures.all (fun (key, build, _)
      =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- An interval must not conceal a missing reference or a changed item range. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      !(Solanalib.Specs.SplTokenMetadataInterface.Capabilities.catalog.applicability key).isEmpty &&
      (Solanalib.Specs.SplTokenMetadataInterface.Capabilities.catalog.applicability key).all (fun
        profile =>
        decide (profile.releases = ["0.7.0"] ∧
          profile.compatibleRanges = [⟨"0.7.0", "0.8.0"⟩]))) = true := by
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

/-- Each required edge is checked independently. Duplicate compatible
candidates remain ambiguous actual dependency facts. -/
theorem dependency_facts_cannot_be_missing_wrong_or_ambiguous :
    fixtures.all (fun (key, build, _) => build.dependencies.all (fun required =>
      identitiesMatch key { build with dependencies := (build.dependencies.filter
        (fun dependency => dependency.package != required.package)) } [] &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with version := "99.0.0" } else dependency)) } [] &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with source :=
            ⟨"git", "https://example.invalid/dependency", "01234567890123456789012345678901\
              23456789"⟩ }
          else dependency)) } [] &&
      identitiesMatch key { build with dependencies := build.dependencies ++ [required] } [])) =
        true := by
  decide +kernel

/-- Provider references and compatible fixtures preserve the actual
identity of the caller; the provider version is not substituted for the defining crate. -/
theorem dependency_references_and_compatible_versions :
    ([("solana-program-error", ["2.2.0", "2.2.1", "2.2.2", "2.9.99", "2.9.99+fixture"])] : List
      (String × List String)).all (fun (package, versions) =>
      fixtures.all (fun (key, build, expected) => versions.all (fun version =>
        identitiesMatch key { build with dependencies := (build.dependencies.map
          (fun dependency => if dependency.package == package then
            { dependency with version := version } else dependency)) } expected))) = true := by
  decide +kernel

/-- In particular, the unit BorshIoError of ProgramError 3 cannot replace the
selected owned String carrier. Other rows enforce their declared bounds. -/
theorem dependency_bounds_retain_the_selected_domains :
    ([("solana-program-error", ["2.1.0", "3.0.0", "2.2.2-rc.1"])] : List (String × List
      String)).all (fun (package, versions) =>
      fixtures.all (fun (key, build, _) => if (build.dependency package).isSome then
        versions.all (fun version => identitiesMatch key
          { build with dependencies := (build.dependencies.map (fun dependency =>
            if dependency.package == package then { dependency with version := version }
            else dependency)) } []) else true)) = true := by
  decide +kernel

/-- A missing fact is unknown. Wrong and duplicated facts cannot be supplied
by the host machine or hidden by another valid field. -/
theorem target_facts_are_operation_specific :
    fixtures.all (fun (key, build, _) => build.target.all (fun required =>
      let changed : Versioning.TargetFact :=
        ⟨required.field, if required.field == "pointer_width" then "32"
          else if required.field == "os" then "linux"
          else if required.field == "endian" then "big" else "unwind"⟩
      identitiesMatch key { build with target := (build.target.filter
        (fun fact => fact.field != required.field)) } [] &&
      identitiesMatch key { build with target := (build.target.map
        (fun fact => if fact.field == required.field then changed else fact)) } [] &&
      identitiesMatch key { build with target := build.target ++ [required] } [])) = true := by
  decide +kernel

end SolanalibTest.Specs.SplTokenMetadataInterface.Models.Profiles
