/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.Core.SdkValues
public import Solanalib.Specs.SolanaProgramOption.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaProgramOption.Values.Profiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.SolanaProgramOption.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.COption_as_ref,
      {
        package := "solana-program-option",
        version := "2.1.0",
        source := registry },
      [("solana_program_option::COption::<T>::as_ref",
        "solana_program_option::COption::<T>::as_ref")]),
    (.COption_as_ref,
      {
        package := "solana-program-option",
        version := "2.1.0",
        source := registry,
        dependencies := [⟨"solana-pubkey", "2.2.1", registry⟩] },
      [("solana_program_option::COption::<T>::as_ref",
        "solana_program_option::COption::<T>::as_ref"),
        ("solana_program_option::COption::<T>::as_ref",
          "solana_program_option::COption::<T>::as_ref")]),
    (.COption_as_ref,
      {
        package := "solana-program-option",
        version := "2.1.0",
        source := registry,
        dependencies := [⟨"solana-pubkey", "2.4.0", registry⟩] },
      [("solana_program_option::COption::<T>::as_ref",
        "solana_program_option::COption::<T>::as_ref"),
        ("solana_program_option::COption::<T>::as_ref",
          "solana_program_option::COption::<T>::as_ref")]),
    (.COption_is_none,
      {
        package := "solana-program-option",
        version := "2.1.0",
        source := registry },
      [("solana_program_option::COption::<T>::is_none",
        "solana_program_option::COption::<T>::is_none")]),
    (.COption_is_none,
      {
        package := "solana-program-option",
        version := "2.1.0",
        source := registry,
        dependencies := [⟨"solana-pubkey", "2.2.1", registry⟩] },
      [("solana_program_option::COption::<T>::is_none",
        "solana_program_option::COption::<T>::is_none"),
        ("solana_program_option::COption::<T>::is_none",
          "solana_program_option::COption::<T>::is_none")]),
    (.COption_is_none,
      {
        package := "solana-program-option",
        version := "2.1.0",
        source := registry,
        dependencies := [⟨"solana-pubkey", "2.4.0", registry⟩] },
      [("solana_program_option::COption::<T>::is_none",
        "solana_program_option::COption::<T>::is_none"),
        ("solana_program_option::COption::<T>::is_none",
          "solana_program_option::COption::<T>::is_none")]),
    (.COption_map,
      {
        package := "solana-program-option",
        version := "2.1.0",
        source := registry },
      [("solana_program_option::COption::<T>::map", "solana_program_option::COption::<T>::m\
        ap")]),
    (.COption_unwrap_or,
      {
        package := "solana-program-option",
        version := "2.1.0",
        source := registry },
      [("solana_program_option::COption::<T>::unwrap_or",
        "solana_program_option::COption::<T>::unwrap_or"),
        ("solana_program_option::COption::<T>::unwrap_or",
          "solana_program_option::COption::<T>::unwrap_or")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.SolanaProgramOption.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"solana-program-option", build.version, item, implementation⟩))

def members : List Key := [.COption_as_ref, .COption_is_none, .COption_map, .COption_unwrap_or]

theorem every_member_has_a_literal_case :
    members.length = 4 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["2.1.0", "2.2.0", "2.2.1"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["2.1.1", "2.9.99+fixture"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["2.0.99", "3.0.0", "3.1.0", "2.2.2-rc.1"].all (fun version => fixtures.all (fun (key, build,
      _) =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- An interval must not conceal a missing reference or a changed item range. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      !(Solanalib.Specs.SolanaProgramOption.Capabilities.catalog.applicability key).isEmpty &&
      (Solanalib.Specs.SolanaProgramOption.Capabilities.catalog.applicability key).all (fun profile
        =>
        decide (profile.releases = ["2.1.0", "2.2.0", "2.2.1"] ∧
          profile.compatibleRanges = [⟨"2.1.0", "3.0.0"⟩]))) = true := by
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

/-- A failed concrete key profile leaves the generic profile available; it
does not authorize the source binding of that concrete payload. -/
def withoutKeyProfile : Key → List (String × String)
  | .COption_as_ref => [("solana_program_option::COption::<T>::as_ref",
      "solana_program_option::COption::<T>::as_ref")]
  | .COption_is_none => [("solana_program_option::COption::<T>::is_none",
      "solana_program_option::COption::<T>::is_none")]
  | _ => []

/-- Each required edge is checked independently. Duplicate compatible
candidates remain ambiguous actual dependency facts. -/
theorem dependency_facts_cannot_be_missing_wrong_or_ambiguous :
    fixtures.all (fun (key, build, _) => build.dependencies.all (fun required =>
      identitiesMatch key { build with dependencies := (build.dependencies.filter
        (fun dependency => dependency.package != required.package)) } (withoutKeyProfile key) &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with version := "99.0.0" } else dependency)) } (withoutKeyProfile key) &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with source :=
            ⟨"git", "https://example.invalid/dependency", "01234567890123456789012345678901\
              23456789"⟩ }
          else dependency)) } (withoutKeyProfile key) &&
      identitiesMatch key { build with dependencies := build.dependencies ++ [required] }
        (withoutKeyProfile key))) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaProgramOption.Values.Profiles

namespace SolanalibTest.Specs.SolanaProgramOption.Values.ConcreteKeyProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def build : Versioning.Build :=
  {
    package := "solana-program-option", version := "2.2.1", source := registry }

/-- Missing or mismatched nominal key providers fail the concrete profile,
even though the generic family can still have a callable identity. -/
theorem concrete_key_profile_keeps_its_actual_dependency :
    ([Solanalib.Specs.SolanaProgramOption.Capabilities.Key.COption_as_ref, .COption_is_none]).all
      (fun key =>
        let selected := (Solanalib.Specs.SolanaProgramOption.Capabilities.catalog.applicability
          key).filter
          (fun profile => profile.id == "reviewed-key")
        selected.length == 1 &&
        selected.all (fun profile => !profile.matches build &&
          ["2.2.1", "2.4.0"].all (fun version => profile.matches
            { build with dependencies := [⟨"solana-pubkey", version, registry⟩] }) &&
          ["2.3.0", "3.0.0"].all (fun version => !profile.matches
            { build with dependencies := [⟨"solana-pubkey", version, registry⟩] }))) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaProgramOption.Values.ConcreteKeyProfiles
