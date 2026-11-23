/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplMemo
public import Solanalib.Specs.SplMemo.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SplMemo

/-- The memo program constant is a nonzero key and retains the original state. -/
theorem constant_is_nonzero :
    Solanalib.Specs.SplMemo.id_reference () () = (Solanalib.Specs.SplMemo.declaredId, ()) ∧
      Solanalib.Specs.SplMemo.declaredId ≠ Solanalib.Runtime.Pubkey.zero := by decide +kernel

end SolanalibTest.Specs.SplMemo

namespace SolanalibTest.Specs.SplMemo.Profiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.SplMemo.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.id,
      {
        package := "spl-memo",
        version := "6.0.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩],
        dependencies := [⟨"solana-pubkey", "2.2.1", registry⟩] },
      [("spl_memo::id", "spl_memo::id")]),
    (.id,
      {
        package := "spl-memo",
        version := "6.0.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩],
        dependencies := [⟨"solana-pubkey", "2.4.0", registry⟩] },
      [("spl_memo::id", "spl_memo::id")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.SplMemo.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"spl-memo", build.version, item, implementation⟩))

def members : List Key := [.id]

theorem every_member_has_a_literal_case :
    members.length = 1 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["6.0.0"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["6.0.1", "6.9.99+fixture"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["5.0.0", "7.0.0", "6.0.1-rc.1"].all (fun version => fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- An interval must not conceal a missing reference or a changed item range. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      !(Solanalib.Specs.SplMemo.Capabilities.catalog.applicability key).isEmpty &&
      (Solanalib.Specs.SplMemo.Capabilities.catalog.applicability key).all (fun profile =>
        decide (profile.releases = ["6.0.0"] ∧
          profile.compatibleRanges = [⟨"6.0.0", "7.0.0"⟩]))) = true := by
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

end SolanalibTest.Specs.SplMemo.Profiles
