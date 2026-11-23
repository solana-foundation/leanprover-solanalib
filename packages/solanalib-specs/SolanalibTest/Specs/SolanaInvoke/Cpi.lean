/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaInvoke.Cpi
public import Solanalib.Specs.SolanaInvoke.Capabilities
public import SolanalibTest.Specs.Core.OpaqueCpi

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaInvoke.Cpi

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi
open SolanalibTest.Specs.Core.OpaqueCpi (registry onchainTarget dependency)
open Solanalib.Specs.SolanaInvoke.Capabilities (catalog)

/-- Every registered signature uses the same exact closed finite execution
witness, while its source identity and ABI remain separate review obligations. -/
theorem signature_has_execution : FamilyHasExecution
    Solanalib.Specs.SolanaInvoke.invoke_signed_contract
      Solanalib.Specs.SolanaInvoke.invoke_signed_run
    Solanalib.Specs.SolanaInvoke.invoke_signed_sample :=
  Solanalib.Specs.SolanaInvoke.invoke_signed_has_execution

def reviewedBuild : Versioning.Build where
  package := "solana-invoke"
  version := "0.4.0"
  source := registry
  target := onchainTarget
  targetFeatures := some []
  dependencies :=
    [dependency "solana-account-info" "2.3.0", dependency "solana-instruction" "2.3.3",
     dependency "solana-stable-layout" "2.2.1", dependency "solana-program-error" "2.2.2",
     dependency "solana-program-entrypoint" "2.3.0", dependency "solana-define-syscall" "2.\
       3.0"]

/-- Synthetic compatible versions exercise declared selection assumptions;
they are not additional inspected or native-tested releases. -/
def compatibleBuild : Versioning.Build :=
  { reviewedBuild with version := "0.4.1", dependencies := (reviewedBuild.dependencies.map (fun dep
    => { dep with version := "2.9.0" })) }

/-- A complete reviewed build supplies the exact source identity. -/
theorem reviewed_build_admitted :
    (catalog.forBuild reviewedBuild).identities .invoke_signed =
      [⟨"solana-invoke", "0.4.0", "solana_invoke::invoke_signed",
        "solana_invoke::invoke_signed"⟩] := by decide +kernel

/-- Compatibility keeps the actual calling-package version and exact source name. -/
theorem compatible_build_actual_identity :
    [{ reviewedBuild with version := "0.4.1" }, compatibleBuild].all (fun build => decide
      ((catalog.forBuild build).identities .invoke_signed =
        [⟨"solana-invoke", "0.4.1", "solana_invoke::invoke_signed",
          "solana_invoke::invoke_signed"⟩])) = true := by decide +kernel

theorem lower_bound_and_prerelease_rejected :
    ["0.3.9", "0.4.1-rc.1"].all (fun version =>
      ((catalog.forBuild { compatibleBuild with version := version }).identities
        .invoke_signed).isEmpty) = true := by decide +kernel

/-- The other individually reviewed instruction release uses the same contract. -/
theorem reviewed_instruction_alternative_admitted :
    (catalog.forBuild { reviewedBuild with dependencies :=
      (reviewedBuild.dependencies.map (fun dep => if dep.package = "solana-instruction" then { dep
        with version := "2.2.1" }
        else dep)) }).identities .invoke_signed =
      (catalog.forBuild reviewedBuild).identities .invoke_signed := by decide +kernel

theorem outside_range_source_or_release_rejected :
    (catalog.forBuild { reviewedBuild with version := "0.5.0" }).identities .invoke_signed = [] ∧
    (catalog.forBuild { reviewedBuild with source :=
      ⟨"git", "https://example.org/invoke-fork", "0123456789012345678901234567890123456789"⟩
      }).identities .invoke_signed = [] := by decide +kernel

/-- Each dependency is selected from the actual function closure. Removing,
substituting or duplicating even one cannot be hidden by other valid entries. -/
theorem every_dependency_is_required :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        ((catalog.forBuild { build with dependencies :=
          (build.dependencies.filter (fun kept => kept.package != dep.package)) }).identities
          .invoke_signed).isEmpty)) = true := by decide +kernel

theorem every_dependency_rejects_outside_range_versions :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        ((catalog.forBuild { build with dependencies :=
          (build.dependencies.map (fun kept => if kept.package = dep.package then
            { kept with version := "99.0.0" } else kept)) }).identities
          .invoke_signed).isEmpty)) = true := by decide +kernel

theorem every_dependency_rejects_ambiguous_resolution :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        ((catalog.forBuild { build with dependencies := build.dependencies ++ [dep] }).identities
          .invoke_signed).isEmpty)) = true := by decide +kernel

theorem every_dependency_rejects_a_fork :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        ((catalog.forBuild { build with dependencies :=
          (build.dependencies.map (fun kept => if kept.package = dep.package then { kept with
            source :=
            ⟨"git", "https://example.org/dependency-fork",
              "0123456789012345678901234567890123456789"⟩ } else kept)) }).identities
          .invoke_signed).isEmpty)) = true := by decide +kernel

theorem every_target_fact_is_required :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.target.all (fun fact =>
        ((catalog.forBuild { build with target :=
          (build.target.filter (fun kept => kept.field != fact.field)) }).identities
          .invoke_signed).isEmpty)) = true := by decide +kernel

theorem changed_target_facts_rejected :
    [reviewedBuild, compatibleBuild].all (fun build =>
      ([⟨"os", "linux"⟩, ⟨"pointer_width", "32"⟩, ⟨"endian", "big"⟩, ⟨"panic", "unwind"⟩] :
        List Versioning.TargetFact).all (fun changed =>
          ((catalog.forBuild { build with target :=
            (build.target.map (fun fact => if fact.field = changed.field then changed else fact))
              }).identities
            .invoke_signed).isEmpty)) = true := by decide +kernel

theorem static_or_unknown_dispatch_rejected :
    [reviewedBuild, compatibleBuild].all (fun build =>
      [none, some ["static-syscalls"]].all (fun targetFeatures =>
        ((catalog.forBuild { build with targetFeatures := targetFeatures }).identities
          .invoke_signed).isEmpty)) = true := by decide +kernel

/-- Duplicate target facts remain unresolved even when their values agree. -/
theorem ambiguous_target_facts_rejected :
    [reviewedBuild, compatibleBuild].all (fun build =>
      build.target.all (fun fact =>
        ((catalog.forBuild { build with target := build.target ++ [fact] }).identities
          .invoke_signed).isEmpty)) = true := by decide +kernel

theorem compatible_source_fork_rejected :
    (catalog.forBuild { compatibleBuild with source :=
      ⟨"git", "https://example.org/cpi-fork", "0123456789012345678901234567890123456789"⟩ }).identities
        .invoke_signed = [] := by decide +kernel

/-- Each provider has its own lower boundary; all these SDK 2 providers also
reject the exclusive next-major boundary and a prerelease inside the numeric interval. -/
theorem dependency_boundaries_and_prereleases_rejected :
    let below : List (String × String) :=
      [("solana-account-info", "2.2.9"),
      ("solana-instruction", "2.2.0"),
      ("solana-stable-layout", "2.2.0"),
      ("solana-program-error", "2.2.1"),
      ("solana-program-entrypoint", "2.2.9"),
      ("solana-define-syscall", "2.2.9")]
    below.all (fun changed =>
      ((catalog.forBuild { compatibleBuild with dependencies :=
        (compatibleBuild.dependencies.map (fun dep => if dep.package = changed.1 then
          { dep with version := changed.2 } else dep)) }).identities .invoke_signed).isEmpty) =
            true ∧
    compatibleBuild.dependencies.all (fun dep =>
      ["3.0.0", "2.9.0-rc.1"].all (fun version =>
        ((catalog.forBuild { compatibleBuild with dependencies :=
          (compatibleBuild.dependencies.map (fun kept => if kept.package = dep.package then
            { kept with version := version } else kept)) }).identities .invoke_signed).isEmpty)) =
              true := by
  decide +kernel

end SolanalibTest.Specs.SolanaInvoke.Cpi

namespace SolanalibTest.Specs.SolanaInvoke.Cpi.InvokeProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.SolanaInvoke.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.invoke,
      {
        package := "solana-invoke",
        version := "0.4.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic",
          "abort"⟩],
        targetFeatures := some [],
        dependencies := [⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-instruction",
          "2.2.1", registry⟩, ⟨"solana-stable-layout", "2.2.1", registry⟩, ⟨"solana-program\
            -error",
          "2.2.0", registry⟩, ⟨"solana-program-entrypoint", "2.3.0", registry⟩,
          ⟨"solana-define-syscall", "2.3.0", registry⟩] },
      [("solana_invoke::invoke", "solana_invoke::invoke")]),
    (.invoke,
      {
        package := "solana-invoke",
        version := "0.4.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic",
          "abort"⟩],
        targetFeatures := some [],
        dependencies := [⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-instruction",
          "2.3.3", registry⟩, ⟨"solana-stable-layout", "2.2.1", registry⟩, ⟨"solana-program\
            -error",
          "2.2.0", registry⟩, ⟨"solana-program-entrypoint", "2.3.0", registry⟩,
          ⟨"solana-define-syscall", "2.3.0", registry⟩] },
      [("solana_invoke::invoke", "solana_invoke::invoke")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.SolanaInvoke.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"solana-invoke", build.version, item, implementation⟩))

def members : List Key := [.invoke]

theorem every_member_has_a_literal_case :
    members.length = 1 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["0.4.0"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["0.4.1", "0.4.99+fixture"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["0.3.0", "0.5.0", "0.4.1-rc.1"].all (fun version => fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- Check the 0.4 profile separately from the SDK 3 profile on the same key. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      let profiles := (Solanalib.Specs.SolanaInvoke.Capabilities.catalog.applicability key).filter
        (fun profile => profile.id == "invoke-0.4.0-borrowed-invoke")
      decide (profiles.length = 1) && profiles.all (fun profile =>
        decide (profile.releases = ["0.4.0"] ∧
          profile.compatibleRanges = [⟨"0.4.0", "0.5.0"⟩]))) = true := by
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
    ([("solana-account-info", ["2.3.0", "2.9.99", "2.9.99+fixture"]),
      ("solana-program-error", ["2.2.0", "2.2.1", "2.2.2", "2.9.99", "2.9.99+fixture"])] : List
        (String × List String)).all (fun (package, versions) =>
      fixtures.all (fun (key, build, expected) => versions.all (fun version =>
        identitiesMatch key { build with dependencies := (build.dependencies.map
          (fun dependency => if dependency.package == package then
            { dependency with version := version } else dependency)) } expected))) = true := by
  decide +kernel

/-- In particular, the unit BorshIoError of ProgramError 3 cannot replace the
selected owned String carrier. Other rows enforce their declared bounds. -/
theorem dependency_bounds_retain_the_selected_domains :
    ([("solana-account-info", ["2.2.1", "3.0.0", "2.3.0-rc.1"]),
      ("solana-program-error", ["2.1.0", "3.0.0", "2.2.2-rc.1"])] : List (String × List
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

theorem dispatch_mode_remains_explicit :
    fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with targetFeatures := none } [] &&
      identitiesMatch key { build with targetFeatures := some ["static-syscalls"] } []) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaInvoke.Cpi.InvokeProfiles

namespace SolanalibTest.Specs.SolanaInvoke.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SolanaInvoke.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SolanaInvoke.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

abbrev Row := Solanalib.Specs.SolanaInvoke.Capabilities.Key × String × String × String

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
  package := "solana-invoke"
  version := "0.5.0"
  source := registry
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "ab\
    ort"⟩]
  targetFeatures := some []
  dependencies := [
    ⟨"solana-account-info", "3.1.1", registry⟩,
    ⟨"solana-instruction", "3.4.0", registry⟩,
    ⟨"solana-stable-layout", "3.0.0", registry⟩,
    ⟨"solana-program-error", "3.0.1", registry⟩,
    ⟨"solana-program-entrypoint", "3.1.1", registry⟩,
    ⟨"solana-define-syscall", "3.0.0", registry⟩]

def rows0 : List Row := [
    (.invoke_signed, "invoke-0.5.0-borrowed-invoke_signed",
      "solana_invoke::invoke_signed", "solana_invoke::invoke_signed")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 1 ∧
    ["0.5.0", "0.5.1"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def accepted0 : List Build := [
  dependencyVersion build0 "solana-account-info" "3.1.2",
  dependencyVersion build0 "solana-instruction" "3.4.1",
  dependencyVersion build0 "solana-stable-layout" "3.0.1",
  dependencyVersion build0 "solana-program-error" "3.0.2",
  dependencyVersion build0 "solana-program-entrypoint" "3.1.2",
  dependencyVersion build0 "solana-define-syscall" "3.0.1"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_0 :
    accepted0.length = 6 ∧
    accepted0.all (fun build => rows0.all (identifies build)) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "0.4.999" },
  { build0 with version := "0.6.0" },
  { build0 with version := "0.5.1-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build0 "solana-account-info" "4.0.0",
  dependencyVersion build0 "solana-instruction" "4.0.0",
  dependencyVersion build0 "solana-stable-layout" "4.0.0",
  dependencyVersion build0 "solana-program-error" "4.0.0",
  dependencyVersion build0 "solana-program-entrypoint" "4.0.0",
  dependencyVersion build0 "solana-define-syscall" "4.0.0",
  { build0 with dependencies := (build0.dependencies.filter (fun dep => dep.package !=
    "solana-account-info")) },
  { build0 with dependencies := (build0.dependencies ++ [⟨"solana-account-info", "3.1.1",
    registry⟩]) },
  { build0 with dependencies := (build0.dependencies.map (fun dep =>
        if dep.package == "solana-account-info" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build0 with target := (build0.target.filter (fun fact => fact.field != "os")) },
  { build0 with target := (build0.target.map (fun fact =>
        if fact.field == "os" then { fact with value := "linux" } else fact)) },
  { build0 with target := (build0.target ++ [⟨"os", "linux"⟩]) },
  { build0 with target := (build0.target.filter (fun fact => fact.field != "pointer_width")) },
  { build0 with target := (build0.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build0 with target := (build0.target ++ [⟨"pointer_width", "32"⟩]) },
  { build0 with target := (build0.target.filter (fun fact => fact.field != "endian")) },
  { build0 with target := (build0.target.map (fun fact =>
        if fact.field == "endian" then { fact with value := "unsupported" } else fact)) },
  { build0 with target := (build0.target ++ [⟨"endian", "unsupported"⟩]) },
  { build0 with target := (build0.target.filter (fun fact => fact.field != "panic")) },
  { build0 with target := (build0.target.map (fun fact =>
        if fact.field == "panic" then { fact with value := "unwind" } else fact)) },
  { build0 with target := (build0.target ++ [⟨"panic", "unwind"⟩]) },
  { build0 with targetFeatures := none },
  { build0 with targetFeatures := some ["static-syscalls"] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 28 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaInvoke.UpdatedProfiles

@[expose] public section

namespace SolanalibTest.Specs.SolanaInvoke.BorrowedInstructionCpi

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.SolanaInvoke.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.SolanaInvoke.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

def build0 : Versioning.Build where
  package := "solana-invoke"
  version := "0.5.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "ab\
    ort"⟩]
  features := none
  targetFeatures := some []
  dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["0.5.0", "0.5.1"].all (fun version =>
      decide (((selectedProfile "invoke-0.5.0-borrowed-invoke").forBuild
        { build0 with version := version }).identities .invoke =
          [⟨"solana-invoke", version, "solana_invoke::invoke",
            "solana_invoke::invoke"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"solana-invoke", "0.5.0", "solana_invoke::invoke",
            "solana_invoke::invoke"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaInvoke.Capabilities.catalog.forBuild
        build0).identities .invoke)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "invoke-0.5.0-borrowed-invoke").applicability .invoke).length = 1 ∧
    ["0.4.999", "0.6.0", "0.5.1-rc.1"].all (fun version =>
      (((selectedProfile "invoke-0.5.0-borrowed-invoke").forBuild { build0 with version := version
        }).identities
        .invoke).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "solana-invoke-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with dependencies := [⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-stable-layout", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-define-syscall", "3.0.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] },
      { build0 with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "ab\
        ort"⟩] },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "littl\
        e"⟩,
        ⟨"panic", "abort"⟩, ⟨"os", "solana"⟩] },
      { build0 with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "ab\
        ort"⟩,
        ⟨"os", "unsupported-target-value"⟩] },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩] },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "littl\
        e"⟩,
        ⟨"panic", "abort"⟩, ⟨"pointer_width", "64"⟩] },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩,
        ⟨"pointer_width", "unsupported-target-value"⟩] },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"panic", "abort"⟩] },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "littl\
        e"⟩,
        ⟨"panic", "abort"⟩, ⟨"endian", "little"⟩] },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"panic", "abort"⟩,
        ⟨"endian", "unsupported-target-value"⟩] },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "littl\
        e"⟩] },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "littl\
        e"⟩,
        ⟨"panic", "abort"⟩, ⟨"panic", "abort"⟩] },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "littl\
        e"⟩,
        ⟨"panic", "unsupported-target-value"⟩] },
      { build0 with targetFeatures := none },
      { build0 with targetFeatures := some ["static-syscalls"] } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.SolanaInvoke.Capabilities.catalog.forBuild build).identities
        .invoke).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaInvoke.BorrowedInstructionCpi
