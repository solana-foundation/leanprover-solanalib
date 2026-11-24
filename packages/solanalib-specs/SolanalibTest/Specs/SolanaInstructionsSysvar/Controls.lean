/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaInstructionsSysvar.Checked
public import Solanalib.Specs.SolanaInstructionsSysvar.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SolanaInstructionsSysvar.Controls

open Solanalib.Contracts.Model Solanalib.Specs.Core InstructionsSysvar.Checked
open InstructionsSysvar.Checked.Witness

theorem short_footer_unwinds_and_releases :
    currentReference currentSample ⟨borrows [], ()⟩ info
      (.unwound .subtractionOverflow ⟨{ borrows [] with slots := [none] }, ()⟩) := by
  exact acquired_exit_retained (Callback.ofFunction (currentBody currentSample.down))
    ⟨borrows [], ()⟩ info rfl ⟨0, 0⟩
    { borrows [] with slots := [some ⟨⟨1⟩, .shared, 0, .whole⟩] } []
    (by rfl) (by rfl) (.unwound .subtractionOverflow ()) (by rfl)

theorem wrapping_footer_has_slice_panic :
    currentBody ⟨false, .unwind⟩ () [] = .unwound .sliceRange () := rfl

theorem footer_abort_has_no_final_state :
    currentBody ⟨true, .abort⟩ () [] = .terminated .subtractionOverflow := rfl

theorem wrong_key_before_missing_cell :
    currentReference currentSample ⟨⟨[], []⟩, ()⟩ AccountInfo.sampleInfo
      (.returned (.error .unsupportedSysvar) ⟨⟨[], []⟩, ()⟩) :=
  wrong_id_first _ _ _ (by decide)

theorem truncated_meta_drops_accounts :
    decode instructionSample 0 {} [1, 0, 4, 0, 1, 0, 3]
      (.returned (.error .invalidArgument) { metas := [none], events := [10, 40] }) := by
  simp [decode, readMetas, protectMetas, word, readMeta, key, takeBytes, instructionSample,
    InstructionBuilder.Sample.metaVec, InstructionBuilder.Sample.allocateMetas,
    InstructionBuilder.Sample.retireMetas, Callback.bind, Callback.ofFunction,
    Owned.cleanup, Owned.VectorOps.dropAction, Solanalib.Runtime.slice, Solanalib.Runtime.leNat]

theorem invalid_index_precedes_allocation :
    decode instructionSample (UInt64.ofNat (2^64 - 1)) {} [1, 0]
      (.returned (.error .invalidArgument) {}) := by
  simp [decode, word, takeBytes, Solanalib.Runtime.slice, Solanalib.Runtime.leNat]

theorem ignored_high_flag_bits :
    readMeta ([131] ++ Solanalib.Runtime.Pubkey.zero.bytes) 0 =
      some (Instruction.accountMeta .zero true true, 33) := by decide

end SolanalibTest.Specs.SolanaInstructionsSysvar.Controls

namespace SolanalibTest.Specs.SolanaInstructionsSysvar.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SolanaInstructionsSysvar.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SolanaInstructionsSysvar.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

abbrev Row := Solanalib.Specs.SolanaInstructionsSysvar.Capabilities.Key × String × String × String

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
  package := "solana-instructions-sysvar"
  version := "4.0.0"
  source := registry
  target := [⟨"pointer_width", "64"⟩]
  dependencies := [
    ⟨"solana-account-info", "3.1.1", registry⟩,
    ⟨"solana-program-error", "3.0.1", registry⟩,
    ⟨"solana-sdk-ids", "3.1.0", registry⟩,
    ⟨"solana-serialize-utils", "3.1.2", registry⟩,
    ⟨"solana-instruction", "3.4.0", registry⟩,
    ⟨"solana-sanitize", "3.0.1", registry⟩]

def rows0 : List Row := [
    (.load_instruction_at_checked, "checked-4.0.0",
      "solana_instructions_sysvar::load_instruction_at_checked",
        "solana_instructions_sysvar::load_instruction_at_checked")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 1 ∧
    ["4.0.0", "4.0.1"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def accepted0 : List Build := [
  dependencyVersion build0 "solana-account-info" "3.1.2",
  dependencyVersion build0 "solana-program-error" "3.0.2",
  dependencyVersion build0 "solana-sdk-ids" "3.1.1",
  dependencyVersion build0 "solana-serialize-utils" "3.1.3",
  dependencyVersion build0 "solana-instruction" "3.4.1",
  dependencyVersion build0 "solana-sanitize" "3.0.2"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_0 :
    accepted0.length = 6 ∧
    accepted0.all (fun build => rows0.all (identifies build)) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "3.999.999" },
  { build0 with version := "5.0.0" },
  { build0 with version := "4.0.1-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build0 "solana-account-info" "4.0.0",
  dependencyVersion build0 "solana-program-error" "4.0.0",
  dependencyVersion build0 "solana-sdk-ids" "4.0.0",
  dependencyVersion build0 "solana-serialize-utils" "4.0.0",
  dependencyVersion build0 "solana-instruction" "4.0.0",
  dependencyVersion build0 "solana-sanitize" "4.0.0",
  { build0 with dependencies := (build0.dependencies.filter (fun dep => dep.package !=
    "solana-account-info")) },
  { build0 with dependencies := (build0.dependencies ++ [⟨"solana-account-info", "3.1.1",
    registry⟩]) },
  { build0 with dependencies := (build0.dependencies.map (fun dep =>
        if dep.package == "solana-account-info" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build0 with target := (build0.target.filter (fun fact => fact.field != "pointer_width")) },
  { build0 with target := (build0.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build0 with target := (build0.target ++ [⟨"pointer_width", "32"⟩]) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 17 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

def build1 : Build where
  package := "solana-instructions-sysvar"
  version := "4.0.0"
  source := registry
  target := [⟨"pointer_width", "64"⟩]
  dependencies := [
    ⟨"solana-account-info", "3.1.1", registry⟩,
    ⟨"solana-program-error", "3.0.1", registry⟩,
    ⟨"solana-sdk-ids", "3.1.0", registry⟩]

def rows1 : List Row := [
    (.load_current_index_checked, "checked-4.0.0",
      "solana_instructions_sysvar::load_current_index_checked",
        "solana_instructions_sysvar::load_current_index_checked")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_1 :
    rows1.length = 1 ∧
    ["4.0.0", "4.0.1"].all (fun version =>
      rows1.all (identifies { build1 with version := version })) = true := by
  decide +kernel

def accepted1 : List Build := [
  dependencyVersion build1 "solana-account-info" "3.1.2",
  dependencyVersion build1 "solana-program-error" "3.0.2",
  dependencyVersion build1 "solana-sdk-ids" "3.1.1"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_1 :
    accepted1.length = 3 ∧
    accepted1.all (fun build => rows1.all (identifies build)) = true := by
  decide +kernel

def rejected1 : List Build := [
  { build1 with version := "3.999.999" },
  { build1 with version := "5.0.0" },
  { build1 with version := "4.0.1-rc.1" },
  { build1 with package := "unrelated-library" },
  { build1 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build1 "solana-account-info" "4.0.0",
  dependencyVersion build1 "solana-program-error" "4.0.0",
  dependencyVersion build1 "solana-sdk-ids" "4.0.0",
  { build1 with dependencies := (build1.dependencies.filter (fun dep => dep.package !=
    "solana-account-info")) },
  { build1 with dependencies := (build1.dependencies ++ [⟨"solana-account-info", "3.1.1",
    registry⟩]) },
  { build1 with dependencies := (build1.dependencies.map (fun dep =>
        if dep.package == "solana-account-info" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build1 with target := (build1.target.filter (fun fact => fact.field != "pointer_width")) },
  { build1 with target := (build1.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build1 with target := (build1.target ++ [⟨"pointer_width", "32"⟩]) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_1 :
    rejected1.length = 14 ∧
    rejected1.all (fun build => rows1.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaInstructionsSysvar.UpdatedProfiles

@[expose] public section

namespace SolanalibTest.Specs.SolanaInstructionsSysvar.V3V4Controls

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.SolanaInstructionsSysvar.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.SolanaInstructionsSysvar.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

def build0 : Versioning.Build where
  package := "solana-instructions-sysvar"
  version := "3.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩]
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["3.0.0", "3.1.0"].all (fun version =>
      decide (((selectedProfile "checked-3.0.0").forBuild
        { build0 with version := version }).identities .load_current_index_checked =
          [⟨"solana-instructions-sysvar", version,
            "solana_instructions_sysvar::load_current_index_checked",
            "solana_instructions_sysvar::load_current_index_checked"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"solana-instructions-sysvar", "3.0.0",
      "solana_instructions_sysvar::load_current_index_checked",
            "solana_instructions_sysvar::load_current_index_checked"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaInstructionsSysvar.Capabilities.catalog.forBuild
        build0).identities .load_current_index_checked)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "checked-3.0.0").applicability .load_current_index_checked).length = 1 ∧
    ["2.999.999", "4.0.0", "3.1.0-rc.1"].all (fun version =>
      (((selectedProfile "checked-3.0.0").forBuild { build0 with version := version }).identities
        .load_current_index_checked).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "solana-instructions-sysvar-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with dependencies := [⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] },
      { build0 with target := [] },
      { build0 with target := [⟨"pointer_width", "64"⟩, ⟨"pointer_width", "64"⟩] },
      { build0 with target := [⟨"pointer_width", "unsupported-target-value"⟩] } ] : List
        Versioning.Build).all
      (fun build => (((selectedProfile "checked-3.0.0").forBuild build).identities
        .load_current_index_checked).isEmpty) = true := by
  decide +kernel

def build1 : Versioning.Build where
  package := "solana-instructions-sysvar"
  version := "3.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩]
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile1_literal_identities :
    ["3.0.0", "3.1.0"].all (fun version =>
      decide (((selectedProfile "checked-3.0.0").forBuild
        { build1 with version := version }).identities .load_instruction_at_checked =
          [⟨"solana-instructions-sysvar", version,
            "solana_instructions_sysvar::load_instruction_at_checked",
            "solana_instructions_sysvar::load_instruction_at_checked"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile1_present_in_full_catalog :
    ([⟨"solana-instructions-sysvar", "3.0.0",
      "solana_instructions_sysvar::load_instruction_at_checked",
            "solana_instructions_sysvar::load_instruction_at_checked"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaInstructionsSysvar.Capabilities.catalog.forBuild
        build1).identities .load_instruction_at_checked)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile1_range_rejections :
    ((selectedProfile "checked-3.0.0").applicability .load_instruction_at_checked).length = 1 ∧
    ["2.999.999", "4.0.0", "3.1.0-rc.1"].all (fun version =>
      (((selectedProfile "checked-3.0.0").forBuild { build1 with version := version }).identities
        .load_instruction_at_checked).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile1_build_rejections :
    ([{ build1 with package := "solana-instructions-sysvar-other" },
      { build1 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build1 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build1 with dependencies := [⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sdk-ids", "3.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-serialize-utils", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-instruction", "3.4.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-sanitize", "3.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] },
      { build1 with target := [] },
      { build1 with target := [⟨"pointer_width", "64"⟩, ⟨"pointer_width", "64"⟩] },
      { build1 with target := [⟨"pointer_width", "unsupported-target-value"⟩] } ] : List
        Versioning.Build).all
      (fun build => (((selectedProfile "checked-3.0.0").forBuild build).identities
        .load_instruction_at_checked).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaInstructionsSysvar.V3V4Controls
