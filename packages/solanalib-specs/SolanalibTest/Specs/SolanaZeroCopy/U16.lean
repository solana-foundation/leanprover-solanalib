/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaZeroCopy.U16
public import Solanalib.Specs.SolanaZeroCopy.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaZeroCopy.U16

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Distinct bytes distinguish little-endian conversion from byte reversal. -/
abbrev word16 : SdkValue.U16 := ⟨[0x12, 0x34], rfl⟩

/-- The selected 1.1.1 contract returns the full little-endian value. -/
theorem little_endian :
    Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_contract.ensures
      () word16 0x3412 () := by
  unfold Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_contract
    SdkValue.intoU16Contract Solanalib.Contracts.Model.ensures
  decide +kernel

end SolanalibTest.Specs.SolanaZeroCopy.U16

namespace SolanalibTest.Specs.SolanaZeroCopy.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SolanaZeroCopy.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SolanaZeroCopy.Capabilities.catalog.applicability key).filter (fun profile
        => profile.id == id) }

abbrev Row := Solanalib.Specs.SolanaZeroCopy.Capabilities.Key × String × String × String

def identifies (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 =
    [⟨build.package, build.version, row.2.2.1, row.2.2.2⟩])

def rejects (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 = [])

def registry : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def build0 : Build where
  package := "solana-zero-copy"
  version := "1.1.1"
  source := registry

def rows0 : List Row := [
    (.unaligned_U16_into_u16, "reviewed-1-1-1",
      "core::convert::From::from",
        "solana_zero_copy::unaligned::<impl \
          core::convert::From<solana_zero_copy::unaligned::U16> for u16>::from")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 1 ∧
    ["1.1.1", "1.1.2"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "1.1.0" },
  { build0 with version := "2.0.0" },
  { build0 with version := "1.1.2-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 5 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaZeroCopy.UpdatedProfiles

@[expose] public section

namespace SolanalibTest.Specs.SolanaZeroCopy.V1U16

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.SolanaZeroCopy.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.SolanaZeroCopy.Capabilities.catalog.applicability key).filter (fun profile
        => profile.id == id) }

def build0 : Versioning.Build where
  package := "solana-zero-copy"
  version := "1.0.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["1.0.1", "1.0.2"].all (fun version =>
      decide (((selectedProfile "reviewed-1-0-1").forBuild
        { build0 with version := version }).identities .unaligned_U16_into_u16 =
          [⟨"solana-zero-copy", version, "core::convert::From::from",
            "solana_zero_copy::unaligned::<impl \
              core::convert::From<solana_zero_copy::unaligned::U16> for u16>::from"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"solana-zero-copy", "1.0.1", "core::convert::From::from",
            "solana_zero_copy::unaligned::<impl \
              core::convert::From<solana_zero_copy::unaligned::U16> for u16>::from"⟩] : List
                Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaZeroCopy.Capabilities.catalog.forBuild
        build0).identities .unaligned_U16_into_u16)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "reviewed-1-0-1").applicability .unaligned_U16_into_u16).length = 1 ∧
    ["1.0.0", "2.0.0", "1.0.2-rc.1"].all (fun version =>
      (((selectedProfile "reviewed-1-0-1").forBuild { build0 with version := version }).identities
        .unaligned_U16_into_u16).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "solana-zero-copy-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "reviewed-1-0-1").forBuild build).identities
        .unaligned_U16_into_u16).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaZeroCopy.V1U16
