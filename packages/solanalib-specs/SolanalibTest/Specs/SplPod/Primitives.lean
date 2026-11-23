/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplPod.Primitives
public import Solanalib.Specs.SplPod.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SplPod.Primitives

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- An asymmetric stored word distinguishes the two byte orders. -/
abbrev word16 : SdkValue.U16 := ⟨[0x12, 0x34], rfl⟩

/-- The selected POD contract decodes its complete stored word as little-endian. -/
theorem u16_little_endian :
    Solanalib.Specs.SplPod.primitives.PodU16.into_u16_contract.ensures () word16 0x3412 () := by
  unfold Solanalib.Specs.SplPod.primitives.PodU16.into_u16_contract SdkValue.intoU16Contract
    Solanalib.Contracts.Model.ensures
  decide +kernel

/-- The selected POD contract rejects the opposite byte order. -/
theorem u16_rejects_big_endian :
    ¬ Solanalib.Specs.SplPod.primitives.PodU16.into_u16_contract.ensures () word16 0x1234 () := by
  unfold Solanalib.Specs.SplPod.primitives.PodU16.into_u16_contract SdkValue.intoU16Contract
    Solanalib.Contracts.Model.ensures
  decide +kernel

end SolanalibTest.Specs.SplPod.Primitives

namespace SolanalibTest.Specs.SplPod.Primitives.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def primitives_PodU16_into_u16Build : Versioning.Build where
  package := "spl-pod"
  version := "0.5.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def primitives_PodU16_into_u16Cases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.5.0; eligible
  (primitives_PodU16_into_u16Build, true),
  -- inspected-reference-0.5.1; eligible
  ({ primitives_PodU16_into_u16Build with version := "0.5.1" }, true),
  -- lower; eligible
  (primitives_PodU16_into_u16Build, true),
  -- hypothetical-declaration-probe; eligible
  ({ primitives_PodU16_into_u16Build with version := "0.5.97" }, true),
  -- exclusive-upper; unsupported
  ({ primitives_PodU16_into_u16Build with version := "0.6.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ primitives_PodU16_into_u16Build with version := "0.5.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ primitives_PodU16_into_u16Build with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ primitives_PodU16_into_u16Build with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.4.999; unsupported
  ({ primitives_PodU16_into_u16Build with version := "0.4.999" }, false)
]

set_option maxRecDepth 8192 in
theorem primitives_PodU16_into_u16_profile_controls :
    primitives_PodU16_into_u16Cases.all (fun test =>
      (((Solanalib.Specs.SplPod.Capabilities.catalog.applicability .primitives_PodU16_into_u16).any
        (fun profile => ["reviewed-0-5-1"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem primitives_PodU16_into_u16_callable_identities :
    ["0.5.0", "0.5.1", "0.5.97"].all (fun version =>
      (((Solanalib.Specs.SplPod.Capabilities.catalog.forBuild
        { primitives_PodU16_into_u16Build with version := version }).identities
          .primitives_PodU16_into_u16).eraseDups ==
        [⟨"spl-pod", version, "core::convert::From::from",
          "spl_pod::primitives::<impl core::convert::From<spl_pod::primitives::PodU16> for \
            u16>::from"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def primitives_PodU64_into_u64Build : Versioning.Build where
  package := "spl-pod"
  version := "0.5.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def primitives_PodU64_into_u64Cases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.5.0; eligible
  (primitives_PodU64_into_u64Build, true),
  -- inspected-reference-0.5.1; eligible
  ({ primitives_PodU64_into_u64Build with version := "0.5.1" }, true),
  -- lower; eligible
  (primitives_PodU64_into_u64Build, true),
  -- hypothetical-declaration-probe; eligible
  ({ primitives_PodU64_into_u64Build with version := "0.5.97" }, true),
  -- exclusive-upper; unsupported
  ({ primitives_PodU64_into_u64Build with version := "0.6.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ primitives_PodU64_into_u64Build with version := "0.5.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ primitives_PodU64_into_u64Build with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ primitives_PodU64_into_u64Build with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.4.999; unsupported
  ({ primitives_PodU64_into_u64Build with version := "0.4.999" }, false)
]

set_option maxRecDepth 8192 in
theorem primitives_PodU64_into_u64_profile_controls :
    primitives_PodU64_into_u64Cases.all (fun test =>
      (((Solanalib.Specs.SplPod.Capabilities.catalog.applicability .primitives_PodU64_into_u64).any
        (fun profile => ["reviewed-0-5-1"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem primitives_PodU64_into_u64_callable_identities :
    ["0.5.0", "0.5.1", "0.5.97"].all (fun version =>
      (((Solanalib.Specs.SplPod.Capabilities.catalog.forBuild
        { primitives_PodU64_into_u64Build with version := version }).identities
          .primitives_PodU64_into_u64).eraseDups ==
        [⟨"spl-pod", version, "core::convert::From::from",
          "spl_pod::primitives::<impl core::convert::From<spl_pod::primitives::PodU64> for \
            u64>::from"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.SplPod.Primitives.Pr575Compatibility
