/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.Core.SdkValues
public import Solanalib.Specs.SplPod.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SplPod.V0OptionalKeys

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.SplPod.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.SplPod.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

def build0 : Versioning.Build where
  package := "spl-pod"
  version := "0.7.3"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["0.7.1", "0.7.3", "0.7.4", "0.7.5"].all (fun version =>
      decide (((selectedProfile "reviewed-0-7-3").forBuild
        { build0 with version := version }).identities
          .optional_keys_OptionalNonZeroPubkey_into_option =
          [⟨"spl-pod", version, "core::convert::From::from",
            "spl_pod::optional_keys::<impl \
              core::convert::From<spl_pod::optional_keys::OptionalNonZeroPubkey> for \
              core::option::Option<solana_address::Address>>::from"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"spl-pod", "0.7.3", "core::convert::From::from",
            "spl_pod::optional_keys::<impl \
              core::convert::From<spl_pod::optional_keys::OptionalNonZeroPubkey> for \
              core::option::Option<solana_address::Address>>::from"⟩] : List
                Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SplPod.Capabilities.catalog.forBuild build0).identities
        .optional_keys_OptionalNonZeroPubkey_into_option)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "reviewed-0-7-3").applicability
      .optional_keys_OptionalNonZeroPubkey_into_option).length = 1 ∧
    ["0.7.0", "0.8.0", "0.7.5-rc.1"].all (fun version =>
      (((selectedProfile "reviewed-0-7-3").forBuild { build0 with version := version }).identities
        .optional_keys_OptionalNonZeroPubkey_into_option).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "spl-pod-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with dependencies := [⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-pubkey", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-pubkey", "3.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "reviewed-0-7-3").forBuild build).identities
        .optional_keys_OptionalNonZeroPubkey_into_option).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SplPod.V0OptionalKeys
