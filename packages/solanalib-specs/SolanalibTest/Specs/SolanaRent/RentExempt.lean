/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaRent.RentExempt
public import Solanalib.Specs.SolanaRent.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SolanaRent.RentExempt

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.SolanaRent.Rent

theorem exact_threshold :
    is_exempt .release (Sysvar.defaultRent300, 890879, 0) = .returned false .release ∧
      is_exempt .release (Sysvar.defaultRent300, 890880, 0) = .returned true .release := ⟨rfl, rfl⟩

theorem nan_zero_balance :
    is_exempt .release (⟨3480, 0x7ff8000000000001, 50⟩, 0, 165) =
      .returned true .release := rfl

theorem overflow_precedes_comparison :
    is_exempt .checked (Sysvar.defaultRent300, UInt64.ofNat (2^64 - 1), UInt64.ofNat (2^64 - 1)) =
      .terminated .additionOverflow := rfl

theorem multiplication_overflow_precedes_comparison :
    is_exempt .checked (⟨UInt64.ofNat (2^64 - 1), Sysvar.thresholdTwo, 50⟩,
      UInt64.ofNat (2^64 - 1), 0) = .terminated .multiplicationOverflow := rfl

def checkedUnwind : Profile := ⟨true, .unwind⟩

theorem overflow_unwind_preserves_profile :
    is_exempt checkedUnwind (Sysvar.defaultRent300, 0, UInt64.ofNat (2^64 - 1)) =
      .unwound .additionOverflow checkedUnwind := rfl

theorem infinite_threshold_requires_maximum_balance :
    is_exempt .release (⟨3480, 0x7ff0000000000000, 50⟩, UInt64.ofNat (2^64 - 2), 0) =
      .returned false .release ∧
    is_exempt .release (⟨3480, 0x7ff0000000000000, 50⟩, UInt64.ofNat (2^64 - 1), 0) =
      .returned true .release := ⟨rfl, rfl⟩

def selectedBuild : Versioning.Build where
  package := "solana-rent"
  version := "2.2.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩]

theorem compatible_exemption_identities :
    ["2.2.1", "2.2.2", "2.9.0"].all (fun version => decide
      ((Solanalib.Specs.SolanaRent.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities .Rent_is_exempt =
        [⟨"solana-rent", version, "solana_rent::Rent::is_exempt",
          "solana_rent::Rent::is_exempt"⟩])) = true := by
  decide +kernel

theorem outside_exemption_range_rejected :
    ["2.2.0", "4.0.0", "2.2.2-rc.1"].all (fun version => decide
      ((Solanalib.Specs.SolanaRent.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities .Rent_is_exempt = [])) = true := by
  decide +kernel

theorem unsupported_exemption_width_rejected :
    (Solanalib.Specs.SolanaRent.Capabilities.catalog.forBuild
      { selectedBuild with version := "2.2.2", target := [⟨"pointer_width", "32"⟩] }).identities
        .Rent_is_exempt = [] := by
  decide +kernel

theorem unknown_exemption_width_rejected :
    (Solanalib.Specs.SolanaRent.Capabilities.catalog.forBuild
      { selectedBuild with version := "2.2.2", target := [] }).identities .Rent_is_exempt = [] := by
  decide +kernel

end SolanalibTest.Specs.SolanaRent.RentExempt

namespace SolanalibTest.Specs.SolanaRent.RentExempt.Profiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

def build (version : String) : Versioning.Build :=
  {
    package := "solana-rent", version := version,
    source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩,
    target := [⟨"pointer_width", "64"⟩] }

/-- 3.0.0/3.1.0 are inspected additions; the other 2.x/3.x versions exercise
declared compatibility. Retain the actual selected package version. -/
theorem inherited_and_added_rent_identities :
    ["2.2.1", "2.2.2", "2.9.99", "3.0.0", "3.1.0", "3.1.1", "3.9.99+fixture"].all
      (fun version => decide
        ((Solanalib.Specs.SolanaRent.Capabilities.catalog.forBuild (build version)).identities
          .Rent_is_exempt =
          [⟨"solana-rent", version, "solana_rent::Rent::is_exempt",
            "solana_rent::Rent::is_exempt"⟩])) = true := by
  decide +kernel

/-- Rent 4 changes the public threshold representation and adds size/rate
validation plus specialized arithmetic. It is outside the retained contract. -/
theorem incompatible_representation_and_bounds :
    ["2.2.0", "4.0.0", "3.1.1-rc.1"].all (fun version =>
      ((Solanalib.Specs.SolanaRent.Capabilities.catalog.forBuild (build version)).identities
        .Rent_is_exempt).isEmpty) = true := by
  decide +kernel

theorem added_rent_references_preserve_width_and_origin :
    ["3.0.0", "3.1.0", "3.1.1"].all (fun version =>
      let selected := build version
      ((Solanalib.Specs.SolanaRent.Capabilities.catalog.forBuild { selected with target := []
        }).identities
        .Rent_is_exempt).isEmpty &&
      ((Solanalib.Specs.SolanaRent.Capabilities.catalog.forBuild
        { selected with target := [⟨"pointer_width", "32"⟩] }).identities .Rent_is_exempt).isEmpty
          &&
      ((Solanalib.Specs.SolanaRent.Capabilities.catalog.forBuild
        { selected with target := [⟨"pointer_width", "64"⟩, ⟨"pointer_width", "64"⟩] }).identities
          .Rent_is_exempt).isEmpty &&
      ((Solanalib.Specs.SolanaRent.Capabilities.catalog.forBuild { selected with source :=
        ⟨"git", "https://example.invalid/rent", "0123456789012345678901234567890123456789"⟩ }).identities
          .Rent_is_exempt).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaRent.RentExempt.Profiles
