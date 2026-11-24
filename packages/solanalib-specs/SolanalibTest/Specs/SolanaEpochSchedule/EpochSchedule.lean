/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaEpochSchedule.EpochSchedule
public import Solanalib.Specs.SolanaEpochSchedule.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SolanaEpochSchedule.Controls

open Solanalib.Specs.Core.EpochSchedule

theorem normal_boundary :
    firstSlot defaultValue 14 = 524256 ∧ firstSlot defaultValue 15 = 956256 := by decide

theorem public_fields_need_no_consistency :
    firstSlot ⟨7, 0, false, 2, 900⟩ 2 = 96 ∧
      firstSlot ⟨7, 0, false, 2, 900⟩ 3 = 907 := by decide

theorem truncating_u32_cast :
    firstSlot ⟨1, 0, true, UInt64.ofNat (2^32), 0⟩ (UInt64.ofNat (2^32)) = 0 := by decide

theorem last_slot_saturates_before_subtraction :
    lastSlot ⟨UInt64.ofNat (2^64 - 1), 0, false, 0, 0⟩ 1 = UInt64.ofNat (2^64 - 2) := by decide

theorem zero_length_epoch_uses_saturating_subtraction :
    lastSlot ⟨0, 0, false, 0, 0⟩ 0 = 0 := by decide

end SolanalibTest.Specs.SolanaEpochSchedule.Controls

@[expose] public section

namespace SolanalibTest.Specs.SolanaEpochSchedule.V3EpochSchedule

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.SolanaEpochSchedule.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.SolanaEpochSchedule.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

def build0 : Versioning.Build where
  package := "solana-epoch-schedule"
  version := "3.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["3.0.0", "3.1.0", "3.1.1", "3.2.0", "3.3.0", "3.4.0", "3.5.0"].all (fun version =>
      decide (((selectedProfile "epoch-schedule-3.0.0").forBuild
        { build0 with version := version }).identities .EpochSchedule_get_first_slot_in_epoch =
          [⟨"solana-epoch-schedule", version,
            "solana_epoch_schedule::EpochSchedule::get_first_slot_in_epoch",
            "solana_epoch_schedule::EpochSchedule::get_first_slot_in_epoch"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"solana-epoch-schedule", "3.0.0",
      "solana_epoch_schedule::EpochSchedule::get_first_slot_in_epoch",
            "solana_epoch_schedule::EpochSchedule::get_first_slot_in_epoch"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaEpochSchedule.Capabilities.catalog.forBuild
        build0).identities .EpochSchedule_get_first_slot_in_epoch)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "epoch-schedule-3.0.0").applicability
      .EpochSchedule_get_first_slot_in_epoch).length = 1 ∧
    ["2.999.999", "4.0.0", "3.5.0-rc.1"].all (fun version =>
      (((selectedProfile "epoch-schedule-3.0.0").forBuild { build0 with version := version
        }).identities
        .EpochSchedule_get_first_slot_in_epoch).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "solana-epoch-schedule-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "epoch-schedule-3.0.0").forBuild build).identities
        .EpochSchedule_get_first_slot_in_epoch).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaEpochSchedule.V3EpochSchedule
