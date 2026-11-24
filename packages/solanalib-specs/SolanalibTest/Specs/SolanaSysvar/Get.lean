/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaSysvar.Get
public import Solanalib.Specs.SolanaSysvar.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaSysvar

open Solanalib.Contracts.Model Solanalib.Specs.Core

def failedClock : Sysvar.GetterIndex Sysvar.Clock where
  State := Nat
  Unwind := String
  Terminal := String
  target := .hostStub
  read := Callback.ofFunction fun (state : Nat) _ =>
    .returned ⟨1, none⟩ (state + 1)

theorem typed_clock_error_preserves_actual_callback_state :
    Solanalib.Specs.SolanaSysvar.clock.Clock.get_run failedClock
      (3 : Nat) () (.returned (.error .unsupportedSysvar) (4 : Nat)) :=
  ⟨.returned ⟨1, none⟩ (4 : Nat), rfl, rfl⟩

theorem clock_starts_from_default :
    Sysvar.sdkClockConfig.request.initial = some Sysvar.zeroClock := rfl

theorem rent_starts_from_default_without_integerizing_threshold :
    Sysvar.sdkRentConfig.request.initial = some ⟨3480, 0x4000000000000000, 50⟩ := rfl

theorem typed_rent_request_is_not_a_prefix_read :
    Sysvar.sdkRentConfig.request.kind = .typed .rent := rfl

end SolanalibTest.Specs.SolanaSysvar

@[expose] public section

namespace SolanalibTest.Specs.SolanaSysvar.V3Get

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.SolanaSysvar.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.SolanaSysvar.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

def build0 : Versioning.Build where
  package := "solana-sysvar"
  version := "3.1.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["3.1.1", "3.2.0"].all (fun version =>
      decide (((selectedProfile "typed-epoch-3.1.1").forBuild
        { build0 with version := version }).identities .epoch_schedule_EpochSchedule_get =
          [⟨"solana-sysvar", version, "solana_sysvar::Sysvar::get",
            "solana_sysvar::epoch_schedule::<impl solana_sysvar::Sysvar for \
              solana_epoch_schedule::EpochSchedule>::get"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"solana-sysvar", "3.1.1", "solana_sysvar::Sysvar::get",
            "solana_sysvar::epoch_schedule::<impl solana_sysvar::Sysvar for \
              solana_epoch_schedule::EpochSchedule>::get"⟩] : List Capabilities.RustIdentity).all
                (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
        build0).identities .epoch_schedule_EpochSchedule_get)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "typed-epoch-3.1.1").applicability .epoch_schedule_EpochSchedule_get).length
      = 1 ∧
    ["3.1.0", "4.0.0", "3.2.0-rc.1"].all (fun version =>
      (((selectedProfile "typed-epoch-3.1.1").forBuild { build0 with version := version
        }).identities
        .epoch_schedule_EpochSchedule_get).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "solana-sysvar-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with dependencies := [⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"solana-epoch-schedule", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-entrypoint", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "typed-epoch-3.1.1").forBuild build).identities
        .epoch_schedule_EpochSchedule_get).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaSysvar.V3Get
