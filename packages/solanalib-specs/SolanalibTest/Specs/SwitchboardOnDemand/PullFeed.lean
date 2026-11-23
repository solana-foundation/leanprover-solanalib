/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SwitchboardOnDemand

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SwitchboardOnDemand

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Oracle.Switchboard

theorem trailing_bytes_do_not_expand_view :
    prepare sampleArgs ⟨0, sampleBytes⟩ = .ok (.bytesRange 8 3200) := by
  simp [prepare, sampleBytes_length, sampleBytes_prefix,
    discriminator_length, payloadSize, sampleArgs, Layout.alignment]

theorem short_discriminator_precedes_alignment :
    prepare { sampleArgs with dataAddress := 4097 } ⟨0, [196]⟩ =
      .error .invalidDiscriminator := rfl

theorem bad_discriminator_precedes_short_payload :
    prepare sampleArgs ⟨0, List.replicate 8 0⟩ = .error .invalidDiscriminator := rfl

theorem short_payload_is_invalid_data :
    prepare sampleArgs ⟨0, discriminator ++ [1, 2]⟩ = .error .invalidData := rfl

theorem misaligned_payload_is_deserialization_error :
    prepare { sampleArgs with dataAddress := 4097 } ⟨0, sampleBytes⟩ =
      .error .accountDeserializeError := by
  simp [prepare, sampleBytes_length, sampleBytes_prefix,
    discriminator_length, payloadSize, sampleArgs, Layout.alignment]

theorem i128_alignment_difference_is_observable :
    prepare { sampleArgs with layout := .i128Align16 } ⟨0, sampleBytes⟩ =
      .error .accountDeserializeError := by
  simp [prepare, sampleBytes_length, sampleBytes_prefix,
    discriminator_length, payloadSize, sampleArgs, Layout.alignment]

theorem aligned_i128_16_payload_succeeds :
    prepare { sampleArgs with layout := .i128Align16, dataAddress := 4104 }
      ⟨0, sampleBytes⟩ = .ok (.bytesRange 8 3200) := by
  simp [prepare, sampleBytes_length, sampleBytes_prefix,
    discriminator_length, payloadSize, Layout.alignment]

/-- The mapped reference keeps the same cell, advances one generation, and
does not add a lease. The extra account remains untouched. -/
theorem success_retains_identity_and_cells :
    parse (sampleState sampleBytes) sampleArgs =
      some (.ok ⟨⟨0, 1⟩, .i128Align8⟩,
        (Borrow.transfer (sampleState sampleBytes) ⟨0, 0⟩ (.bytesRange 8 3200)).2) := by
  exact parse_prepared (sampleState sampleBytes) sampleArgs ⟨0, sampleBytes⟩
    (.bytesRange 8 3200) ⟨⟨0⟩, .shared, 0, .whole⟩ rfl
    trailing_bytes_do_not_expand_view rfl

theorem validation_error_releases_input_guard :
    parse (sampleState [196]) sampleArgs =
      some (.error .invalidDiscriminator, (Borrow.release (sampleState [196]) ⟨0, 0⟩).2) := rfl

theorem failed_parse_releases_lease :
    ((Borrow.release (sampleState [196]) ⟨0, 0⟩).2).lease ⟨0⟩ = .free := rfl

theorem mapped_input_generation_is_unusable :
    (Borrow.transfer (sampleState sampleBytes) ⟨0, 0⟩ (.bytesRange 8 3200)).2.resolve
      ⟨0, 0⟩ = none := rfl

theorem mapped_reference_reads_current_payload :
    read (Borrow.transfer (sampleState sampleBytes) ⟨0, 0⟩ (.bytesRange 8 3200)).2
      ⟨0, 1⟩ = some ⟨8, List.replicate 3200 0⟩ := by
  simp [Oracle.Switchboard.read, sampleState, freeState, sampleBytes_length,
    Borrow.current, Borrow.transfer, Borrow.acquire, Borrow.State.issue,
    Borrow.State.resolve, Borrow.State.lookupSlot, Borrow.State.lookupCell,
    Borrow.State.exclusiveCount, Borrow.State.sharedCount, Borrow.State.count,
    Borrow.Policy.refCell, AccountInfo.projectBytes, Except.toOption, -List.reduceReplicate]
  exact sampleBytes_payload

open Solanalib.Specs.SwitchboardOnDemand.on_demand.accounts.pull_feed.PullFeedAccountData

/-- A nonphysical natural-number address remains an admitted mathematical
input. Its aligned payload and actual guard transfer are unchanged. -/
theorem abstract_address_retains_exact_parse :
    let args := { sampleArgs with dataAddress := 2^64 }
    parse_contract.requires (sampleState sampleBytes) args ∧
      parse_run (sampleState sampleBytes) args
        (.returned (.ok ⟨⟨0, 1⟩, .i128Align8⟩)
          (Borrow.transfer (sampleState sampleBytes) ⟨0, 0⟩ (.bytesRange 8 3200)).2) := by
  refine ⟨⟨sampleState_valid _, _, ⟨0, sampleBytes⟩, rfl, rfl⟩, ?_⟩
  apply parse_prepared _ _ ⟨0, sampleBytes⟩ (.bytesRange 8 3200)
    ⟨⟨0⟩, .shared, 0, .whole⟩ rfl _ rfl
  simp [prepare, sampleBytes_length, sampleBytes_prefix,
    discriminator_length, payloadSize, sampleArgs, Layout.alignment]

/-- Shared mode and positive physical address are separate source bindings.
The mathematical parser still releases this exclusive input on validation error. -/
theorem other_mode_retains_error_and_retirement :
    let state := (Borrow.acquire (freeState [196]) ⟨0⟩ .exclusive AccountInfo.View.whole).2
    let args := { sampleArgs with dataAddress := 0 }
    parse_contract.requires state args ∧
      parse_contract.post state args
        (.returned (.error .invalidDiscriminator) (Borrow.release state ⟨0, 0⟩).2) := by
  have ready : Ready
      (Borrow.acquire (freeState [196]) ⟨0⟩ .exclusive AccountInfo.View.whole).2
      { sampleArgs with dataAddress := 0 } :=
    ⟨Borrow.acquire_valid (Borrow.State.valid_empty_slots _) _ _ _,
      ⟨⟨0⟩, .exclusive, 0, .whole⟩, ⟨0, [196]⟩, rfl, rfl⟩
  exact ⟨ready, parse_reference _ _ _ ready rfl⟩

/-- A consumed token is still outside mathematical admission. -/
theorem consumed_input_is_not_ready :
    ¬ Ready (Borrow.release (sampleState [196]) ⟨0, 0⟩).2 sampleArgs := by
  rintro ⟨_, slot, _, live, _⟩
  have dead : (Borrow.release (sampleState [196]) ⟨0, 0⟩).2.resolve sampleArgs.guard = none := rfl
  rw [dead] at live
  cases live

namespace Applicability

open Solanalib.Specs.SwitchboardOnDemand.Capabilities

def registryBuild : Versioning.Build where
  package := "switchboard-on-demand"
  version := "0.12.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def gitBuild : Versioning.Build :=
  { registryBuild with source :=
    ⟨"git", "https://github.com/switchboard-xyz/switchboard-sdk",
      "f75b1ef63e10eda35d046b1838810ec2935d7f39"⟩ }

def parserIdentity (version : String) : Solanalib.Contracts.Model.Capabilities.RustIdentity :=
  ⟨"switchboard-on-demand", version,
    "switchboard_on_demand::on_demand::accounts::pull_feed::PullFeedAccountData::parse",
    "switchboard_on_demand::on_demand::accounts::pull_feed::PullFeedAccountData::parse"⟩

/-- Both origins select the existing complete parser identity at the actual version. -/
theorem reviewed_origins_select_the_actual_parser :
    (catalog.forBuild registryBuild).identities
      .on_demand_accounts_pull_feed_PullFeedAccountData_parse =
      [parserIdentity "0.12.1"] ∧
    (catalog.forBuild gitBuild).identities .on_demand_accounts_pull_feed_PullFeedAccountData_parse =
      [parserIdentity "0.12.1"] := by decide +kernel

def compatibleVersions : List String :=
  ["0.7.5", "0.8.1", "0.9.6", "0.10.9", "0.11.4", "0.12.2", "0.13.1"]

/-- Each existing registry interval retains the actual compatible version. -/
theorem registry_intervals_keep_the_actual_identity :
    compatibleVersions.map (fun version =>
      (catalog.forBuild { registryBuild with version := version }).identities
        .on_demand_accounts_pull_feed_PullFeedAccountData_parse) =
      compatibleVersions.map (fun version => [parserIdentity version]) := by decide +kernel

/-- The exact Git registration does not inherit any registry interval. -/
theorem git_version_changes_are_rejected :
    ["0.12.0", "0.12.2", "0.13.0", "0.12.1-rc.1", "0.12.1+probe"].all (fun version =>
      ((catalog.forBuild { gitBuild with version := version }).identities
        .on_demand_accounts_pull_feed_PullFeedAccountData_parse).isEmpty) = true := by
  decide +kernel

theorem changed_git_source_is_rejected :
    [{ gitBuild.source with revision := "0000000000000000000000000000000000000000" },
      { gitBuild.source with url := "https://example.invalid/switchboard-sdk" }].all (fun source =>
        ((catalog.forBuild { gitBuild with source := source }).identities
          .on_demand_accounts_pull_feed_PullFeedAccountData_parse).isEmpty) = true := by
  decide +kernel

/-- Preserve the older exclusions, the two release holes and the exclusive upper bound. -/
theorem registry_exceptions_and_prereleases_are_rejected :
    ["0.6.0", "0.11.0", "0.12.0", "0.14.0", "0.12.2-rc.1"].all (fun version =>
      ((catalog.forBuild { registryBuild with version := version }).identities
        .on_demand_accounts_pull_feed_PullFeedAccountData_parse).isEmpty) = true := by
  decide +kernel

end Applicability

end SolanalibTest.Specs.SwitchboardOnDemand
