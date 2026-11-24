/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaProgram.Log
public import Solanalib.Specs.SolanaProgram.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaProgram

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem nested_fields_and_empty_field_reach_sink :
    Solanalib.Specs.SolanaProgram.log.sol_log_data_run
      Solanalib.Specs.SolanaProgram.log.sol_log_data_sample
      [] [[8], [], [9, 10]] (.returned () [.data [[8], [], [9, 10]]]) := rfl

def abortSink (_ : Nat) (_ : Log.Event) : Outcome Nat Unit String String := .terminated "lo\
  g"

theorem terminal_sink_outcome_is_preserved :
    Log.dataCall .solana (Callback.ofFunction abortSink) 4 [[8], [9]]
      (.terminated "log") := rfl

theorem host_stub_is_selected_explicitly :
    Log.dataCall .hostStub (Callback.ofFunction Log.appendEvent) [] [[8], [9]]
      (.returned () [.stubData [[8], [9]]]) := rfl

end SolanalibTest.Specs.SolanaProgram

namespace SolanalibTest.Specs.SolanaProgram.LogCompatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (Key catalog)

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal Rust identities are independent of generated profile selection. -/
def referenceRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.log_sol_log, {
    package := "solana-program", version := "1.15.2", source := registry },
      [("solana_program::log::sol_log", "solana_program::log::sol_log")]),
    (.log_sol_log, {
      package := "solana-program", version := "1.18.26", source := registry },
      [("solana_program::log::sol_log", "solana_program::log::sol_log")])]

/-- These uninspected patch versions exercise compatibility assumptions only. -/
def compatibleRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.log_sol_log, {
    package := "solana-program", version := "1.15.3", source := registry },
      [("solana_program::log::sol_log", "solana_program::log::sol_log")]),
    (.log_sol_log, {
      package := "solana-program", version := "1.18.27", source := registry },
      [("solana_program::log::sol_log", "solana_program::log::sol_log")])]

theorem exact_reference_identities :
    referenceRows.length = 2 ∧ referenceRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem compatible_actual_version_identities :
    compatibleRows.length = 2 ∧ compatibleRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem build_metadata_keeps_actual_version :
    compatibleRows.all (fun row =>
      let build := { row.2.1 with version := row.2.1.version ++ "+review" }
      decide ((catalog.forBuild build).identities row.1 =
        row.2.2.map (fun names => ⟨build.package, build.version, names.1, names.2⟩))) = true := by
  decide +kernel

def rejectedVersions : List (Key × Versioning.Build × List String) :=
  [(.log_sol_log, {
    package := "solana-program", version := "1.15.2", source := registry },
    ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.log_sol_log, {
      package := "solana-program", version := "1.18.26", source := registry },
      ["1.15.1", "2.0.0", "1.15.2-rc.1"])]

theorem bounds_and_prereleases_rejected :
    rejectedVersions.all (fun row => row.2.2.all (fun version =>
      ((catalog.forBuild { row.2.1 with version := version }).identities row.1).isEmpty)) = true :=
        by
  decide +kernel

theorem defining_package_and_fork_rejected :
    (referenceRows ++ compatibleRows).all (fun row =>
      ((catalog.forBuild { row.2.1 with package := "wrong-defining-package" }).identities
        row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with source :=
        ⟨"git", "https://example.invalid/source-fork", "01234567890123456789012345678901234\
          56789"⟩
        }).identities row.1).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaProgram.LogCompatibility

/- Per-operation compatibility selection. Synthetic versions carry no native or ABI credit. -/
namespace SolanalibTest.Specs.SolanaProgram.Log.LegacyCompatibility

@[expose] public section

set_option autoImplicit false

namespace Logging

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "solana-program"
  version := "1.15.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "1.15.3" }

def identityCases (version : String) : List (Solanalib.Specs.SolanaProgram.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.log_sol_log_compute_units, [⟨"solana-program", version,
      "solana_program::log::sol_log_compute_units", "solana_program::log::sol_log_compute_u\
        nits"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["1.15.1", "1.16.0", "1.15.3-rc.1"].all (fun version =>
      (identityCases version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with version := version }).identities
          entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_origin_rejected :
    (identityCases compatibleBuild.version).all (fun entry =>
      ((catalog.forBuild { compatibleBuild with source :=
        ⟨"git", "https://example.org/source-fork", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
          a"⟩ }).identities entry.1).isEmpty) = true := by decide +kernel

end Logging

end

end SolanalibTest.Specs.SolanaProgram.Log.LegacyCompatibility
