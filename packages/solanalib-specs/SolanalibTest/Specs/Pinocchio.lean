/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.Pinocchio.Rent
public import SolanalibTest.Specs.Pinocchio.RentAccount
public import SolanalibTest.Specs.Pinocchio.Instructions
public import SolanalibTest.Specs.Pinocchio.InstructionsGeneric
public import SolanalibTest.Specs.Pinocchio.Values
public import SolanalibTest.Specs.Pinocchio.Guards
public import SolanalibTest.Specs.Pinocchio.Accounts
public import Solanalib.Specs.Pinocchio.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.Pinocchio.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def cpi_invoke_signed_uncheckedBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "ab\
    ort"⟩]
  features := some []
  targetFeatures := some []
  dependencies := []

def cpi_invoke_signed_uncheckedCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (cpi_invoke_signed_uncheckedBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ cpi_invoke_signed_uncheckedBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (cpi_invoke_signed_uncheckedBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ cpi_invoke_signed_uncheckedBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ cpi_invoke_signed_uncheckedBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ cpi_invoke_signed_uncheckedBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ cpi_invoke_signed_uncheckedBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ cpi_invoke_signed_uncheckedBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ cpi_invoke_signed_uncheckedBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian",
    "little"⟩, ⟨"panic", "abort"⟩] }, false),
  -- wrong-target-os; unsupported
  ({ cpi_invoke_signed_uncheckedBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "6\
    4"⟩,
    ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ cpi_invoke_signed_uncheckedBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩,
    ⟨"panic", "abort"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ cpi_invoke_signed_uncheckedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "linux"⟩,
    ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ cpi_invoke_signed_uncheckedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"panic", "abort"⟩] }, false),
  -- wrong-target-endian; unsupported
  ({ cpi_invoke_signed_uncheckedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "linux"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-panic; unresolved
  ({ cpi_invoke_signed_uncheckedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- wrong-target-panic; unsupported
  ({ cpi_invoke_signed_uncheckedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "little"⟩, ⟨"panic", "linux"⟩] }, false),
  -- missing-target_features; unresolved
  ({ cpi_invoke_signed_uncheckedBuild with targetFeatures := none }, false),
  -- wrong-target_features; unsupported
  ({ cpi_invoke_signed_uncheckedBuild with targetFeatures := some ["static-syscalls"] }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ cpi_invoke_signed_uncheckedBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem cpi_invoke_signed_unchecked_profile_controls :
    cpi_invoke_signed_uncheckedCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .cpi_invoke_signed_unchecked).any
        (fun profile => ["pinocchio-0.9.2-unchecked-cpi"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem cpi_invoke_signed_unchecked_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { cpi_invoke_signed_uncheckedBuild with version := version }).identities
          .cpi_invoke_signed_unchecked).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::cpi::invoke_signed_unchecked",
          "pinocchio::cpi::invoke_signed_unchecked"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def entrypoint_deserializeBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def entrypoint_deserializeCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (entrypoint_deserializeBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ entrypoint_deserializeBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (entrypoint_deserializeBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ entrypoint_deserializeBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ entrypoint_deserializeBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ entrypoint_deserializeBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ entrypoint_deserializeBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ entrypoint_deserializeBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ entrypoint_deserializeBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem entrypoint_deserialize_profile_controls :
    entrypoint_deserializeCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability .entrypoint_deserialize).any
        (fun profile => ["entry-deserialize-0-9-2"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem entrypoint_deserialize_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { entrypoint_deserializeBuild with version := version }).identities
          .entrypoint_deserialize).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::entrypoint::deserialize",
          "pinocchio::entrypoint::deserialize"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def syscalls_sol_invoke_signed_cBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "ab\
    ort"⟩]
  features := some []
  targetFeatures := some []
  dependencies := []

def syscalls_sol_invoke_signed_cCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (syscalls_sol_invoke_signed_cBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ syscalls_sol_invoke_signed_cBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (syscalls_sol_invoke_signed_cBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ syscalls_sol_invoke_signed_cBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ syscalls_sol_invoke_signed_cBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ syscalls_sol_invoke_signed_cBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ syscalls_sol_invoke_signed_cBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ syscalls_sol_invoke_signed_cBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ syscalls_sol_invoke_signed_cBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian",
    "little"⟩, ⟨"panic", "abort"⟩] }, false),
  -- wrong-target-os; unsupported
  ({ syscalls_sol_invoke_signed_cBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ syscalls_sol_invoke_signed_cBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩,
    ⟨"panic", "abort"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ syscalls_sol_invoke_signed_cBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "linux"⟩, ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ syscalls_sol_invoke_signed_cBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"panic", "abort"⟩] }, false),
  -- wrong-target-endian; unsupported
  ({ syscalls_sol_invoke_signed_cBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "linux"⟩, ⟨"panic", "abort"⟩] }, false),
  -- missing-target-panic; unresolved
  ({ syscalls_sol_invoke_signed_cBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- wrong-target-panic; unsupported
  ({ syscalls_sol_invoke_signed_cBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "little"⟩, ⟨"panic", "linux"⟩] }, false),
  -- missing-target_features; unresolved
  ({ syscalls_sol_invoke_signed_cBuild with targetFeatures := none }, false),
  -- wrong-target_features; unsupported
  ({ syscalls_sol_invoke_signed_cBuild with targetFeatures := some ["static-syscalls"] }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ syscalls_sol_invoke_signed_cBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem syscalls_sol_invoke_signed_c_profile_controls :
    syscalls_sol_invoke_signed_cCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .syscalls_sol_invoke_signed_c).any
        (fun profile => ["raw-cpi-c-pinocchio-0.9.2"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem syscalls_sol_invoke_signed_c_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { syscalls_sol_invoke_signed_cBuild with version := version }).identities
          .syscalls_sol_invoke_signed_c).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::syscalls::sol_invoke_signed_c",
          "pinocchio::syscalls::sol_invoke_signed_c"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.Pinocchio.Pr575Compatibility
