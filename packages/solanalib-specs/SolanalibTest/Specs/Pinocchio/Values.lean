/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Pinocchio.Instruction
public import Solanalib.Specs.Pinocchio.Pubkey
public import Solanalib.Specs.Pinocchio.Get
public import Solanalib.Specs.Pinocchio.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Pinocchio.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem constructors_retain_reference_and_privileges :
    Solanalib.Specs.Pinocchio.instruction.AccountMeta.readonly_run Nat () (9 : Nat) (.returned ⟨9,
      false, false⟩ ()) ∧
    Solanalib.Specs.Pinocchio.instruction.AccountMeta.readonly_signer_run Nat () (9 : Nat)
      (.returned ⟨9, true, false⟩ ()) ∧
    Solanalib.Specs.Pinocchio.instruction.AccountMeta.writable_run Nat () (9 : Nat) (.returned ⟨9,
      false, true⟩ ()) ∧
    Solanalib.Specs.Pinocchio.instruction.AccountMeta.writable_signer_run Nat () (9 : Nat)
      (.returned ⟨9, true, true⟩ ()) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem seed_constructor_has_no_pda_length_check :
    Solanalib.Specs.Pinocchio.instruction.Seed.from_array_run ⟨Nat, 100⟩ () (7 : Nat) (.returned
      ⟨7, 100⟩ ()) ∧
    Solanalib.Specs.Pinocchio.instruction.Seed.from_array_run ⟨Nat, 0⟩ () (7 : Nat) (.returned ⟨7,
      0⟩ ()) := ⟨rfl, rfl⟩

def differentKey : Solanalib.Runtime.Pubkey := ⟨1 :: List.replicate 31 0, rfl⟩
theorem pubkeys_compare_all_bytes :
    (Solanalib.Specs.Pinocchio.pubkey.pubkey_eq_run () (.zero, .zero)).1 = true ∧
    (Solanalib.Specs.Pinocchio.pubkey.pubkey_eq_run () (.zero, differentKey)).1 = false := by decide

theorem clock_all_nonzero_statuses_are_unsupported :
    Solanalib.Specs.Pinocchio.sysvars.clock.Clock.dedicatedConfig.error 1 = some .unsupportedSysvar
      ∧
    Solanalib.Specs.Pinocchio.sysvars.clock.Clock.dedicatedConfig.error 2 = some .unsupportedSysvar
      ∧
    Solanalib.Specs.Pinocchio.sysvars.clock.Clock.dedicatedConfig.error 18446744073709551615 = some
      .unsupportedSysvar := by decide

/-- The same provider records the actual request and leaves an error destination
uninitialized. Its state change survives the status conversion of either syscall. -/
def errorClockProvider : Sysvar.GetterIndex Sysvar.Clock where
  State := List (Sysvar.GetterTarget × Sysvar.ReadRequest Sysvar.Clock)
  Unwind := String
  Terminal := String
  target := .solana
  read := Callback.ofFunction fun before request =>
    .returned ⟨1, none⟩ (before ++ [request])

def dedicatedClockRead : Sysvar.GetterTarget × Sysvar.ReadRequest Sysvar.Clock :=
  (.solana, ⟨.typed .clock, none⟩)

def genericClockRead : Sysvar.GetterTarget × Sysvar.ReadRequest Sysvar.Clock :=
  (.solana, ⟨.generic Solanalib.Runtime.Ids.sysvarClock 0 40, none⟩)

theorem dedicated_clock_error_retains_typed_request :
    (Solanalib.Specs.Pinocchio.sysvars.clock.Clock.get_dedicated_contract.contract
      errorClockProvider).post
      [] () (.returned (.error .unsupportedSysvar) [dedicatedClockRead]) := by
  apply Solanalib.Specs.Pinocchio.sysvars.clock.Clock.get_dedicated_reference
  · intro reply after called successful
    cases called
    cases successful
  · exact ⟨.returned ⟨1, none⟩ [dedicatedClockRead], rfl, rfl⟩

theorem generic_clock_error_retains_byte_request :
    ((Sysvar.getterFamily Sysvar.pinClockConfig).contract errorClockProvider).post
      [] () (.returned (.error .invalidArgument) [genericClockRead]) := by
  apply Sysvar.getter_reference
  · intro reply after called successful
    cases called
    cases successful
  · exact ⟨.returned ⟨1, none⟩ [genericClockRead], rfl, rfl⟩

theorem generic_clock_rejects_dedicated_outcome :
    ¬ ((Sysvar.getterFamily Sysvar.pinClockConfig).contract errorClockProvider).post
      [] () (.returned (.error .unsupportedSysvar) [dedicatedClockRead]) := by
  rintro ⟨exit, called, forwarded⟩
  cases called
  cases forwarded

end SolanalibTest.Specs.Pinocchio.Values

namespace SolanalibTest.Specs.Pinocchio.Values.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_AccountMeta_readonlyBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def instruction_AccountMeta_readonlyCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (instruction_AccountMeta_readonlyBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ instruction_AccountMeta_readonlyBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (instruction_AccountMeta_readonlyBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_AccountMeta_readonlyBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_AccountMeta_readonlyBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_AccountMeta_readonlyBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_AccountMeta_readonlyBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_AccountMeta_readonlyBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ instruction_AccountMeta_readonlyBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_AccountMeta_readonly_profile_controls :
    instruction_AccountMeta_readonlyCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .instruction_AccountMeta_readonly).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_AccountMeta_readonly_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { instruction_AccountMeta_readonlyBuild with version := version }).identities
          .instruction_AccountMeta_readonly).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::instruction::AccountMeta::<'a>::readonly",
          "pinocchio::instruction::AccountMeta::<'a>::readonly"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_AccountMeta_readonly_signerBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def instruction_AccountMeta_readonly_signerCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (instruction_AccountMeta_readonly_signerBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ instruction_AccountMeta_readonly_signerBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (instruction_AccountMeta_readonly_signerBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_AccountMeta_readonly_signerBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_AccountMeta_readonly_signerBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_AccountMeta_readonly_signerBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_AccountMeta_readonly_signerBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_AccountMeta_readonly_signerBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ instruction_AccountMeta_readonly_signerBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_AccountMeta_readonly_signer_profile_controls :
    instruction_AccountMeta_readonly_signerCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .instruction_AccountMeta_readonly_signer).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_AccountMeta_readonly_signer_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { instruction_AccountMeta_readonly_signerBuild with version := version }).identities
          .instruction_AccountMeta_readonly_signer).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::instruction::AccountMeta::<'a>::readonly_signer",
          "pinocchio::instruction::AccountMeta::<'a>::readonly_signer"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_AccountMeta_writableBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def instruction_AccountMeta_writableCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (instruction_AccountMeta_writableBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ instruction_AccountMeta_writableBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (instruction_AccountMeta_writableBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_AccountMeta_writableBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_AccountMeta_writableBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_AccountMeta_writableBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_AccountMeta_writableBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_AccountMeta_writableBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ instruction_AccountMeta_writableBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_AccountMeta_writable_profile_controls :
    instruction_AccountMeta_writableCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .instruction_AccountMeta_writable).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_AccountMeta_writable_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { instruction_AccountMeta_writableBuild with version := version }).identities
          .instruction_AccountMeta_writable).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::instruction::AccountMeta::<'a>::writable",
          "pinocchio::instruction::AccountMeta::<'a>::writable"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_AccountMeta_writable_signerBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def instruction_AccountMeta_writable_signerCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (instruction_AccountMeta_writable_signerBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ instruction_AccountMeta_writable_signerBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (instruction_AccountMeta_writable_signerBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_AccountMeta_writable_signerBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_AccountMeta_writable_signerBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_AccountMeta_writable_signerBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_AccountMeta_writable_signerBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_AccountMeta_writable_signerBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ instruction_AccountMeta_writable_signerBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_AccountMeta_writable_signer_profile_controls :
    instruction_AccountMeta_writable_signerCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .instruction_AccountMeta_writable_signer).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_AccountMeta_writable_signer_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { instruction_AccountMeta_writable_signerBuild with version := version }).identities
          .instruction_AccountMeta_writable_signer).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::instruction::AccountMeta::<'a>::writable_signer",
          "pinocchio::instruction::AccountMeta::<'a>::writable_signer"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_Seed_from_arrayBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def instruction_Seed_from_arrayCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (instruction_Seed_from_arrayBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ instruction_Seed_from_arrayBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (instruction_Seed_from_arrayBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_Seed_from_arrayBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_Seed_from_arrayBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_Seed_from_arrayBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_Seed_from_arrayBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_Seed_from_arrayBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ instruction_Seed_from_arrayBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_Seed_from_array_profile_controls :
    instruction_Seed_from_arrayCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .instruction_Seed_from_array).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_Seed_from_array_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { instruction_Seed_from_arrayBuild with version := version }).identities
          .instruction_Seed_from_array).eraseDups ==
        [⟨"pinocchio", version, "core::convert::From::from",
          "<pinocchio::instruction::Seed<'a> as core::convert::From<&'a [u8; SIZE]>>::from"⟩])) =
          true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def pubkey_pubkey_eqBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def pubkey_pubkey_eqCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (pubkey_pubkey_eqBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ pubkey_pubkey_eqBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (pubkey_pubkey_eqBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ pubkey_pubkey_eqBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ pubkey_pubkey_eqBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ pubkey_pubkey_eqBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ pubkey_pubkey_eqBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ pubkey_pubkey_eqBuild with source := ⟨"git", "https://example.invalid/review-fork", "b\
    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ pubkey_pubkey_eqBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem pubkey_pubkey_eq_profile_controls :
    pubkey_pubkey_eqCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability .pubkey_pubkey_eq).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem pubkey_pubkey_eq_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { pubkey_pubkey_eqBuild with version := version }).identities .pubkey_pubkey_eq).eraseDups
          ==
        [⟨"pinocchio", version, "pinocchio::pubkey::pubkey_eq", "pinocchio::pubkey::pubkey_\
          eq"⟩]))
          = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def syscalls_sol_get_clock_sysvarBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩]
  features := some []
  targetFeatures := some []
  dependencies := []

def syscalls_sol_get_clock_sysvarCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (syscalls_sol_get_clock_sysvarBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ syscalls_sol_get_clock_sysvarBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (syscalls_sol_get_clock_sysvarBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ syscalls_sol_get_clock_sysvarBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ syscalls_sol_get_clock_sysvarBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ syscalls_sol_get_clock_sysvarBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ syscalls_sol_get_clock_sysvarBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ syscalls_sol_get_clock_sysvarBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-pointer_width; unresolved
  ({ syscalls_sol_get_clock_sysvarBuild with target := [] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ syscalls_sol_get_clock_sysvarBuild with target := [⟨"pointer_width", "linux"⟩] }, false),
  -- missing-target_features; unresolved
  ({ syscalls_sol_get_clock_sysvarBuild with targetFeatures := none }, false),
  -- wrong-target_features; unsupported
  ({ syscalls_sol_get_clock_sysvarBuild with targetFeatures := some ["static-syscalls"] }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ syscalls_sol_get_clock_sysvarBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem syscalls_sol_get_clock_sysvar_profile_controls :
    syscalls_sol_get_clock_sysvarCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .syscalls_sol_get_clock_sysvar).any
        (fun profile => ["raw-runtime-pinocchio-0.9.2"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem syscalls_sol_get_clock_sysvar_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { syscalls_sol_get_clock_sysvarBuild with version := version }).identities
          .syscalls_sol_get_clock_sysvar).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::syscalls::sol_get_clock_sysvar",
          "pinocchio::syscalls::sol_get_clock_sysvar"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def sysvars_clock_Clock_get_dedicatedBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩]
  features := some []
  targetFeatures := some []
  dependencies := []

def sysvars_clock_Clock_get_dedicatedCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (sysvars_clock_Clock_get_dedicatedBuild, true),
  -- lower; eligible
  (sysvars_clock_Clock_get_dedicatedBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ sysvars_clock_Clock_get_dedicatedBuild with version := "0.9.2+selector.probe" }, true),
  -- exclusive-upper; unsupported
  ({ sysvars_clock_Clock_get_dedicatedBuild with version := "0.9.3" }, false),
  -- unlisted-prerelease; unsupported
  ({ sysvars_clock_Clock_get_dedicatedBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ sysvars_clock_Clock_get_dedicatedBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ sysvars_clock_Clock_get_dedicatedBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ sysvars_clock_Clock_get_dedicatedBuild with target := [] }, false),
  -- wrong-target-os; unsupported
  ({ sysvars_clock_Clock_get_dedicatedBuild with target := [⟨"os", "linux"⟩] }, false),
  -- dedicated-boundary-0.9.2; eligible
  (sysvars_clock_Clock_get_dedicatedBuild, true),
  -- dedicated-boundary-0.9.3; unsupported
  ({ sysvars_clock_Clock_get_dedicatedBuild with version := "0.9.3" }, false),
  -- dedicated-boundary-0.10.2; unsupported
  ({ sysvars_clock_Clock_get_dedicatedBuild with version := "0.10.2" }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ sysvars_clock_Clock_get_dedicatedBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem sysvars_clock_Clock_get_dedicated_profile_controls :
    sysvars_clock_Clock_get_dedicatedCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .sysvars_clock_Clock_get_dedicated).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem sysvars_clock_Clock_get_dedicated_callable_identities :
    ["0.9.2", "0.9.2+selector.probe"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { sysvars_clock_Clock_get_dedicatedBuild with version := version }).identities
          .sysvars_clock_Clock_get_dedicated).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::sysvars::Sysvar::get",
          "<pinocchio::sysvars::clock::Clock as pinocchio::sysvars::Sysvar>::get"⟩])) = true := by
  decide +kernel

/-- Version 0.9.2 selects the dedicated typed request. -/
theorem dedicated_clock_092_admitted :
    (Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
      sysvars_clock_Clock_get_dedicatedBuild).identities
      .sysvars_clock_Clock_get_dedicated ≠ [] := by
  decide +kernel

/-- Version 0.9.3 changes the syscall request and is outside this complete family. -/
theorem dedicated_clock_093_rejected :
    (Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
      { sysvars_clock_Clock_get_dedicatedBuild with version := "0.9.3" }).identities
      .sysvars_clock_Clock_get_dedicated = [] := by
  decide +kernel

/-- The inherited generic profile retains its distinct request and status converter. -/
theorem generic_clock_profile_remains_separate :
    (Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
      { sysvars_clock_Clock_get_dedicatedBuild with version := "0.9.2" }).identities
      .sysvars_clock_Clock_get = [] ∧
    (Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
      { sysvars_clock_Clock_get_dedicatedBuild with version := "0.9.3" }).identities
      .sysvars_clock_Clock_get = [] ∧
    (Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
      { sysvars_clock_Clock_get_dedicatedBuild with version := "0.10.2" }).identities
      .sysvars_clock_Clock_get_dedicated = [] ∧
    (Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
      { sysvars_clock_Clock_get_dedicatedBuild with version := "0.10.2" }).identities
      .sysvars_clock_Clock_get ≠ [] := by
  decide +kernel

end SolanalibTest.Specs.Pinocchio.Values.Pr575Compatibility
