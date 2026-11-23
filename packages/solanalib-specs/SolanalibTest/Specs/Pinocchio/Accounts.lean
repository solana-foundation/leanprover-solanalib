/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Pinocchio.AccountInfo
public import Solanalib.Specs.Pinocchio.Guard
public import Solanalib.Specs.Pinocchio.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Pinocchio.Accounts

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.PinocchioAccount
open Solanalib.Specs.Pinocchio.account_info.AccountInfo

theorem noncanonical_true_flags :
    (is_signer_run sampleState sampleHandle).1 = true ∧
    (is_writable_run sampleState sampleHandle).1 = true := by repeat' constructor <;> first | rfl |
      decide

theorem field_references_retain_alias :
    (key_run sampleState sampleHandle).1 = keyRef sampleHandle ∧
    (owner_run sampleState sampleHandle.alias).1 = ownerRef sampleHandle := by repeat' constructor
      <;> first | rfl | decide

theorem owner_compares_current_field :
    (is_owned_by_run sampleState (sampleHandle, sampleInput.owner)).1 = true := by repeat'
      constructor <;> first | rfl | decide

theorem scalar_getters_ignore_exclusive_data_lease :
    (lamports_run sampleGuardState sampleHandle).1 = 40 ∧
    (data_len_run sampleGuardState sampleHandle).1 = 3 := by repeat' constructor <;> first | rfl |
      decide

def shared (count : Nat) : State :=
  count.rec sampleState (fun _ state => (try_borrow_data_run state sampleHandle).2)

theorem exactly_seven_shared_data_leases :
    borrowByte (shared 7) sampleHandle = 248 ∧
    (try_borrow_data_run (shared 7) sampleHandle).1 = .error .accountBorrowFailed ∧
    (try_borrow_data_run (shared 7) sampleHandle).2 = shared 7 := by
  have full : available (shared 7) sampleHandle .data .shared = false := by decide
  exact ⟨by decide, by simp [try_borrow_data_run, acquire, full],
    by simp [try_borrow_data_run, acquire, full]⟩

theorem data_exclusive_updates_only_low_nibble :
    borrowByte sampleGuardState sampleHandle = 247 ∧
    (try_borrow_data_run sampleGuardState sampleHandle.alias).1 = .error .accountBorrowFailed := by
      repeat' constructor <;> first | rfl | decide

theorem field_leases_are_independent :
    (try_borrow_mut_lamports_run sampleGuardState sampleHandle).1 = .ok ⟨1, 0⟩ ∧
    borrowByte (try_borrow_mut_lamports_run sampleGuardState sampleHandle).2 sampleHandle = 119 :=
      by repeat' constructor <;> first | rfl | decide

theorem regrow_zeroes_retained_bytes :
    ((resize (resize sampleState (sampleHandle, 1)).2 (sampleHandle, 4)).2.data
      sampleHandle).backing =
      [10, 0, 0, 0, 91] ∧
    ((resize (resize sampleState (sampleHandle, 1)).2 (sampleHandle, 4)).2.data
      sampleHandle).resizeDelta = 1 := by repeat' constructor <;> first | rfl | decide

/-- The zeroing provider records the state it receives before terminating. -/
def observingZero : ResizeIndex where
  Aux := Unit
  Terminal := Nat × Int × Solanalib.Runtime.Bytes × ZeroRequest
  zero := Callback.ofFunction fun before request => .terminated
    ((before.1.data request.account).dataLen, (before.1.data request.account).resizeDelta,
      (before.1.data request.account).backing, request)
  zeroCorrect := by intro before request after called; cases called

/-- Length and signed delta are committed before growth reaches sol_memset_. -/
theorem resize_terminal_observes_committed_header :
    resize_run observingZero (sampleState, ()) (sampleHandle, 4)
      (.terminated (4, 1, [10, 20, 30, 90, 91], ⟨sampleHandle, 3, 1⟩)) :=
  resize_terminates observingZero (sampleState, ()) (sampleHandle, 4)
    (by decide) _ rfl

/-- A borrow conflict precedes the otherwise failing i32 length conversion. -/
theorem resize_borrow_failure_skips_zeroing :
    resize_run observingZero (sampleGuardState, ()) (sampleHandle, 2^31)
      (.returned (.error .accountBorrowFailed) (sampleGuardState, ())) := by
  unfold resize_run resizeCallRun resizeRunAt
  simp only [show resizeCallsZero sampleGuardState (sampleHandle, 2^31) = false from by decide,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Equal length returns without entering even a terminal zeroing provider. -/
theorem unchanged_resize_skips_zeroing :
    resize_run observingZero (sampleState, ()) (sampleHandle, 3)
      (.returned (.ok ()) (sampleState, ())) := by
  unfold resize_run resizeCallRun resizeRunAt
  simp only [show resizeCallsZero sampleState (sampleHandle, 3) = false from by decide,
    Bool.false_eq_true, ↓reduceIte]
  rfl

end SolanalibTest.Specs.Pinocchio.Accounts

namespace SolanalibTest.Specs.Pinocchio.Accounts.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_AccountInfo_data_lenBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_AccountInfo_data_lenCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_AccountInfo_data_lenBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_AccountInfo_data_lenBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_AccountInfo_data_lenBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_AccountInfo_data_lenBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_AccountInfo_data_lenBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_AccountInfo_data_lenBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_AccountInfo_data_lenBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_AccountInfo_data_lenBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_AccountInfo_data_lenBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_AccountInfo_data_len_profile_controls :
    account_info_AccountInfo_data_lenCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_AccountInfo_data_len).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_AccountInfo_data_len_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_AccountInfo_data_lenBuild with version := version }).identities
          .account_info_AccountInfo_data_len).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::AccountInfo::data_len",
          "pinocchio::account_info::AccountInfo::data_len"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_AccountInfo_is_owned_byBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_AccountInfo_is_owned_byCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_AccountInfo_is_owned_byBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_AccountInfo_is_owned_byBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_AccountInfo_is_owned_byBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_AccountInfo_is_owned_byBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_AccountInfo_is_owned_byBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_AccountInfo_is_owned_byBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_AccountInfo_is_owned_byBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_AccountInfo_is_owned_byBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_AccountInfo_is_owned_byBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_AccountInfo_is_owned_by_profile_controls :
    account_info_AccountInfo_is_owned_byCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_AccountInfo_is_owned_by).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_AccountInfo_is_owned_by_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_AccountInfo_is_owned_byBuild with version := version }).identities
          .account_info_AccountInfo_is_owned_by).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::AccountInfo::is_owned_by",
          "pinocchio::account_info::AccountInfo::is_owned_by"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_AccountInfo_is_signerBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_AccountInfo_is_signerCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_AccountInfo_is_signerBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_AccountInfo_is_signerBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_AccountInfo_is_signerBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_AccountInfo_is_signerBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_AccountInfo_is_signerBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_AccountInfo_is_signerBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_AccountInfo_is_signerBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_AccountInfo_is_signerBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_AccountInfo_is_signerBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_AccountInfo_is_signer_profile_controls :
    account_info_AccountInfo_is_signerCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_AccountInfo_is_signer).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_AccountInfo_is_signer_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_AccountInfo_is_signerBuild with version := version }).identities
          .account_info_AccountInfo_is_signer).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::AccountInfo::is_signer",
          "pinocchio::account_info::AccountInfo::is_signer"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_AccountInfo_is_writableBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_AccountInfo_is_writableCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_AccountInfo_is_writableBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_AccountInfo_is_writableBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_AccountInfo_is_writableBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_AccountInfo_is_writableBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_AccountInfo_is_writableBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_AccountInfo_is_writableBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_AccountInfo_is_writableBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_AccountInfo_is_writableBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_AccountInfo_is_writableBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_AccountInfo_is_writable_profile_controls :
    account_info_AccountInfo_is_writableCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_AccountInfo_is_writable).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_AccountInfo_is_writable_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_AccountInfo_is_writableBuild with version := version }).identities
          .account_info_AccountInfo_is_writable).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::AccountInfo::is_writable",
          "pinocchio::account_info::AccountInfo::is_writable"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_AccountInfo_keyBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_AccountInfo_keyCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_AccountInfo_keyBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_AccountInfo_keyBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_AccountInfo_keyBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_AccountInfo_keyBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_AccountInfo_keyBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_AccountInfo_keyBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_AccountInfo_keyBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_AccountInfo_keyBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_AccountInfo_keyBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_AccountInfo_key_profile_controls :
    account_info_AccountInfo_keyCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_AccountInfo_key).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_AccountInfo_key_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_AccountInfo_keyBuild with version := version }).identities
          .account_info_AccountInfo_key).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::AccountInfo::key",
          "pinocchio::account_info::AccountInfo::key"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_AccountInfo_lamportsBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_AccountInfo_lamportsCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_AccountInfo_lamportsBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_AccountInfo_lamportsBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_AccountInfo_lamportsBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_AccountInfo_lamportsBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_AccountInfo_lamportsBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_AccountInfo_lamportsBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_AccountInfo_lamportsBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_AccountInfo_lamportsBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_AccountInfo_lamportsBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_AccountInfo_lamports_profile_controls :
    account_info_AccountInfo_lamportsCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_AccountInfo_lamports).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_AccountInfo_lamports_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_AccountInfo_lamportsBuild with version := version }).identities
          .account_info_AccountInfo_lamports).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::AccountInfo::lamports",
          "pinocchio::account_info::AccountInfo::lamports"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_AccountInfo_ownerBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_AccountInfo_ownerCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_AccountInfo_ownerBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_AccountInfo_ownerBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_AccountInfo_ownerBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_AccountInfo_ownerBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_AccountInfo_ownerBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_AccountInfo_ownerBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_AccountInfo_ownerBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_AccountInfo_ownerBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_AccountInfo_ownerBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_AccountInfo_owner_profile_controls :
    account_info_AccountInfo_ownerCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_AccountInfo_owner).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_AccountInfo_owner_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_AccountInfo_ownerBuild with version := version }).identities
          .account_info_AccountInfo_owner).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::AccountInfo::owner",
          "pinocchio::account_info::AccountInfo::owner"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_AccountInfo_resizeBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩]
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_AccountInfo_resizeCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_AccountInfo_resizeBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_AccountInfo_resizeBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_AccountInfo_resizeBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_AccountInfo_resizeBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_AccountInfo_resizeBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_AccountInfo_resizeBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_AccountInfo_resizeBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_AccountInfo_resizeBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ account_info_AccountInfo_resizeBuild with target := [] }, false),
  -- wrong-target-os; unsupported
  ({ account_info_AccountInfo_resizeBuild with target := [⟨"os", "linux"⟩] }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_AccountInfo_resizeBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_AccountInfo_resize_profile_controls :
    account_info_AccountInfo_resizeCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_AccountInfo_resize).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_AccountInfo_resize_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_AccountInfo_resizeBuild with version := version }).identities
          .account_info_AccountInfo_resize).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::AccountInfo::resize",
          "pinocchio::account_info::AccountInfo::resize"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_AccountInfo_try_borrow_dataBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_AccountInfo_try_borrow_dataCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_AccountInfo_try_borrow_dataBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_AccountInfo_try_borrow_dataBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_AccountInfo_try_borrow_dataBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_AccountInfo_try_borrow_dataBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_AccountInfo_try_borrow_dataBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_AccountInfo_try_borrow_dataBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_AccountInfo_try_borrow_dataBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_AccountInfo_try_borrow_dataBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_AccountInfo_try_borrow_dataBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_AccountInfo_try_borrow_data_profile_controls :
    account_info_AccountInfo_try_borrow_dataCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_AccountInfo_try_borrow_data).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_AccountInfo_try_borrow_data_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_AccountInfo_try_borrow_dataBuild with version := version }).identities
          .account_info_AccountInfo_try_borrow_data).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::AccountInfo::try_borrow_data",
          "pinocchio::account_info::AccountInfo::try_borrow_data"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_AccountInfo_try_borrow_mut_dataBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_AccountInfo_try_borrow_mut_dataCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_AccountInfo_try_borrow_mut_dataBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_AccountInfo_try_borrow_mut_dataBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_AccountInfo_try_borrow_mut_dataBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_AccountInfo_try_borrow_mut_dataBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_AccountInfo_try_borrow_mut_dataBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_AccountInfo_try_borrow_mut_dataBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_AccountInfo_try_borrow_mut_dataBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_AccountInfo_try_borrow_mut_dataBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_AccountInfo_try_borrow_mut_dataBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_AccountInfo_try_borrow_mut_data_profile_controls :
    account_info_AccountInfo_try_borrow_mut_dataCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_AccountInfo_try_borrow_mut_data).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_AccountInfo_try_borrow_mut_data_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_AccountInfo_try_borrow_mut_dataBuild with version := version }).identities
          .account_info_AccountInfo_try_borrow_mut_data).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::AccountInfo::try_borrow_mut_data",
          "pinocchio::account_info::AccountInfo::try_borrow_mut_data"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_AccountInfo_try_borrow_mut_lamportsBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_AccountInfo_try_borrow_mut_lamportsCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_AccountInfo_try_borrow_mut_lamportsBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_AccountInfo_try_borrow_mut_lamportsBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_AccountInfo_try_borrow_mut_lamportsBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_AccountInfo_try_borrow_mut_lamportsBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_AccountInfo_try_borrow_mut_lamportsBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_AccountInfo_try_borrow_mut_lamportsBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_AccountInfo_try_borrow_mut_lamportsBuild with package := "unrelated-sourc\
    e" },
    false),
  -- wrong-origin; unsupported
  ({ account_info_AccountInfo_try_borrow_mut_lamportsBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_AccountInfo_try_borrow_mut_lamportsBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_AccountInfo_try_borrow_mut_lamports_profile_controls :
    account_info_AccountInfo_try_borrow_mut_lamportsCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_AccountInfo_try_borrow_mut_lamports).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_AccountInfo_try_borrow_mut_lamports_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_AccountInfo_try_borrow_mut_lamportsBuild with version := version
          }).identities .account_info_AccountInfo_try_borrow_mut_lamports).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::AccountInfo::try_borrow_mut_lampo\
          rts",
          "pinocchio::account_info::AccountInfo::try_borrow_mut_lamports"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.Pinocchio.Accounts.Pr575Compatibility
