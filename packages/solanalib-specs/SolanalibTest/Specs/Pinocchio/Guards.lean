/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Pinocchio.Guard
public import Solanalib.Specs.Pinocchio.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Pinocchio.Guards

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.PinocchioAccount

def profile : MapProfile := ⟨guardSample, String, String, fun _ _ _ _ => True⟩
def mappedArgs : MapArgs profile :=
  ⟨sampleGuard, fun before _ _ produced => produced = .returned (.bytes 1 2) before⟩

theorem map_success_keeps_lease :
    Solanalib.Specs.Pinocchio.account_info.RefMut.map_run profile sampleGuardState mappedArgs
      (.returned (nextGuard sampleGuard)
        ((Borrow.transfer sampleGuardState.1 sampleGuard (.bytes 1 2)).2, sampleGuardState.2)) :=
  ⟨_, _, .returned (.bytes 1 2) sampleGuardState, rfl, rfl, rfl, rfl⟩

def mapped : State := ((Borrow.transfer sampleGuardState.1 sampleGuard (.bytes 1 2)).2,
  sampleGuardState.2)

theorem deref_mut_retains_current_reference :
    Solanalib.Specs.Pinocchio.account_info.RefMut.deref_mut_run guardSample mapped (nextGuard
      sampleGuard)
      (.returned ⟨nextGuard sampleGuard, true⟩ mapped) := rfl

/-- A mapped guard consumes the original generation while retaining the lease. -/
theorem mapping_invalidates_original_generation :
    mapped.1.resolve sampleGuard = none ∧
    borrowByte mapped sampleHandle = 247 := by decide +kernel

def released : State :=
  ((Borrow.release mapped.1 (nextGuard sampleGuard)).2, mapped.2)

/-- Releasing the mapped guard repays the original data lease exactly once. -/
theorem mapped_release_repays_original_field :
    released.1.resolve sampleGuard = none ∧
    released.1.resolve (nextGuard sampleGuard) = none ∧
    borrowByte released sampleHandle = 255 ∧
    (released.data sampleHandle).backing = sampleInput.data.backing := by decide +kernel

def callbackState : State :=
  ((Borrow.replaceCell sampleGuardState.1 (sampleGuardState.field sampleHandle .data)
    (.data { sampleInput.data with backing := [11, 20, 30, 90, 91] })).2, sampleGuardState.2)

def unwindArgs : MapArgs profile :=
  ⟨sampleGuard, fun _ _ _ produced => produced = .unwound "callback" callbackState⟩

def unwindState : State :=
  (Borrow.unwindState .retainLease callbackState.1 sampleGuard .whole, callbackState.2)

/-- ManuallyDrop precedes the callback, so unwind retains its actual writes. -/
theorem map_unwind_retains_callback_state :
    Solanalib.Specs.Pinocchio.account_info.RefMut.map_run profile sampleGuardState unwindArgs
      (.unwound "callback" unwindState) :=
  ⟨_, _, .unwound "callback" callbackState, rfl, rfl, rfl, rfl⟩

private theorem sample_guard_valid : sampleGuardState.1.Valid := by
  have base : sampleState.1.Valid := Borrow.State.valid_empty_slots _
  change (sampleState.1.issue (sampleState.field sampleHandle .data) .exclusive .whole).2.Valid
  exact Borrow.State.issue_valid base _ _ _ rfl rfl rfl

private theorem callback_frame :
    Borrow.CallbackFrame profile.footprint sampleGuardState.1 callbackState.1 sampleGuard := by
  apply Borrow.CallbackFrame.of_slots
  · exact Borrow.replaceCell_valid sample_guard_valid _ _
  · exact Borrow.replaceCell_slots _ _ _
  · exact fun query => Borrow.replaceCell_policy _ _ query _
  · intro slot old next live oldFound nextFound
    trivial

/-- The concrete unwinding callback meets the full registered precondition. -/
theorem map_unwind_obeys_contract :
    (Solanalib.Specs.Pinocchio.account_info.RefMut.map_contract.contract profile).post
      sampleGuardState unwindArgs (.unwound "callback" unwindState) := by
  apply Solanalib.Specs.Pinocchio.account_info.RefMut.map_reference profile
    sampleGuardState unwindArgs _ _ map_unwind_retains_callback_state
  intro slot cell live present produced called
  cases called
  exact callback_frame

/-- An unwinding map leaks the lease but retires the consumed source token. -/
theorem unwind_preserves_write_and_retires_generation :
    (unwindState.data sampleHandle).backing = [11, 20, 30, 90, 91] ∧
    borrowByte unwindState sampleHandle = 247 ∧
    unwindState.1.resolve sampleGuard = none := by decide +kernel

def terminalArgs : MapArgs profile :=
  ⟨sampleGuard, fun _ _ _ produced => produced = .terminated "callback stopped"⟩

/-- A terminal callback has no invented guard or post-state. -/
theorem map_terminal_keeps_reason :
    Solanalib.Specs.Pinocchio.account_info.RefMut.map_run profile sampleGuardState terminalArgs
      (.terminated "callback stopped") :=
  ⟨_, _, .terminated "callback stopped", rfl, rfl, rfl, rfl⟩

/-- The same terminal callback cannot be interpreted as a normal map return. -/
theorem terminal_callback_cannot_return (guard : Guard) (after : State) :
    ¬Solanalib.Specs.Pinocchio.account_info.RefMut.map_run profile sampleGuardState terminalArgs
      (.returned guard after) := by
  rintro ⟨slot, cell, produced, live, present, called, finished⟩
  cases called
  cases finished

end SolanalibTest.Specs.Pinocchio.Guards

namespace SolanalibTest.Specs.Pinocchio.Guards.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_Ref_derefBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_Ref_derefCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_Ref_derefBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_Ref_derefBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_Ref_derefBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_Ref_derefBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_Ref_derefBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_Ref_derefBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_Ref_derefBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_Ref_derefBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_Ref_derefBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_Ref_deref_profile_controls :
    account_info_Ref_derefCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability .account_info_Ref_deref).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_Ref_deref_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_Ref_derefBuild with version := version }).identities
          .account_info_Ref_deref).eraseDups ==
        [⟨"pinocchio", version, "core::ops::deref::Deref::deref",
          "<pinocchio::account_info::Ref<'_, T> as core::ops::deref::Deref>::deref"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_RefMut_derefBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_RefMut_derefCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_RefMut_derefBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_RefMut_derefBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_RefMut_derefBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_RefMut_derefBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_RefMut_derefBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_RefMut_derefBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_RefMut_derefBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_RefMut_derefBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_RefMut_derefBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_RefMut_deref_profile_controls :
    account_info_RefMut_derefCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_RefMut_deref).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_RefMut_deref_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_RefMut_derefBuild with version := version }).identities
          .account_info_RefMut_deref).eraseDups ==
        [⟨"pinocchio", version, "core::ops::deref::Deref::deref",
          "<pinocchio::account_info::RefMut<'_, T> as core::ops::deref::Deref>::deref"⟩])) = true
          := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_RefMut_deref_mutBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_RefMut_deref_mutCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_RefMut_deref_mutBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_RefMut_deref_mutBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_RefMut_deref_mutBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_RefMut_deref_mutBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_RefMut_deref_mutBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_RefMut_deref_mutBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_RefMut_deref_mutBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_RefMut_deref_mutBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_RefMut_deref_mutBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_RefMut_deref_mut_profile_controls :
    account_info_RefMut_deref_mutCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability
        .account_info_RefMut_deref_mut).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_RefMut_deref_mut_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_RefMut_deref_mutBuild with version := version }).identities
          .account_info_RefMut_deref_mut).eraseDups ==
        [⟨"pinocchio", version, "core::ops::deref::DerefMut::deref_mut",
          "<pinocchio::account_info::RefMut<'_, T> as \
            core::ops::deref::DerefMut>::deref_mut"⟩])) =
          true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def account_info_RefMut_mapBuild : Versioning.Build where
  package := "pinocchio"
  version := "0.9.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def account_info_RefMut_mapCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.2; eligible
  (account_info_RefMut_mapBuild, true),
  -- inspected-reference-0.9.3; eligible
  ({ account_info_RefMut_mapBuild with version := "0.9.3" }, true),
  -- lower; eligible
  (account_info_RefMut_mapBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ account_info_RefMut_mapBuild with version := "0.9.99" }, true),
  -- exclusive-upper; unsupported
  ({ account_info_RefMut_mapBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ account_info_RefMut_mapBuild with version := "0.9.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ account_info_RefMut_mapBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ account_info_RefMut_mapBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.9.1; unsupported
  ({ account_info_RefMut_mapBuild with version := "0.9.1" }, false)
]

set_option maxRecDepth 8192 in
theorem account_info_RefMut_map_profile_controls :
    account_info_RefMut_mapCases.all (fun test =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.applicability .account_info_RefMut_map).any
        (fun profile => ["pinocchio-0.9.2-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem account_info_RefMut_map_callable_identities :
    ["0.9.2", "0.9.3", "0.9.99"].all (fun version =>
      (((Solanalib.Specs.Pinocchio.Capabilities.catalog.forBuild
        { account_info_RefMut_mapBuild with version := version }).identities
          .account_info_RefMut_map).eraseDups ==
        [⟨"pinocchio", version, "pinocchio::account_info::RefMut::<'a, T>::map",
          "pinocchio::account_info::RefMut::<'a, T>::map"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.Pinocchio.Guards.Pr575Compatibility
