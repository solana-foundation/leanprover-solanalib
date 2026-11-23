/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaSysvar.GetStringError
public import Solanalib.Specs.SolanaSysvar.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SolanaSysvar.StringError

open Solanalib.Specs.Core.Sysvar.Legacy

theorem retains_borsh_payload :
    fromStatus .split222 (UInt64.ofNat (15 * 2^32)) = .borshIoError "Unknown" := by decide

theorem arbitrary_status_keeps_low_word :
    fromStatus .split222 (UInt64.ofNat (27 * 2^32 + 7)) = .plain (.custom 7) := by decide

theorem known_nonzero_is_not_folded :
    fromStatus .split222 (UInt64.ofNat (2 * 2^32)) = .plain .invalidArgument := by decide

open Solanalib.Contracts.Model Solanalib.Specs.Core

def request : Sysvar.ReadRequest Sysvar.Clock := ⟨.typed .clock, some Sysvar.zeroClock⟩

def afterReadCopy : Index Sysvar.Clock where
  getter := {
    State := Nat
    Unwind := Nat
    Terminal := Nat
    target := .solana
    read := Callback.ofFunction fun before _ =>
      .returned ⟨UInt64.ofNat (15 * 2^32), none⟩ (before + 1)
  }
  StringResource := Nat
  currentString := fun _ _ => none
  copyLiteral := Callback.ofFunction fun before literal =>
    .terminated (if before = 1 ∧ literal = "Unknown" then 77 else 88)

/-- The copy receives the actual after-state of the syscall, and its terminal exit
is retained without inventing a final resource state. -/
theorem copy_after_read_can_terminate :
    Solanalib.Specs.SolanaSysvar.clock.Clock.string_error.get_run afterReadCopy (0 : Nat) ()
      (.terminated (77 : Nat)) := by
  apply allocation_exit_retained .split222 request afterReadCopy (0 : Nat) (1 : Nat)
    ?_ (.terminated (77 : Nat)) (by rfl)
  exact ⟨.returned ⟨UInt64.ofNat (15 * 2^32), none⟩ (1 : Nat), rfl, by rfl⟩

def reusedString : Index Sysvar.Clock :=
  { sample Sysvar.zeroClock with currentString := fun _ _ => some "Unknown" }

/-- A value-correct error still fails the actual ownership law if its alleged
new resource already existed at the reached copy site. -/
theorem preexisting_string_rejected : ¬ StringReady .split222 request reusedString [] := by
  intro ready
  have called : Sysvar.get (config .split222 request) reusedString.getter [] ()
      (.returned (.error .borshIoError) []) :=
    ⟨.returned ⟨UInt64.ofNat (15 * 2^32), some Sysvar.zeroClock⟩ [], rfl, by rfl⟩
  have fresh := (ready [] called (0 : Nat) ["Unknown"] (by rfl)).1
  cases fresh

def unwindCopy : Index Sysvar.Clock :=
  { afterReadCopy with
    copyLiteral := Callback.ofFunction fun (before : Nat) _ =>
      .unwound (91 : Nat) (before + 4) }

theorem copy_unwind_retains_final_state :
    Solanalib.Specs.SolanaSysvar.clock.Clock.string_error.get_run unwindCopy (0 : Nat) ()
      (.unwound (91 : Nat) (5 : Nat)) := by
  apply allocation_exit_retained .split222 request unwindCopy (0 : Nat) (1 : Nat)
    ?_ (.unwound (91 : Nat) (5 : Nat)) (by rfl)
  exact ⟨.returned ⟨UInt64.ofNat (15 * 2^32), none⟩ (1 : Nat), rfl, by rfl⟩

def plainError : Index Sysvar.Clock :=
  { afterReadCopy with
    getter := { afterReadCopy.getter with
      read := Callback.ofFunction fun (before : Nat) _ =>
        .returned ⟨UInt64.ofNat (2 * 2^32), none⟩ (before + 1) } }

/-- A plain builtin error retains the state of the read without reaching the
terminating String allocator. -/
theorem plain_error_bypasses_string_copy :
    Solanalib.Specs.SolanaSysvar.clock.Clock.string_error.get_run plainError (0 : Nat) ()
      (.returned (.error (.plain .invalidArgument)) (1 : Nat)) :=
  ⟨.returned (.error .invalidArgument) (1 : Nat),
    ⟨.returned ⟨UInt64.ofNat (2 * 2^32), none⟩ (1 : Nat), rfl, by rfl⟩, rfl⟩

theorem owned_error_uses_new_handle :
    Solanalib.Specs.SolanaSysvar.clock.Clock.string_error.get_run (sample Sysvar.zeroClock)
      ["kept"] ()
      (.returned (.error (.borshIoError (1 : Nat))) ["kept", "Unknown"]) ∧
    observeError (sample Sysvar.zeroClock) ["kept", "Unknown"] (.borshIoError (1 : Nat)) =
      some (.borshIoError "Unknown") ∧
    observeError (sample Sysvar.zeroClock) ["kept"] (.borshIoError (1 : Nat)) = none := by
  refine ⟨?_, rfl, rfl⟩
  apply (allocated_returned_iff .split222 request (sample Sysvar.zeroClock)
    ["kept"] ["kept", "Unknown"] (1 : Nat)).mpr
  exact ⟨["kept"],
    ⟨.returned ⟨UInt64.ofNat (15 * 2^32), some Sysvar.zeroClock⟩ ["kept"], rfl, by rfl⟩, rfl⟩

def cratesIo : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def selectedBuild : Versioning.Build where
  package := "solana-sysvar"
  version := "2.3.0"
  source := cratesIo
  features := some ["bincode"]
  dependencies := [⟨"solana-program-error", "2.2.2", cratesIo⟩,
    ⟨"solana-program-entrypoint", "2.3.0", cratesIo⟩,
    ⟨"solana-clock", "2.2.2", cratesIo⟩, ⟨"solana-rent", "2.2.1", cratesIo⟩]

theorem reviewed_getters_admitted :
    (Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild selectedBuild).identities
      .clock_Clock_string_error_get ≠ [] ∧
    (Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild selectedBuild).identities
      .rent_Rent_string_error_get ≠ [] :=
  by decide +kernel

/-- The newly reviewed 2.2.2 source keeps the same explicit dependency obligations. -/
theorem reviewed_222_getters_admitted :
    (Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
      { selectedBuild with version := "2.2.2" }).identities .clock_Clock_string_error_get ≠ [] ∧
    (Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
      { selectedBuild with version := "2.2.2" }).identities .rent_Rent_string_error_get ≠ [] :=
  by decide +kernel

def getterMembers : List (Solanalib.Specs.SolanaSysvar.Capabilities.Key × String) :=
  [(.clock_Clock_string_error_get,
    "solana_sysvar::clock::<impl solana_sysvar::Sysvar for solana_clock::Clock>::get"),
    (.rent_Rent_string_error_get,
    "solana_sysvar::rent::<impl solana_sysvar::Sysvar for solana_rent::Rent>::get")]

/-- Compatible field and error providers preserve the complete getter identity;
the required bincode feature remains part of this build. -/
theorem compatible_getter_identities :
    ["2.3.0", "2.3.1", "2.9.0"].all (fun version => getterMembers.all (fun (key, implementation) =>
      decide ((Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
        { selectedBuild with
          version := version
          dependencies := [⟨"solana-program-error", "2.2.3", cratesIo⟩,
            ⟨"solana-program-entrypoint", "2.3.1", cratesIo⟩,
            ⟨"solana-clock", "2.2.3", cratesIo⟩, ⟨"solana-rent", "2.2.2", cratesIo⟩] }).identities
              key =
        [⟨"solana-sysvar", version, "solana_sysvar::Sysvar::get", implementation⟩]))) = true := by
  decide +kernel

theorem outside_string_error_range_rejected :
    ["2.2.1", "3.0.0", "2.3.1-rc.1"].all (fun version => getterMembers.all (fun (key, _) =>
      decide ((Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities key = []))) = true := by
  decide +kernel

theorem below_reference_getter_rejected :
    (Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
      { selectedBuild with version := "2.2.1" }).identities .clock_Clock_string_error_get = [] :=
  by decide +kernel

theorem missing_bincode_rejected :
    (Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
      { selectedBuild with version := "2.3.1", features := some [] }).identities
        .rent_Rent_string_error_get = [] :=
  by decide +kernel

theorem unknown_bincode_rejected :
    (Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
      { selectedBuild with version := "2.3.1", features := none }).identities
        .clock_Clock_string_error_get = [] := by decide +kernel

theorem changed_error_dependency_rejected :
    (Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
      { selectedBuild with
        version := "2.3.1"
        dependencies := selectedBuild.dependencies.map fun dependency =>
        if dependency.package = "solana-program-error" then
          { dependency with version := "3.0.1" } else dependency }).identities
            .clock_Clock_string_error_get = [] :=
  by decide +kernel

theorem missing_rent_dependency_rejected :
    (Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
      { selectedBuild with
        version := "2.3.1"
        dependencies := selectedBuild.dependencies.filter fun dependency =>
        dependency.package != "solana-rent" }).identities .rent_Rent_string_error_get = [] :=
  by decide +kernel

end SolanalibTest.Specs.SolanaSysvar.StringError

namespace SolanalibTest.Specs.SolanaSysvar.StringError.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def clock_Clock_string_error_getBuild : Versioning.Build where
  package := "solana-sysvar"
  version := "2.2.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some ["bincode"]
  targetFeatures := some []
  dependencies := [⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-entrypoint", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-clock", "2.2.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def clock_Clock_string_error_getCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-2.2.2; eligible
  (clock_Clock_string_error_getBuild, true),
  -- lower; eligible
  (clock_Clock_string_error_getBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ clock_Clock_string_error_getBuild with version := "2.2.99" }, true),
  -- exclusive-upper; unsupported
  ({ clock_Clock_string_error_getBuild with version := "2.3.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ clock_Clock_string_error_getBuild with version := "2.2.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ clock_Clock_string_error_getBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ clock_Clock_string_error_getBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-features; unresolved
  ({ clock_Clock_string_error_getBuild with features := none }, false),
  -- wrong-features; unsupported
  ({ clock_Clock_string_error_getBuild with features := some [] }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (clock_Clock_string_error_getBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (clock_Clock_string_error_getBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-entrypoint-2.2.1; eligible
  (clock_Clock_string_error_getBuild, true),
  -- dependency-reference-solana-program-entrypoint-2.3.0; eligible
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with version := "2.3.0" } else dependency)) },
    true),
  -- dependency-solana-program-entrypoint-lower; eligible
  (clock_Clock_string_error_getBuild, true),
  -- dependency-solana-program-entrypoint-hypothetical-declaration-probe; eligible
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with version := "2.2.98" } else dependency)) },
    true),
  -- dependency-solana-program-entrypoint-exclusive-upper; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with version := "3.0.0" } else dependency)) },
    false),
  -- dependency-solana-program-entrypoint-unlisted-prerelease; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with version := "2.2.1-rc.1" } else dependency))
    }, false),
  -- missing-dependency-solana-program-entrypoint; unresolved
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-entrypoint")) }, false),
  -- wrong-dependency-origin-solana-program-entrypoint; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-entrypoint; ValueError containing Ambiguous dependency
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies ++ [⟨
    "solana-program-entrypoint", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-clock-2.2.2; eligible
  (clock_Clock_string_error_getBuild, true),
  -- dependency-solana-clock-lower; eligible
  (clock_Clock_string_error_getBuild, true),
  -- dependency-solana-clock-hypothetical-declaration-probe; eligible
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-clock" then { dependency with version := "2.2.99" } else dependency)) }, true),
  -- dependency-solana-clock-exclusive-upper; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-clock" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-clock-unlisted-prerelease; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-clock" then { dependency with version := "2.2.2-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-clock; unresolved
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-clock")) }, false),
  -- wrong-dependency-origin-solana-clock; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-clock" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-clock; ValueError containing Ambiguous dependency
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies ++ [⟨
    "solana-clock", "2.2.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-2.2.1; unsupported
  ({ clock_Clock_string_error_getBuild with version := "2.2.1" }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-entrypoint-below-lower-bound-fixture-2.2.0; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with version := "2.2.0" } else dependency)) },
    false),
  -- dependency-solana-clock-below-lower-bound-fixture-2.2.1; unsupported
  ({ clock_Clock_string_error_getBuild with dependencies :=
    (clock_Clock_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-clock" then { dependency with version := "2.2.1" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem clock_Clock_string_error_get_profile_controls :
    clock_Clock_string_error_getCases.all (fun test =>
      (((Solanalib.Specs.SolanaSysvar.Capabilities.catalog.applicability
        .clock_Clock_string_error_get).any
        (fun profile => ["typed-clock-2.2.2"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem clock_Clock_string_error_get_callable_identities :
    ["2.2.2", "2.2.99"].all (fun version =>
      (((Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
        { clock_Clock_string_error_getBuild with version := version }).identities
          .clock_Clock_string_error_get).eraseDups ==
        [⟨"solana-sysvar", version, "solana_sysvar::Sysvar::get",
          "solana_sysvar::clock::<impl solana_sysvar::Sysvar for solana_clock::Clock>::get"⟩])) =
          true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def rent_Rent_string_error_getBuild : Versioning.Build where
  package := "solana-sysvar"
  version := "2.2.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some ["bincode"]
  targetFeatures := some []
  dependencies := [⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-entrypoint", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-rent", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def rent_Rent_string_error_getCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-2.2.2; eligible
  (rent_Rent_string_error_getBuild, true),
  -- lower; eligible
  (rent_Rent_string_error_getBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ rent_Rent_string_error_getBuild with version := "2.2.99" }, true),
  -- exclusive-upper; unsupported
  ({ rent_Rent_string_error_getBuild with version := "2.3.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ rent_Rent_string_error_getBuild with version := "2.2.2-rc.1" }, false),
  -- wrong-package; unsupported
  ({ rent_Rent_string_error_getBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ rent_Rent_string_error_getBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-features; unresolved
  ({ rent_Rent_string_error_getBuild with features := none }, false),
  -- wrong-features; unsupported
  ({ rent_Rent_string_error_getBuild with features := some [] }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (rent_Rent_string_error_getBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (rent_Rent_string_error_getBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-entrypoint-2.2.1; eligible
  (rent_Rent_string_error_getBuild, true),
  -- dependency-reference-solana-program-entrypoint-2.3.0; eligible
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with version := "2.3.0" } else dependency)) },
    true),
  -- dependency-solana-program-entrypoint-lower; eligible
  (rent_Rent_string_error_getBuild, true),
  -- dependency-solana-program-entrypoint-hypothetical-declaration-probe; eligible
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with version := "2.2.98" } else dependency)) },
    true),
  -- dependency-solana-program-entrypoint-exclusive-upper; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with version := "3.0.0" } else dependency)) },
    false),
  -- dependency-solana-program-entrypoint-unlisted-prerelease; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with version := "2.2.1-rc.1" } else dependency))
    }, false),
  -- missing-dependency-solana-program-entrypoint; unresolved
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-entrypoint")) }, false),
  -- wrong-dependency-origin-solana-program-entrypoint; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-entrypoint; ValueError containing Ambiguous dependency
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies ++ [⟨
    "solana-program-entrypoint", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-rent-2.2.1; eligible
  (rent_Rent_string_error_getBuild, true),
  -- dependency-solana-rent-lower; eligible
  (rent_Rent_string_error_getBuild, true),
  -- dependency-solana-rent-hypothetical-declaration-probe; eligible
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-rent" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-rent-exclusive-upper; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-rent" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-rent-unlisted-prerelease; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-rent" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-rent; unresolved
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-rent")) }, false),
  -- wrong-dependency-origin-solana-rent; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-rent" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-rent; ValueError containing Ambiguous dependency
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies ++ [⟨
    "solana-rent", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-2.2.1; unsupported
  ({ rent_Rent_string_error_getBuild with version := "2.2.1" }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-entrypoint-below-lower-bound-fixture-2.2.0; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-entrypoint" then { dependency with version := "2.2.0" } else dependency)) },
    false),
  -- dependency-solana-rent-below-lower-bound-fixture-2.2.0; unsupported
  ({ rent_Rent_string_error_getBuild with dependencies :=
    (rent_Rent_string_error_getBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-rent" then { dependency with version := "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem rent_Rent_string_error_get_profile_controls :
    rent_Rent_string_error_getCases.all (fun test =>
      (((Solanalib.Specs.SolanaSysvar.Capabilities.catalog.applicability
        .rent_Rent_string_error_get).any
        (fun profile => ["typed-rent-2.2.2"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem rent_Rent_string_error_get_callable_identities :
    ["2.2.2", "2.2.99"].all (fun version =>
      (((Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
        { rent_Rent_string_error_getBuild with version := version }).identities
          .rent_Rent_string_error_get).eraseDups ==
        [⟨"solana-sysvar", version, "solana_sysvar::Sysvar::get",
          "solana_sysvar::rent::<impl solana_sysvar::Sysvar for solana_rent::Rent>::get"⟩])) = true
          := by
  decide +kernel

/-- The earlier profile remains usable alongside the incoming interval. -/
def clock_Clock_string_error_get_inheritedBuild : Versioning.Build where
  package := "solana-sysvar"
  version := "2.3.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some ["bincode"]
  targetFeatures := some []
  dependencies := [⟨"solana-program-error", "2.2.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-entrypoint", "2.3.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-clock", "2.2.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

set_option maxRecDepth 8192 in
theorem clock_Clock_string_error_get_inherited_callable_identity :
    ((Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
      clock_Clock_string_error_get_inheritedBuild).identities
      .clock_Clock_string_error_get).eraseDups =
      [⟨"solana-sysvar", "2.3.0", "solana_sysvar::Sysvar::get",
        "solana_sysvar::clock::<impl solana_sysvar::Sysvar for solana_clock::Clock>::get"⟩] := by
  decide +kernel

/-- The earlier profile remains usable alongside the incoming interval. -/
def rent_Rent_string_error_get_inheritedBuild : Versioning.Build where
  package := "solana-sysvar"
  version := "2.3.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some ["bincode"]
  targetFeatures := some []
  dependencies := [⟨"solana-program-error", "2.2.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-entrypoint", "2.3.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-rent", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

set_option maxRecDepth 8192 in
theorem rent_Rent_string_error_get_inherited_callable_identity :
    ((Solanalib.Specs.SolanaSysvar.Capabilities.catalog.forBuild
      rent_Rent_string_error_get_inheritedBuild).identities .rent_Rent_string_error_get).eraseDups =
      [⟨"solana-sysvar", "2.3.0", "solana_sysvar::Sysvar::get",
        "solana_sysvar::rent::<impl solana_sysvar::Sysvar for solana_rent::Rent>::get"⟩] := by
  decide +kernel

end SolanalibTest.Specs.SolanaSysvar.StringError.Pr575Compatibility
