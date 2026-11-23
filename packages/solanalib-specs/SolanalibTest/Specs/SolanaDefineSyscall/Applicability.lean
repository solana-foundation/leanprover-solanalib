/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaDefineSyscall.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaDefineSyscall.Applicability

open Solanalib.Contracts.Model.Versioning Solanalib.Specs.SolanaDefineSyscall.Capabilities

/-- Exact registry release with the dynamic declaration selected on this architecture. -/
def dynamicBuild (arch : String) : Build where
  package := "solana-define-syscall"
  version := "5.2.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"arch", arch⟩]
  features := some []
  targetFeatures := some []

/-- The two declarations whose release boundaries are checked in this module. -/
inductive Call where
  | sha512
  | multiscalar

/-- Select the corresponding member of the shared syscall catalog. -/
def Call.key : Call → Key
  | .sha512 => .definitions_sol_sha512
  | .multiscalar => .definitions_sol_curve_multiscalar_mul

/-- Every published release whose declaration and dispatch have been reviewed for this call. -/
def reviewedVersions : Call → List String
  | .sha512 => ["5.1.0", "5.2.0", "5.3.0", "5.4.0"]
  | .multiscalar =>
      ["2.2.0", "2.2.1", "2.3.0", "3.0.0", "4.0.0", "4.0.1",
        "5.0.0", "5.1.0", "5.2.0", "5.3.0", "5.4.0"]

/-- Selection retains the function name and records the actual release on both architectures. -/
theorem reviewed_dynamic_versions_admitted (key : Call) :
    (reviewedVersions key).all (fun version => ["x86_64", "bpf"].all (fun arch =>
      decide ((catalog.forBuild { dynamicBuild arch with version := version }).identities key.key =
        (catalog.identities key.key).map (fun identity => { identity with crateVersion := version
          })))) =
      true := by
  cases key <;> decide +kernel

/-- Both symbols retain their exact names and version under the non-BPF dynamic branch. -/
theorem dynamic_non_bpf_admitted (key : Call) :
    (catalog.forBuild (dynamicBuild "x86_64")).identities key.key = catalog.identities key.key := by
  cases key <;> decide +kernel

/-- The separately constrained BPF dynamic branch admits the same exact identities. -/
theorem dynamic_bpf_admitted (key : Call) :
    (catalog.forBuild (dynamicBuild "bpf")).identities key.key = catalog.identities key.key := by
  cases key <;> decide +kernel

/-- The unstable static-dispatch feature of the crate has no effect away from BPF. -/
theorem non_bpf_crate_feature_irrelevant (key : Call) :
    (catalog.forBuild { dynamicBuild "x86_64" with
      features := some ["unstable-static-syscalls"] }).identities key.key =
      catalog.identities key.key := by
  cases key <;> decide +kernel

/-- No unused package-feature facts are required on a non-BPF target. -/
theorem non_bpf_unknown_crate_features_admitted (key : Call) :
    (catalog.forBuild { dynamicBuild "x86_64" with features := none }).identities key.key =
      catalog.identities key.key := by
  cases key <;> decide +kernel

/-- Declared compatibility admits unlisted stable releases with their actual identity. -/
theorem compatible_versions_admitted (key : Call) :
    ["5.1.1", "5.5.0"].all (fun version =>
      decide ((catalog.forBuild { dynamicBuild "x86_64" with version := version }).identities
        key.key =
        (catalog.identities key.key).map (fun identity => { identity with crateVersion := version
          }))) =
      true := by
  cases key <;> decide +kernel

/-- The declared range admits neither a new major line nor an unreviewed prerelease. -/
theorem outside_compatible_range_rejected (key : Call) :
    (catalog.forBuild { dynamicBuild "x86_64" with version := "6.0.0" }).identities key.key = [] ∧
      (catalog.forBuild { dynamicBuild "x86_64" with version := "5.5.0-rc.1" }).identities key.key
        = [] := by
  cases key <;> decide +kernel

/-- Neither operation is selected before its defining declaration exists. -/
theorem absent_declarations_rejected :
    ["0.0.1", "0.0.2", "2.1.0", "2.1.21"].all (fun version =>
      decide ((catalog.forBuild { dynamicBuild "x86_64" with version := version }).identities
        .definitions_sol_curve_multiscalar_mul = [])) = true ∧
      ["2.2.0", "2.2.1", "2.3.0", "3.0.0", "4.0.0", "4.0.1", "5.0.0"].all (fun version =>
        decide ((catalog.forBuild { dynamicBuild "x86_64" with version := version }).identities
          .definitions_sol_sha512 = [])) = true := by
  decide +kernel

/-- Earlier MSM declarations do not inspect the architecture or a crate dispatch feature. -/
theorem legacy_msm_needs_only_target_features :
    ["2.2.0", "2.2.1", "2.3.0", "3.0.0"].all (fun version =>
      decide ((catalog.forBuild { dynamicBuild "bpf" with
        version := version
        target := []
        features := none }).identities .definitions_sol_curve_multiscalar_mul =
          [⟨"solana-define-syscall", version,
            "solana_define_syscall::definitions::sol_curve_multiscalar_mul",
            "solana_define_syscall::definitions::sol_curve_multiscalar_mul"⟩])) = true := by
  decide +kernel

/-- Every admitted release still excludes the compiler-selected static wrapper. -/
theorem all_static_target_features_rejected (key : Call) :
    (reviewedVersions key).all (fun version => ["x86_64", "bpf"].all (fun arch =>
      decide ((catalog.forBuild { dynamicBuild arch with
        version := version
        targetFeatures := some ["static-syscalls"] }).identities key.key = []))) = true := by
  cases key <;> decide +kernel

/-- The modern BPF crate-feature exclusion applies across the release ranges of both calls. -/
theorem all_modern_bpf_static_features_rejected (key : Call) :
    ["4.0.0", "4.0.1", "5.0.0", "5.1.0", "5.2.0", "5.3.0", "5.4.0"].all (fun version =>
      decide ((catalog.forBuild { dynamicBuild "bpf" with
        version := version
        features := some ["unstable-static-syscalls"] }).identities key.key = [])) = true := by
  cases key <;> decide +kernel

/-- The static-syscalls feature of the compiler selects an unregistered thunk on both targets. -/
theorem static_target_feature_rejected (key : Call) :
    (catalog.forBuild { dynamicBuild "x86_64" with
      targetFeatures := some ["static-syscalls"] }).identities key.key = [] ∧
      (catalog.forBuild { dynamicBuild "bpf" with
        targetFeatures := some ["static-syscalls"] }).identities key.key = [] := by
  cases key <;> decide +kernel

/-- On BPF the crate feature also selects the unregistered static thunk. -/
theorem bpf_static_crate_feature_rejected (key : Call) :
    (catalog.forBuild { dynamicBuild "bpf" with
      features := some ["unstable-static-syscalls"] }).identities key.key = [] := by
  cases key <;> decide +kernel

/-- Missing constrained compilation facts cannot make either operation callable. -/
theorem missing_build_facts_not_admitted (key : Call) :
    (catalog.forBuild { dynamicBuild "x86_64" with target := [] }).identities key.key = [] ∧
      (catalog.forBuild { dynamicBuild "x86_64" with targetFeatures := none }).identities key.key =
        [] ∧
      (catalog.forBuild { dynamicBuild "bpf" with features := none }).identities key.key = [] := by
  cases key <;> decide +kernel

/-- A fork with the same package name and version is outside the reviewed registry source. -/
theorem same_version_fork_rejected (key : Call) :
    (catalog.forBuild { dynamicBuild "x86_64" with
      source := ⟨"git", "https://example.org/syscall-fork",
        "0123456789012345678901234567890123456789"⟩ }).identities key.key = [] := by
  cases key <;> decide +kernel

end SolanalibTest.Specs.SolanaDefineSyscall.Applicability
