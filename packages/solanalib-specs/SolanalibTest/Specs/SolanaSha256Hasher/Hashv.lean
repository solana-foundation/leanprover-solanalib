/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaSha256Hasher.Hashv
public import Solanalib.Specs.SolanaSha256Hasher.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaSha256Hasher.Hashv

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Hash.Syscall

/-- Ordered nonempty, empty and repeated input slices. -/
def inputs : List Solanalib.Runtime.Bytes := [[8, 9], [], [2], [8, 9]]

/-- A written output with distinguishable bytes; no SHA-256 equation is assumed. -/
def writtenHash : Hash.Value := ⟨(List.range 32).map UInt8.ofNat, by simp⟩

/-- The provider returns nonzero status after initializing its destination. -/
def nonzero : Index where
  State := List Request
  Unwind := String
  Terminal := String
  target := .solanaOS
  provider := Callback.ofFunction fun before call =>
    .returned ⟨7, some writtenHash⟩ (before ++ [call])

theorem actual_request_fields :
    (request inputs).slices = [[8, 9], [], [2], [8, 9]] ∧
    (request inputs).count = 4 ∧ (request inputs).output = none ∧
    (request inputs).canonical = .hash .sha256 inputs := ⟨rfl, rfl, rfl, rfl⟩

theorem nonzero_ready :
    (Solanalib.Specs.SolanaSha256Hasher.hashv_contract.contract nonzero).requires [] inputs := by
  intro reply after execution
  cases execution
  exact ⟨writtenHash, rfl⟩

/-- Status is ignored only after the provider has actually initialized the output. -/
theorem nonzero_return_runs :
    Solanalib.Specs.SolanaSha256Hasher.hashv_model nonzero [] inputs
      (.returned writtenHash [request inputs]) :=
  ⟨.returned ⟨7, some writtenHash⟩ [request inputs], rfl, writtenHash, rfl, rfl⟩

theorem nonzero_return_contract :
    (Solanalib.Specs.SolanaSha256Hasher.hashv_contract.contract nonzero).ensures [] inputs
      writtenHash [request inputs] :=
  (FamilyReference.at Solanalib.Specs.SolanaSha256Hasher.hashv_reference nonzero)
    [] inputs _ nonzero_ready nonzero_return_runs

/-- A backend with a good normal exit and a second, uninitialized nonzero exit. -/
def mixed : Index where
  State := Nat
  Unwind := Empty
  Terminal := Empty
  target := .bpfArch
  provider := fun _ _ outcome =>
    outcome = .returned ⟨0, some writtenHash⟩ 1 ∨ outcome = .returned ⟨9, none⟩ 2

/-- A single valid reply cannot hide another reply that makes assume_init invalid. -/
theorem mixed_uninitialized_nonzero_rejected :
    ¬ (Solanalib.Specs.SolanaSha256Hasher.hashv_contract.contract mixed).requires (0 : Nat) inputs
      := by
  intro ready
  obtain ⟨hash, impossible⟩ := ready ⟨9, none⟩ (2 : Nat) (Or.inr rfl)
  cases impossible

/-- The callback state can retain effects from a finite unwind. -/
def unwinding : Index where
  State := Nat
  Unwind := String
  Terminal := String
  target := .bpfArch
  provider := Callback.ofFunction fun before _ => .unwound "provider unwind" (before + 1)

theorem unwind_ready :
    (Solanalib.Specs.SolanaSha256Hasher.hashv_contract.contract unwinding).requires (4 : Nat)
      inputs := by
  intro reply after impossible
  cases impossible

theorem unwind_keeps_effects :
    Solanalib.Specs.SolanaSha256Hasher.hashv_model unwinding (4 : Nat) inputs
      (.unwound "provider unwind" (5 : Nat)) :=
  ⟨.unwound "provider unwind" (5 : Nat), rfl, rfl⟩

/-- Runtime failure can terminate the call without a readable destination. -/
def terminating : Index where
  State := Unit
  Unwind := Empty
  Terminal := Solanalib.Runtime.InstrError
  target := .solanaOS
  provider := Callback.ofFunction fun _ _ => .terminated .ProgramFailedToComplete

theorem terminal_ready :
    (Solanalib.Specs.SolanaSha256Hasher.hashv_contract.contract terminating).requires () inputs :=
      by
  intro reply after impossible
  cases impossible

theorem terminal_error_preserved :
    Solanalib.Specs.SolanaSha256Hasher.hashv_model terminating () inputs
      (.terminated .ProgramFailedToComplete) :=
  ⟨.terminated .ProgramFailedToComplete, rfl, rfl⟩

/-- A symbolic digest used only to check the boundary of the optional hash law. -/
def zeroPrimitive : Solanalib.Runtime.CryptoPrimitives :=
  ⟨fun _ => List.replicate 32 0, fun _ => false⟩

/-- Successful initialized transport alone does not prove the cryptographic law. -/
theorem transport_does_not_supply_hash_agreement :
    ¬ NormalHashAgreement nonzero.provider zeroPrimitive := by
  intro agreement
  have same := agreement [] inputs ⟨7, some writtenHash⟩ [request inputs] rfl writtenHash rfl
  have different : writtenHash.bytes ≠ zeroPrimitive.sha256 inputs.flatten := by decide
  exact different same

/-- The runtime applies its count limit even when a symbolic digest is defined. -/
theorem canonical_count_failure :
    Solanalib.Runtime.hashReply 3 (fun slices => zeroPrimitive.sha256 slices.flatten) inputs =
      .error .ProgramFailedToComplete := rfl

theorem canonical_count_success :
    Solanalib.Runtime.hashReply 4 (fun slices => zeroPrimitive.sha256 slices.flatten) inputs =
      .ok ⟨0, [zeroPrimitive.sha256 [8, 9, 2, 8, 9]]⟩ := rfl

end SolanalibTest.Specs.SolanaSha256Hasher.Hashv

@[expose] public section

namespace SolanalibTest.Specs.SolanaSha256Hasher.SyscallHashv

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.SolanaSha256Hasher.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.SolanaSha256Hasher.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

def build0 : Versioning.Build where
  package := "solana-sha256-hasher"
  version := "3.1.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩]
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["3.1.0", "3.2.0"].all (fun version =>
      decide (((selectedProfile "singleton-solana-sha256-hasher-reviewed-solana").forBuild
        { build0 with version := version }).identities .hash =
          [⟨"solana-sha256-hasher", version, "solana_sha256_hasher::hash",
            "solana_sha256_hasher::hash"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"solana-sha256-hasher", "3.1.0", "solana_sha256_hasher::hash",
            "solana_sha256_hasher::hash"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaSha256Hasher.Capabilities.catalog.forBuild
        build0).identities .hash)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "singleton-solana-sha256-hasher-reviewed-solana").applicability .hash).length
      = 1 ∧
    ["3.0.999", "4.0.0", "3.2.0-rc.1"].all (fun version =>
      (((selectedProfile "singleton-solana-sha256-hasher-reviewed-solana").forBuild { build0 with
        version := version }).identities
        .hash).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "solana-sha256-hasher-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with target := [] },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"os", "solana"⟩] },
      { build0 with target := [⟨"os", "unsupported-target-value"⟩] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "singleton-solana-sha256-hasher-reviewed-solana").forBuild
        build).identities
        .hash).isEmpty) = true := by
  decide +kernel

def build1 : Versioning.Build where
  package := "solana-sha256-hasher"
  version := "3.1.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "linux"⟩, ⟨"arch", "bpf"⟩]
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile1_literal_identities :
    ["3.1.0", "3.2.0"].all (fun version =>
      decide (((selectedProfile "singleton-solana-sha256-hasher-reviewed-bpf").forBuild
        { build1 with version := version }).identities .hash =
          [⟨"solana-sha256-hasher", version, "solana_sha256_hasher::hash",
            "solana_sha256_hasher::hash"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile1_present_in_full_catalog :
    ([⟨"solana-sha256-hasher", "3.1.0", "solana_sha256_hasher::hash",
            "solana_sha256_hasher::hash"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaSha256Hasher.Capabilities.catalog.forBuild
        build1).identities .hash)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile1_range_rejections :
    ((selectedProfile "singleton-solana-sha256-hasher-reviewed-bpf").applicability .hash).length =
      1 ∧
    ["3.0.999", "4.0.0", "3.2.0-rc.1"].all (fun version =>
      (((selectedProfile "singleton-solana-sha256-hasher-reviewed-bpf").forBuild { build1 with
        version := version }).identities
        .hash).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile1_build_rejections :
    ([{ build1 with package := "solana-sha256-hasher-other" },
      { build1 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build1 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build1 with target := [⟨"arch", "bpf"⟩] },
      { build1 with target := [⟨"os", "linux"⟩, ⟨"arch", "bpf"⟩, ⟨"os", "linux"⟩] },
      { build1 with target := [⟨"arch", "bpf"⟩, ⟨"os", "solana"⟩] },
      { build1 with target := [⟨"os", "linux"⟩] },
      { build1 with target := [⟨"os", "linux"⟩, ⟨"arch", "bpf"⟩, ⟨"arch", "bpf"⟩] },
      { build1 with target := [⟨"os", "linux"⟩, ⟨"arch", "unsupported-target-value"⟩] } ] : List
        Versioning.Build).all
      (fun build => (((selectedProfile "singleton-solana-sha256-hasher-reviewed-bpf").forBuild
        build).identities
        .hash).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaSha256Hasher.SyscallHashv
