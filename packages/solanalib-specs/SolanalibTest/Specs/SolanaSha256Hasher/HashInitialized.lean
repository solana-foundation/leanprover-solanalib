/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaSha256Hasher.HashInitialized
public import Solanalib.Specs.SolanaSha256Hasher.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SolanaSha256Hasher.HashInitialized

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem empty_hash_keeps_single_slice :
    Hash.Initialized.request [[]] ≠ Hash.Initialized.request [] := by
  intro same
  have lengths := congrArg (fun request => request.slices.length) same
  cases lengths

theorem no_write_error_returns_zero :
    Solanalib.Specs.SolanaSha256Hasher.zero_initialized.hash_run Hash.Initialized.sample () [9]
      (.returned Hash.zero ()) :=
  ⟨.returned ⟨7, Hash.zero⟩ (), rfl, rfl⟩

theorem initialized_request_differs :
    (Hash.Initialized.request [[1]]).output ≠ (Hash.Syscall.request [[1]]).output := by decide

def partialHash : Hash.Value := ⟨255 :: List.replicate 31 0, by simp⟩

def partialWrite : Hash.Initialized.Index where
  State := List Hash.Syscall.Request
  Unwind := Nat
  Terminal := Nat
  provider := Callback.ofFunction fun before request =>
    .returned ⟨7, partialHash⟩ (before ++ [request])

/-- A nonzero status keeps the partially changed buffer, its zero tail and the
actual singleton request in the after-state of the provider. -/
theorem partial_write_retains_tail_and_request :
    Solanalib.Specs.SolanaSha256Hasher.zero_initialized.hash_run partialWrite [] []
      (.returned partialHash [Hash.Initialized.request [[]]]) :=
  ⟨.returned ⟨7, partialHash⟩ [Hash.Initialized.request [[]]], rfl, rfl⟩

def unwinding : Hash.Initialized.Index where
  State := Nat
  Unwind := Nat
  Terminal := Nat
  provider := Callback.ofFunction fun before _ => .unwound (5 : Nat) (before + 7)

theorem unwind_retains_provider_state (before : Nat) (bytes : Solanalib.Runtime.Bytes) :
    Solanalib.Specs.SolanaSha256Hasher.zero_initialized.hash_run unwinding before bytes
      (.unwound (5 : Nat) (before + 7)) :=
  ⟨.unwound (5 : Nat) (before + 7), rfl, rfl⟩

def terminating : Hash.Initialized.Index :=
  { unwinding with provider := Callback.ofFunction fun (_ : Nat) _ => .terminated (9 : Nat) }

theorem terminal_exit_has_no_returned_buffer :
    Solanalib.Specs.SolanaSha256Hasher.zero_initialized.hashv_run terminating (3 : Nat) [[1], [2]]
      (.terminated (9 : Nat)) :=
  ⟨.terminated (9 : Nat), rfl, rfl⟩

def cratesIo : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def selectedBuild : Versioning.Build where
  package := "solana-sha256-hasher"
  version := "2.3.0"
  source := cratesIo
  target := [⟨"os", "solana"⟩]
  dependencies := [⟨"solana-hash", "2.3.0", cratesIo⟩,
    ⟨"solana-define-syscall", "2.3.0", cratesIo⟩]

theorem reviewed_build_admitted :
    (Solanalib.Specs.SolanaSha256Hasher.Capabilities.catalog.forBuild selectedBuild).identities
      .zero_initialized_hash ≠ [] :=
  by decide +kernel

def hashMembers : List (Solanalib.Specs.SolanaSha256Hasher.Capabilities.Key × String) :=
  [(.zero_initialized_hash, "hash"), (.zero_initialized_hashv, "hashv")]

/-- Compatible callers may resolve the field and syscall providers independently
of the exact native recording. Both wrapper identities keep the release of the caller. -/
theorem compatible_hash_identities :
    ["2.3.0", "2.3.1", "2.9.0"].all (fun version => hashMembers.all (fun (key, name) =>
      decide ((Solanalib.Specs.SolanaSha256Hasher.Capabilities.catalog.forBuild
        { selectedBuild with
          version := version
          dependencies := [⟨"solana-hash", "2.3.1", cratesIo⟩,
            ⟨"solana-define-syscall", "2.3.1", cratesIo⟩] }).identities key =
        [⟨"solana-sha256-hasher", version, "solana_sha256_hasher::" ++ name,
          "solana_sha256_hasher::" ++ name⟩]))) = true := by
  decide +kernel

theorem outside_initialized_hash_range_rejected :
    ["2.2.1", "3.0.0", "2.3.1-rc.1"].all (fun version => hashMembers.all (fun (key, _) =>
      decide ((Solanalib.Specs.SolanaSha256Hasher.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities key = []))) = true := by
  decide +kernel

theorem host_build_rejected :
    (Solanalib.Specs.SolanaSha256Hasher.Capabilities.catalog.forBuild
      { selectedBuild with
        version := "2.3.1"
        target := [⟨"os", "linux"⟩] }).identities .zero_initialized_hash = [] :=
  by decide +kernel

theorem changed_hash_dependency_rejected :
    (Solanalib.Specs.SolanaSha256Hasher.Capabilities.catalog.forBuild
      { selectedBuild with
        version := "2.3.1"
        dependencies := [⟨"solana-hash", "4.3.0", cratesIo⟩,
        ⟨"solana-define-syscall", "2.3.0", cratesIo⟩] }).identities .zero_initialized_hash = [] :=
  by decide +kernel

theorem changed_syscall_dependency_rejected :
    (Solanalib.Specs.SolanaSha256Hasher.Capabilities.catalog.forBuild
      { selectedBuild with
        version := "2.3.1"
        dependencies := [⟨"solana-hash", "2.3.0", cratesIo⟩,
        ⟨"solana-define-syscall", "4.0.1", cratesIo⟩] }).identities .zero_initialized_hashv = [] :=
  by decide +kernel

theorem missing_hash_providers_rejected :
    (Solanalib.Specs.SolanaSha256Hasher.Capabilities.catalog.forBuild
      { selectedBuild with version := "2.3.1", dependencies := [] }).identities
        .zero_initialized_hashv = [] := by decide +kernel

end SolanalibTest.Specs.SolanaSha256Hasher.HashInitialized
