/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplTransferHookInterface.Onchain
public import Solanalib.Specs.SplTransferHookInterface.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SplTransferHookInterface

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.TransferHookResolution

theorem closed_execution : FamilyHasExecution
  Solanalib.Specs.SplTransferHookInterface.onchain.add_extra_accounts_for_execute_cpi_contract
    Solanalib.Specs.SplTransferHookInterface.onchain.add_extra_accounts_for_execute_cpi_reference
      Solanalib.Specs.SplTransferHookInterface.onchain.add_extra_accounts_for_execute_cpi_sample :=
  Solanalib.Specs.SplTransferHookInterface.onchain.add_extra_accounts_for_execute_cpi_has_execution

/-- A new key retains a signer request under resolver 0.9.0. -/
theorem new_signer_retained : (deescalate [] (Instruction.accountMeta Solanalib.Runtime.Pubkey.zero
  true true)).signerByte = 1 := rfl

/-- A matching readonly alias suppresses both requested privileges. -/
theorem alias_privileges_clamped : deescalate [readonlyMeta Solanalib.Runtime.Pubkey.zero]
    (Instruction.accountMeta Solanalib.Runtime.Pubkey.zero true true) = readonlyMeta
      Solanalib.Runtime.Pubkey.zero := by
  decide +kernel

/-- POD count above capacity reaches bounds panic rather than BufferTooSmall. -/
theorem pod_capacity_panics : podAccess [1, 0, 0, 0] = .error (.inr (.podSliceBounds 1 0)) := rfl

/-- Independent matching aliases jointly retain the requested privileges. -/
theorem alias_privilege_union :
    deescalate [Instruction.accountMeta Solanalib.Runtime.Pubkey.zero true false,
      Instruction.accountMeta Solanalib.Runtime.Pubkey.zero false true]
      (Instruction.accountMeta Solanalib.Runtime.Pubkey.zero true true) =
      Instruction.accountMeta Solanalib.Runtime.Pubkey.zero true true := by decide +kernel

/-- A complete spare record is not visited when the active count is zero. -/
theorem inactive_pod_capacity_is_ignored :
    podAccess ([0, 0, 0, 0] ++ List.replicate 35 255) = .ok 0 := rfl

/-- Physical storage errors occur before the declared count can panic. -/
theorem malformed_pod_size_precedes_count :
    podAccess [255, 255, 255, 255, 0] = .error (.inl (.Custom 1)) ∧
    podAccess ([255, 255, 255, 255] ++ List.replicate 36 0) =
      .error (.inl (.Custom 2)) := ⟨rfl, rfl⟩

def missingProgramArgs : Args Sample.sampleTypes := { Sample.args with additional := [] }

def missingProgramFinal : Sample.State :=
  Sample.dropped (List.replicate 4 AccountInfo.sampleInfo) Sample.entryState

private theorem missing_program_entry :
    hookEntry Sample.sampleTypes missingProgramArgs missingProgramArgs.programId Sample.initialState
      (.returned (.error Token.Hook.incorrectHookAccount) Sample.entryState) :=
  ⟨.returned (.ok (Sample.validationKey, 251)) Sample.entryState,
    ⟨.returned (Sample.validationKey, 251) Sample.entryState, Sample.find_returns, rfl⟩, rfl⟩

/-- Missing program is checked after the PDA and releases all four moved arguments. -/
theorem missing_program_cleans_arguments :
    Solanalib.Specs.SplTransferHookInterface.onchain.add_extra_accounts_for_execute_cpi_reference
      Sample.sampleTypes Sample.initialState missingProgramArgs
      (.returned (.error Token.Hook.incorrectHookAccount) missingProgramFinal) := by
  refine ⟨.returned (.error Token.Hook.incorrectHookAccount) missingProgramFinal, ?_, rfl⟩
  refine ⟨.returned (.error Token.Hook.incorrectHookAccount) Sample.entryState,
    missing_program_entry, ?_⟩
  exact (Sample.drop_trace (List.replicate 4 AccountInfo.sampleInfo) Sample.entryState
    (by
      simp only [List.replicate, Sample.dropsReady, Sample.dropReady, Sample.rcReady];
      decide +kernel)).cleanup_returned
    Sample.sampleTypes.doubleUnwind _

/-- An error retains the actual PDA event and caller resources without a program clone. -/
theorem missing_program_preserves_effects :
    missingProgramFinal.1 = Sample.initialState.1 ∧
    missingProgramFinal.2.bytes = Sample.initialState.2.bytes ∧
    missingProgramFinal.2.metas = Sample.initialState.2.metas ∧
    missingProgramFinal.2.infos = Sample.initialState.2.infos ∧
    missingProgramFinal.2.rcOwners = [2, 2] ∧
    missingProgramFinal.2.rcEvents =
      (List.replicate 4 [AccountInfoRc.Event.drop .lamports ⟨0⟩, .drop .data ⟨1⟩]).flatten ∧
    missingProgramFinal.2.pdaCalls =
      [((hookPdaInputs missingProgramArgs missingProgramArgs.programId).seeds,
        missingProgramArgs.programId)] := by decide +kernel

end SolanalibTest.Specs.SplTransferHookInterface

namespace SolanalibTest.Specs.SplTransferHookInterface.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def onchain_add_extra_accounts_for_execute_cpiBuild : Versioning.Build where
  package := "spl-transfer-hook-interface"
  version := "0.9.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"spl-tlv-account-resolution", "0.9.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"spl-type-length-value", "0.7.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"spl-pod", "0.5.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"spl-discriminator", "0.4.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-account-info", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"bytemuck", "1.22.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def onchain_add_extra_accounts_for_execute_cpiCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.9.0; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- lower; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with version := "0.9.97" }, true),
  -- exclusive-upper; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with version := "0.10.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with version := "0.9.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-pointer_width; unresolved
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with target := [⟨"os", "solana"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with target := [⟨"pointer_width", "lin\
    ux"⟩,
    ⟨"os", "solana"⟩] }, false),
  -- missing-target-os; unresolved
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with target := [⟨"pointer_width", "64"⟩] },
    false),
  -- wrong-target-os; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with target := [⟨"pointer_width", "64"⟩,
    ⟨"os", "linux"⟩] }, false),
  -- dependency-reference-spl-tlv-account-resolution-0.9.0; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-spl-tlv-account-resolution-lower; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-spl-tlv-account-resolution-hypothetical-declaration-probe; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-tlv-account-resolution" then { dependency with version := "0\
      .9.97" }
    else dependency)) }, true),
  -- dependency-spl-tlv-account-resolution-exclusive-upper; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-tlv-account-resolution" then { dependency with version := "0\
      .10.0" }
    else dependency)) }, false),
  -- dependency-spl-tlv-account-resolution-unlisted-prerelease; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-tlv-account-resolution" then { dependency with version :=
    "0.9.0-rc.1" } else dependency)) }, false),
  -- missing-dependency-spl-tlv-account-resolution; unresolved
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.filter (fun dependency =>
    dependency.package != "spl-tlv-account-resolution")) }, false),
  -- wrong-dependency-origin-spl-tlv-account-resolution; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "spl-tlv-account-resolution" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-spl-tlv-account-resolution; ValueError containing Ambiguous dependency
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies ++ [⟨
    "spl-tlv-account-resolution", "0.9.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-spl-type-length-value-0.7.0; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-spl-type-length-value-lower; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-spl-type-length-value-hypothetical-declaration-probe; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-type-length-value" then { dependency with version := "0.7.97" } else
    dependency)) }, true),
  -- dependency-spl-type-length-value-exclusive-upper; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-type-length-value" then { dependency with version := "0.8.0" } else
    dependency)) }, false),
  -- dependency-spl-type-length-value-unlisted-prerelease; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-type-length-value" then { dependency with version := "0.7.0-\
      rc.1" }
    else dependency)) }, false),
  -- missing-dependency-spl-type-length-value; unresolved
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.filter (fun dependency =>
    dependency.package != "spl-type-length-value")) }, false),
  -- wrong-dependency-origin-spl-type-length-value; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "spl-type-length-value" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-spl-type-length-value; ValueError containing Ambiguous dependency
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies ++ [⟨
    "spl-type-length-value", "0.7.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-spl-pod-0.5.0; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-reference-spl-pod-0.5.1; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.5.1" } else dependency))
    }, true),
  -- dependency-spl-pod-lower; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-spl-pod-hypothetical-declaration-probe; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.5.97" } else dependency))
    }, true),
  -- dependency-spl-pod-exclusive-upper; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.6.0" } else dependency))
    }, false),
  -- dependency-spl-pod-unlisted-prerelease; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.5.0-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-spl-pod; unresolved
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.filter (fun dependency =>
    dependency.package != "spl-pod")) }, false),
  -- wrong-dependency-origin-spl-pod; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "spl-pod" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-spl-pod; ValueError containing Ambiguous dependency
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies ++ [⟨
    "spl-pod", "0.5.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- dependency-reference-spl-discriminator-0.4.1; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-spl-discriminator-lower; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-spl-discriminator-hypothetical-declaration-probe; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-discriminator" then { dependency with version := "0.4.98" } else
    dependency)) }, true),
  -- dependency-spl-discriminator-exclusive-upper; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-discriminator" then { dependency with version := "0.5.0" } else
    dependency)) }, false),
  -- dependency-spl-discriminator-unlisted-prerelease; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-discriminator" then { dependency with version := "0.4.1-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-spl-discriminator; unresolved
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.filter (fun dependency =>
    dependency.package != "spl-discriminator")) }, false),
  -- wrong-dependency-origin-spl-discriminator; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "spl-discriminator" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-spl-discriminator; ValueError containing Ambiguous dependency
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies ++ [⟨
    "spl-discriminator", "0.4.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-account-info-2.1.0; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-reference-solana-account-info-2.2.1; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-account-info" then { dependency with version := "2.2.1" } else
    dependency)) }, true),
  -- dependency-reference-solana-account-info-2.3.0; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-account-info" then { dependency with version := "2.3.0" } else
    dependency)) }, true),
  -- dependency-solana-account-info-lower; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-solana-account-info-hypothetical-declaration-probe; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-account-info" then { dependency with version := "2.1.97" } else
    dependency)) }, true),
  -- dependency-solana-account-info-exclusive-upper; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-account-info" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-account-info-unlisted-prerelease; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-account-info" then { dependency with version := "2.1.0-rc\
      .1" }
    else dependency)) }, false),
  -- missing-dependency-solana-account-info; unresolved
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-account-info")) }, false),
  -- wrong-dependency-origin-solana-account-info; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-account-info" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-account-info; ValueError containing Ambiguous dependency
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies ++ [⟨
    "solana-account-info", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.3.3" } else
    dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.2.98" } else
    dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.2.1-rc.\
      1" }
    else dependency)) }, false),
  -- missing-dependency-solana-instruction; unresolved
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.3.0" } else
    dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.4.0" } else
    dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.98" } else
    dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.1.0; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-reference-solana-program-error-2.2.0; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.2.0" } else
    dependency)) }, true),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.2.1" } else
    dependency)) }, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.2.2" } else
    dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.1.97" } else
    dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.1.0-r\
      c.1" }
    else dependency)) }, false),
  -- missing-dependency-solana-program-error; unresolved
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies ++ [⟨
    "solana-program-error", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-bytemuck-1.22.0; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-reference-bytemuck-1.24.0; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "bytemuck" then { dependency with version := "1.24.0" } else dependency))
    }, true),
  -- dependency-reference-bytemuck-1.25.2; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "bytemuck" then { dependency with version := "1.25.2" } else dependency))
    }, true),
  -- dependency-bytemuck-lower; eligible
  (onchain_add_extra_accounts_for_execute_cpiBuild, true),
  -- dependency-bytemuck-hypothetical-declaration-probe; eligible
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "bytemuck" then { dependency with version := "1.22.97" } else
    dependency)) }, true),
  -- dependency-bytemuck-exclusive-upper; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "bytemuck" then { dependency with version := "2.0.0" } else dependency))
    }, false),
  -- dependency-bytemuck-unlisted-prerelease; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "bytemuck" then { dependency with version := "1.22.0-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-bytemuck; unresolved
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.filter (fun dependency =>
    dependency.package != "bytemuck")) }, false),
  -- wrong-dependency-origin-bytemuck; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "bytemuck" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-bytemuck; ValueError containing Ambiguous dependency
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies ++ [⟨
    "bytemuck", "1.22.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-0.8.999; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with version := "0.8.999" }, false),
  -- dependency-spl-tlv-account-resolution-below-lower-bound-fixture-0.8.999; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-tlv-account-resolution" then { dependency with version := "0\
      .8.999"
    } else dependency)) }, false),
  -- dependency-spl-type-length-value-below-lower-bound-fixture-0.6.999; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-type-length-value" then { dependency with version := "0.6.99\
      9" }
    else dependency)) }, false),
  -- dependency-spl-pod-below-lower-bound-fixture-0.4.999; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.4.999" } else dependency))
    }, false),
  -- dependency-spl-discriminator-below-lower-bound-fixture-0.4.0; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-discriminator" then { dependency with version := "0.4.0" } else
    dependency)) }, false),
  -- dependency-solana-account-info-below-lower-bound-fixture-2.0.999; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-account-info" then { dependency with version := "2.0.999" } else
    dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.2.0" } else
    dependency)) }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.0" } else
    dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.0.999; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.0.999" } else
    dependency)) }, false),
  -- dependency-bytemuck-below-lower-bound-fixture-1.21.999; unsupported
  ({ onchain_add_extra_accounts_for_execute_cpiBuild with dependencies :=
    (onchain_add_extra_accounts_for_execute_cpiBuild.dependencies.map (fun dependency => if
    dependency.package == "bytemuck" then { dependency with version := "1.21.999" } else
    dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem onchain_add_extra_accounts_for_execute_cpi_profile_controls :
    onchain_add_extra_accounts_for_execute_cpiCases.all (fun test =>
      (((Solanalib.Specs.SplTransferHookInterface.Capabilities.catalog.applicability
        .onchain_add_extra_accounts_for_execute_cpi).any
        (fun profile => ["transfer-hook-interface-0.9.0-spl-resolution-0.9.0-solana64"].contains
          profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem onchain_add_extra_accounts_for_execute_cpi_callable_identities :
    ["0.9.0", "0.9.97"].all (fun version =>
      (((Solanalib.Specs.SplTransferHookInterface.Capabilities.catalog.forBuild
        { onchain_add_extra_accounts_for_execute_cpiBuild with version := version }).identities
          .onchain_add_extra_accounts_for_execute_cpi).eraseDups ==
        [⟨"spl-transfer-hook-interface", version,
          "spl_transfer_hook_interface::onchain::add_extra_accounts_for_execute_cpi",
          "spl_transfer_hook_interface::onchain::add_extra_accounts_for_execute_cpi"⟩])) = true :=
          by
  decide +kernel

end SolanalibTest.Specs.SplTransferHookInterface.Pr575Compatibility
