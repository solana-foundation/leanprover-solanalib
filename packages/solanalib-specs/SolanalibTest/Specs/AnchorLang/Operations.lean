/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.Core.AnchorOperations
public import Solanalib.Specs.AnchorLang
public import Solanalib.Specs.AnchorLang.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.Operations

open Solanalib.Contracts.Model Solanalib.Specs.Core

def registrySource : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def reviewedBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.32.1"
  source := registrySource
  target := [⟨"pointer_width", "64"⟩]
  dependencies := [⟨"anchor-syn", "0.32.1", registrySource⟩,
    ⟨"solana-program-error", "2.2.2", registrySource⟩]

def operationKeys : List Solanalib.Specs.AnchorLang.Capabilities.Key := [
  .context_Context_new,
  .context_CpiContext_AccountInfoProgram_new,
  .context_CpiContext_AccountInfoProgram_new_with_signer,
  .context_CpiContext_AccountInfoProgram_with_signer,
  .bpf_writer_BpfWriter_write_all,
  .error_Error_GenericProgram_with_account_name,
  .error_Error_GenericProgram_with_pubkeys,
  .error_Error_GenericProgram_with_values,
  .error_Error_from_error_code,
  .error_Error_log,
  .error_ErrorCode_name]

abbrev catalog := Solanalib.Specs.AnchorLang.Capabilities.catalog

/-- Every selected operation has a source identity at the complete reviewed
build. An empty requested capability set cannot establish this check. -/
theorem reviewed_build_admits_all_eleven_operations :
    operationKeys.length = 11 ∧ operationKeys.all (fun key =>
      !((catalog.forBuild reviewedBuild).identities key).isEmpty) = true := by
  decide +kernel

/-- Higher version numbers do not inherit admission. The selected 0.29.0, 1.0.2
and 1.1.2 operations below have their own explicit source profiles. -/
theorem other_anchor_releases_do_not_inherit_admission :
    ["0.27.0", "0.29.0", "1.0.2", "1.1.2"].all (fun version =>
      (operationKeys.filter (fun key => decide (((version ≠ "1.1.2" ∨
        key ∉ [.context_Context_new, .context_CpiContext_AccountInfoProgram_new,
          .context_CpiContext_AccountInfoProgram_with_signer, .bpf_writer_BpfWriter_write_all]) ∧
        (version ≠ "1.0.2" ∨ key ∉ [.context_Context_new,
          .context_CpiContext_AccountInfoProgram_new,
          .context_CpiContext_AccountInfoProgram_with_signer,
          .error_Error_GenericProgram_with_account_name]) ∧
        (version ≠ "0.29.0" ∨ key ∉ [.context_Context_new,
          .context_CpiContext_AccountInfoProgram_new,
          .context_CpiContext_AccountInfoProgram_new_with_signer,
          .context_CpiContext_AccountInfoProgram_with_signer,
          .bpf_writer_BpfWriter_write_all,
          .error_Error_GenericProgram_with_account_name,
          .error_Error_GenericProgram_with_pubkeys,
          .error_Error_GenericProgram_with_values])) ∧
        (version ≠ "0.27.0" ∨ key ∉ [.context_Context_new,
          .context_CpiContext_AccountInfoProgram_new,
          .context_CpiContext_AccountInfoProgram_new_with_signer,
          .context_CpiContext_AccountInfoProgram_with_signer,
          .bpf_writer_BpfWriter_write_all])))).all
        (fun key =>
          ((catalog.forBuild { reviewedBuild with version }).identities key).isEmpty)) = true := by
  decide +kernel

/-- The 0.29.0 source profiles admit the eight shared context, writer and
annotation operations. Its diagnostic names, codes and logger retain their
separate complete families. -/
theorem anchor_0_29_0_selects_only_reviewed_shared_operations :
    operationKeys.filter (fun key => !((catalog.forBuild
      { reviewedBuild with version := "0.29.0" }).identities key).isEmpty) =
      [.context_Context_new, .context_CpiContext_AccountInfoProgram_new,
        .context_CpiContext_AccountInfoProgram_new_with_signer,
        .context_CpiContext_AccountInfoProgram_with_signer,
        .bpf_writer_BpfWriter_write_all, .error_Error_GenericProgram_with_account_name,
        .error_Error_GenericProgram_with_pubkeys, .error_Error_GenericProgram_with_values] := by
  rfl

/-- The 1.0.2 profiles admit exactly three context operations and the generic
account-name annotation from this list. Diagnostic tables and logging use
their separately named contracts and exact dependency profiles. -/
theorem anchor_1_0_2_selects_only_reviewed_shared_operations :
    operationKeys.filter (fun key => !((catalog.forBuild
      { reviewedBuild with version := "1.0.2" }).identities key).isEmpty) =
      [.context_Context_new,
        .context_CpiContext_AccountInfoProgram_new,
        .context_CpiContext_AccountInfoProgram_with_signer,
        .error_Error_GenericProgram_with_account_name] := by
  rfl

/-- The new 1.1.2 source profiles select precisely the four shared operations
in this list; the other signatures and diagnostic dependencies stay separate. -/
theorem modern_anchor_selects_only_reviewed_shared_operations :
    operationKeys.filter (fun key => !((catalog.forBuild
      { reviewedBuild with version := "1.1.2" }).identities key).isEmpty) =
      [.context_Context_new, .context_CpiContext_AccountInfoProgram_new,
        .context_CpiContext_AccountInfoProgram_with_signer,
        .bpf_writer_BpfWriter_write_all] := by
  rfl

/-- The inline-error release shares precisely these five context/writer
operations from this list. Its annotation, error-code and logging contracts
remain separate from the boxed error families. -/
theorem inline_error_anchor_selects_only_reviewed_shared_operations :
    operationKeys.filter (fun key => !((catalog.forBuild
      { reviewedBuild with version := "0.27.0" }).identities key).isEmpty) =
      [.context_Context_new,
        .context_CpiContext_AccountInfoProgram_new,
        .context_CpiContext_AccountInfoProgram_new_with_signer,
        .context_CpiContext_AccountInfoProgram_with_signer,
        .bpf_writer_BpfWriter_write_all] := by
  rfl

theorem matching_version_from_another_source_is_rejected :
    operationKeys.all (fun key => ((catalog.forBuild
      { reviewedBuild with source := ⟨"git", "https://github.com/coral-xyz/anchor",
          "0123456789abcdef0123456789abcdef01234567"⟩ }).identities key).isEmpty) = true := by
  decide +kernel

/-- Unknown, narrow, and conflicting pointer-width facts cannot select the reviewed u64-to-usize
behavior of the writer. -/
theorem writer_needs_one_known_64_bit_pointer_width :
    (catalog.forBuild { reviewedBuild with target := [] }).identities
      .bpf_writer_BpfWriter_write_all = [] ∧
    (catalog.forBuild { reviewedBuild with target := [⟨"pointer_width", "32"⟩] }).identities
      .bpf_writer_BpfWriter_write_all = [] ∧
    (catalog.forBuild { reviewedBuild with
      target := [⟨"pointer_width", "64"⟩, ⟨"pointer_width", "32"⟩] }).identities
      .bpf_writer_BpfWriter_write_all = [] := by
  decide +kernel

theorem missing_macro_provider_rejects_both_generated_operations :
    (catalog.forBuild { reviewedBuild with
      dependencies := [⟨"solana-program-error", "2.2.2", registrySource⟩] }).identities
      .error_ErrorCode_name = [] ∧
    (catalog.forBuild { reviewedBuild with
      dependencies := [⟨"solana-program-error", "2.2.2", registrySource⟩] }).identities
      .error_Error_from_error_code = [] := by
  decide +kernel

theorem wrong_macro_release_rejects_both_generated_operations :
    (catalog.forBuild { reviewedBuild with
      dependencies := [⟨"anchor-syn", "0.29.0", registrySource⟩,
        ⟨"solana-program-error", "2.2.2", registrySource⟩] }).identities
      .error_ErrorCode_name = [] ∧
    (catalog.forBuild { reviewedBuild with
      dependencies := [⟨"anchor-syn", "0.29.0", registrySource⟩,
        ⟨"solana-program-error", "2.2.2", registrySource⟩] }).identities
      .error_Error_from_error_code = [] := by
  decide +kernel

/-- the legacy Borsh payload and rendering of Logging are selected by the actual
resolved ProgramError dependency, not the Anchor package version alone. -/
theorem logger_needs_the_reviewed_program_error_dependency :
    (catalog.forBuild { reviewedBuild with
      dependencies := [⟨"anchor-syn", "0.32.1", registrySource⟩] }).identities
      .error_Error_log = [] ∧
    (catalog.forBuild { reviewedBuild with
      dependencies := [⟨"anchor-syn", "0.32.1", registrySource⟩,
        ⟨"solana-program-error", "3.0.1", registrySource⟩] }).identities
      .error_Error_log = [] := by
  decide +kernel

/-- One matching candidate cannot hide an ambiguous dependency selection. -/
theorem duplicate_dependency_candidates_reject_the_full_build :
    let ambiguous := { reviewedBuild with dependencies := reviewedBuild.dependencies ++
      [⟨"anchor-syn", "0.29.0", registrySource⟩,
       ⟨"solana-program-error", "3.0.1", registrySource⟩] }
    (catalog.forBuild ambiguous).identities .error_ErrorCode_name = [] ∧
    (catalog.forBuild ambiguous).identities .error_Error_from_error_code = [] ∧
    (catalog.forBuild ambiguous).identities .error_Error_log = [] := by
  decide +kernel


/-- The last version is a compatible-patch selector fixture, not another
inspected source or native recording. -/
def identityVersions : List String :=
  ["0.32.1", "0.32.2", "0.32.3", "0.32.4"]

def buildAt (version : String) : Versioning.Build :=
  { reviewedBuild with
    version := version
    dependencies := [⟨"anchor-syn", version, registrySource⟩,
      ⟨"solana-program-error", "2.2.2", registrySource⟩] }

def otherSources : List Versioning.Source := [
  ⟨"git", "https://github.com/coral-xyz/anchor",
    "0123456789abcdef0123456789abcdef01234567"⟩,
  ⟨"registry", "https://example.invalid/registry-index", ""⟩]

/-- The source identity retains the queried release and the complete Context
or CpiContext path, including the generic parameters of the source. -/
theorem context_identities_keep_the_selected_release :
    identityVersions.all (fun version =>
      let selected := catalog.forBuild (buildAt version)
      decide (
        selected.identities .context_Context_new =
          [⟨"anchor-lang", version,
            "anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new",
            "anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new"⟩] ∧
        selected.identities .context_CpiContext_AccountInfoProgram_new =
          [⟨"anchor-lang", version,
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new",
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new"⟩] ∧
        selected.identities .context_CpiContext_AccountInfoProgram_new_with_signer =
          [⟨"anchor-lang", version,
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer",
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer"⟩] ∧
        selected.identities .context_CpiContext_AccountInfoProgram_with_signer =
          [⟨"anchor-lang", version,
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer",
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer"⟩])) = true := by
  decide +kernel

/-- The writer is the concrete std::io::Write implementation, not an inherent
method or a source identity relabeled with the reference version. -/
theorem writer_identity_keeps_the_selected_release :
    identityVersions.all (fun version =>
      decide ((catalog.forBuild (buildAt version)).identities
        .bpf_writer_BpfWriter_write_all =
        [⟨"anchor-lang", version, "std::io::Write::write_all",
          "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as std::io::Write>::write_all"⟩])) = true
            := by
  decide +kernel

/-- GenericProgram names the Lean representation variant; the Rust methods
remain defined on anchor_lang::error::Error. -/
theorem annotation_identities_keep_the_selected_release :
    identityVersions.all (fun version =>
      let selected := catalog.forBuild (buildAt version)
      decide (
        selected.identities .error_Error_GenericProgram_with_account_name =
          [⟨"anchor-lang", version, "anchor_lang::error::Error::with_account_name",
            "anchor_lang::error::Error::with_account_name"⟩] ∧
        selected.identities .error_Error_GenericProgram_with_pubkeys =
          [⟨"anchor-lang", version, "anchor_lang::error::Error::with_pubkeys",
            "anchor_lang::error::Error::with_pubkeys"⟩] ∧
        selected.identities .error_Error_GenericProgram_with_values =
          [⟨"anchor-lang", version, "anchor_lang::error::Error::with_values",
            "anchor_lang::error::Error::with_values"⟩])) = true := by
  decide +kernel

/-- Macro expansion does not make anchor-syn the defining package of the
emitted ErrorCode method or From implementation. -/
theorem generated_error_identities_keep_the_selected_release :
    identityVersions.all (fun version =>
      let selected := catalog.forBuild (buildAt version)
      decide (
        selected.identities .error_ErrorCode_name =
          [⟨"anchor-lang", version, "anchor_lang::error::ErrorCode::name",
            "anchor_lang::error::ErrorCode::name"⟩] ∧
        selected.identities .error_Error_from_error_code =
          [⟨"anchor-lang", version, "core::convert::From::from",
            "<anchor_lang::error::Error as \
              core::convert::From<anchor_lang::error::ErrorCode>>::from"⟩])) = true := by
  decide +kernel

theorem logger_identity_keeps_the_selected_release :
    identityVersions.all (fun version =>
      decide ((catalog.forBuild (buildAt version)).identities .error_Error_log =
        [⟨"anchor-lang", version, "anchor_lang::error::Error::log",
          "anchor_lang::error::Error::log"⟩])) = true := by
  decide +kernel

/-- These are the bounds of the new 0.32 line, with prereleases excluded.
The older-release controls above remain separate. -/
theorem anchor_minor_bounds_and_prerelease_are_rejected :
    ["0.32.0", "0.33.0", "0.32.4-rc.1"].all (fun version =>
      operationKeys.all (fun key =>
        ((catalog.forBuild { reviewedBuild with version }).identities key).isEmpty)) = true := by
  decide +kernel

/-- Range membership cannot substitute another crate, git origin or registry. -/
theorem compatible_patch_keeps_the_crate_and_source_gate :
    operationKeys.all (fun key => ((catalog.forBuild
      { buildAt "0.32.4" with package := "anchor-lang-error" }).identities key).isEmpty) = true ∧
    otherSources.all (fun source => operationKeys.all (fun key => ((catalog.forBuild
      { buildAt "0.32.4" with source }).identities key).isEmpty)) = true := by
  decide +kernel

/-- A compatible provider may have a different resolved patch. The generated
operations still carry the actual Anchor package version. -/
theorem compatible_macro_provider_preserves_the_anchor_identity :
    ["0.32.2", "0.32.3", "0.32.4"].all (fun version =>
      let selected := catalog.forBuild { reviewedBuild with dependencies :=
        [⟨"anchor-syn", version, registrySource⟩,
         ⟨"solana-program-error", "2.2.2", registrySource⟩] }
      decide (
        selected.identities .error_ErrorCode_name =
          [⟨"anchor-lang", "0.32.1", "anchor_lang::error::ErrorCode::name",
            "anchor_lang::error::ErrorCode::name"⟩] ∧
        selected.identities .error_Error_from_error_code =
          [⟨"anchor-lang", "0.32.1", "core::convert::From::from",
            "<anchor_lang::error::Error as \
              core::convert::From<anchor_lang::error::ErrorCode>>::from"⟩])) = true := by
  decide +kernel

theorem macro_provider_bounds_and_prerelease_are_rejected :
    ["0.32.0", "0.33.0", "0.32.4-rc.1"].all (fun version =>
      let selected := catalog.forBuild { reviewedBuild with dependencies :=
        [⟨"anchor-syn", version, registrySource⟩,
         ⟨"solana-program-error", "2.2.2", registrySource⟩] }
      decide (selected.identities .error_ErrorCode_name = [] ∧
        selected.identities .error_Error_from_error_code = [])) = true := by
  decide +kernel

/-- 2.2.3 is a compatible-dependency fixture. It must not replace the defining
Anchor package/version in the selected logger identity. -/
theorem compatible_program_error_preserves_the_anchor_identity :
    (catalog.forBuild { reviewedBuild with dependencies :=
      [⟨"anchor-syn", "0.32.1", registrySource⟩,
       ⟨"solana-program-error", "2.2.3", registrySource⟩] }).identities .error_Error_log =
      [⟨"anchor-lang", "0.32.1", "anchor_lang::error::Error::log",
        "anchor_lang::error::Error::log"⟩] := by
  decide +kernel

/-- The dependency range does not admit the payloadless 3.x ProgramError. -/
theorem program_error_bounds_and_prerelease_are_rejected :
    ["2.2.1", "3.0.0", "3.0.1", "2.2.3-rc.1"].all (fun version =>
      ((catalog.forBuild { reviewedBuild with dependencies :=
        [⟨"anchor-syn", "0.32.1", registrySource⟩,
         ⟨"solana-program-error", version, registrySource⟩] }).identities
        .error_Error_log).isEmpty) = true := by
  decide +kernel

/-- The origin of each required dependency is checked independently while the
other selected dependency remains valid. -/
theorem required_dependency_origins_are_rejected :
    otherSources.all (fun source =>
      let macroOrigin := catalog.forBuild { reviewedBuild with dependencies :=
        [⟨"anchor-syn", "0.32.1", source⟩,
         ⟨"solana-program-error", "2.2.2", registrySource⟩] }
      let errorOrigin := catalog.forBuild { reviewedBuild with dependencies :=
        [⟨"anchor-syn", "0.32.1", registrySource⟩,
         ⟨"solana-program-error", "2.2.2", source⟩] }
      decide (macroOrigin.identities .error_ErrorCode_name = [] ∧
        macroOrigin.identities .error_Error_from_error_code = [] ∧
        errorOrigin.identities .error_Error_log = [])) = true := by
  decide +kernel

/-- Two individually compatible candidates still do not identify the actual
resolved dependency. Check the two package ambiguities independently. -/
theorem compatible_dependency_candidates_are_still_ambiguous :
    let macroCandidates := catalog.forBuild { reviewedBuild with dependencies :=
      [⟨"anchor-syn", "0.32.1", registrySource⟩,
       ⟨"anchor-syn", "0.32.3", registrySource⟩,
       ⟨"solana-program-error", "2.2.2", registrySource⟩] }
    let errorCandidates := catalog.forBuild { reviewedBuild with dependencies :=
      [⟨"anchor-syn", "0.32.1", registrySource⟩,
       ⟨"solana-program-error", "2.2.2", registrySource⟩,
       ⟨"solana-program-error", "2.2.3", registrySource⟩] }
    macroCandidates.identities .error_ErrorCode_name = [] ∧
    macroCandidates.identities .error_Error_from_error_code = [] ∧
    errorCandidates.identities .error_Error_log = [] := by
  decide +kernel

/-- Context moves and generic error annotations do not reach the cast of the writer, the
ProgramError interpretation used by logging or error-code generation. -/
theorem moves_and_annotations_need_no_unrelated_build_facts :
    let selected := catalog.forBuild { reviewedBuild with
      target := [⟨"pointer_width", "32"⟩]
      dependencies := [] }
    [Solanalib.Specs.AnchorLang.Capabilities.Key.context_Context_new,
      .context_CpiContext_AccountInfoProgram_new,
      .context_CpiContext_AccountInfoProgram_new_with_signer,
      .context_CpiContext_AccountInfoProgram_with_signer,
      .error_Error_GenericProgram_with_account_name,
      .error_Error_GenericProgram_with_pubkeys,
      .error_Error_GenericProgram_with_values].all (fun key =>
        !(selected.identities key).isEmpty) = true := by
  decide +kernel

theorem writer_needs_no_macro_or_logger_dependency :
    (catalog.forBuild { reviewedBuild with dependencies := [] }).identities
      .bpf_writer_BpfWriter_write_all =
      [⟨"anchor-lang", "0.32.1", "std::io::Write::write_all",
        "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as std::io::Write>::write_all"⟩] := by
  decide +kernel

/-- Unknown features are admitted by the reference identity tests. Enabling
the inspected debug/IDL helpers does not replace either generated method. -/
theorem optional_helpers_do_not_gate_the_generated_methods :
    let selected := catalog.forBuild { reviewedBuild with
      features := some ["anchor-debug", "idl-build"]
      targetFeatures := some [] }
    selected.identities .error_ErrorCode_name =
      [⟨"anchor-lang", "0.32.1", "anchor_lang::error::ErrorCode::name",
        "anchor_lang::error::ErrorCode::name"⟩] ∧
    selected.identities .error_Error_from_error_code =
      [⟨"anchor-lang", "0.32.1", "core::convert::From::from",
        "<anchor_lang::error::Error as \
          core::convert::From<anchor_lang::error::ErrorCode>>::from"⟩]
          := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.Operations

namespace SolanalibTest.Specs.AnchorLang.Operations.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def error_Error_from_io_errorBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.32.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-program-error", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def error_Error_from_io_errorCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.32.0; eligible
  (error_Error_from_io_errorBuild, true),
  -- inspected-reference-0.32.1; eligible
  ({ error_Error_from_io_errorBuild with version := "0.32.1" }, true),
  -- inspected-reference-0.32.2; eligible
  ({ error_Error_from_io_errorBuild with version := "0.32.2" }, true),
  -- inspected-reference-0.32.3; eligible
  ({ error_Error_from_io_errorBuild with version := "0.32.3" }, true),
  -- lower; eligible
  (error_Error_from_io_errorBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ error_Error_from_io_errorBuild with version := "0.32.97" }, true),
  -- exclusive-upper; unsupported
  ({ error_Error_from_io_errorBuild with version := "0.33.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ error_Error_from_io_errorBuild with version := "0.32.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ error_Error_from_io_errorBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ error_Error_from_io_errorBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- dependency-reference-solana-program-error-2.1.0; eligible
  (error_Error_from_io_errorBuild, true),
  -- dependency-reference-solana-program-error-2.2.0; eligible
  ({ error_Error_from_io_errorBuild with dependencies :=
    (error_Error_from_io_errorBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, true),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  ({ error_Error_from_io_errorBuild with dependencies :=
    (error_Error_from_io_errorBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1" } else dependency)) }, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ error_Error_from_io_errorBuild with dependencies :=
    (error_Error_from_io_errorBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (error_Error_from_io_errorBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ error_Error_from_io_errorBuild with dependencies :=
    (error_Error_from_io_errorBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.1.97" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ error_Error_from_io_errorBuild with dependencies :=
    (error_Error_from_io_errorBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ error_Error_from_io_errorBuild with dependencies :=
    (error_Error_from_io_errorBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.1.0-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ error_Error_from_io_errorBuild with dependencies :=
    (error_Error_from_io_errorBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ error_Error_from_io_errorBuild with dependencies :=
    (error_Error_from_io_errorBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ error_Error_from_io_errorBuild with dependencies :=
    (error_Error_from_io_errorBuild.dependencies ++ [⟨
    "solana-program-error", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-0.31.999; unsupported
  ({ error_Error_from_io_errorBuild with version := "0.31.999" }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.0.999; unsupported
  ({ error_Error_from_io_errorBuild with dependencies :=
    (error_Error_from_io_errorBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.0.999" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem error_Error_from_io_error_profile_controls :
    error_Error_from_io_errorCases.all (fun test =>
      (((Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability
        .error_Error_from_io_error).any
        (fun profile => ["anchor-lang-0.32.1-io"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem error_Error_from_io_error_callable_identities :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "0.32.97"].all (fun version =>
      (((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        { error_Error_from_io_errorBuild with version := version }).identities
          .error_Error_from_io_error).eraseDups ==
        [⟨"anchor-lang", version, "core::convert::From::from",
          "<anchor_lang::error::Error as core::convert::From<std::io::error::Error>>::from"⟩])) =
          true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.Operations.Pr575Compatibility

namespace SolanalibTest.Specs.AnchorLang.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.AnchorLang.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

abbrev Row := Solanalib.Specs.AnchorLang.Capabilities.Key × String × String × String

def identifies (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 =
    [⟨build.package, build.version, row.2.2.1, row.2.2.2⟩])

def rejects (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 = [])

def registry : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def dependencyVersion (build : Build) (package version : String) : Build :=
  { build with dependencies := (build.dependencies.map (fun dep =>
      if dep.package == package then { dep with version := version } else dep)) }

def build0 : Build where
  package := "anchor-lang"
  version := "1.1.2"
  source := registry

def rows0 : List Row := [
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:0",
      "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:1",
      "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:2",
      "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::program::Program<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:3",
      "core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::program::Program<'info, T> as \
          core::ops::deref::Deref>::deref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:4",
      "core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::interface::Interface<'info, T> as \
          core::ops::deref::Deref>::deref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:5",
      "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::interface::Interface<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:6",
      "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::signer::Signer<'info> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:7",
      "core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::signer::Signer<'info> as core::ops::deref::Deref>::deref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:8",
      "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:9",
      "core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
          core::ops::deref::Deref>::deref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:10",
      "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:11",
      "core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
          core::ops::deref::Deref>::deref"),
    (.accounts_borrowed_info_ref, "anchor-views-1.1.2:12",
      "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
    (.accounts_account_Account_deref_mut, "anchor-views-1.1.2:0",
      "core::ops::deref::DerefMut::deref_mut",
        "<anchor_lang::accounts::account::Account<'_, T> as \
          core::ops::deref::DerefMut>::deref_mut"),
    (.accounts_account_Account_deref_mut, "anchor-views-1.1.2:1",
      "core::ops::deref::DerefMut::deref_mut",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
          core::ops::deref::DerefMut>::deref_mut"),
    (.Pubkey_key, "anchor-views-1.1.2",
      "anchor_lang::Key::key", "<solana_address::Address as anchor_lang::Key>::key"),
    (.accounts_wrapper_key, "anchor-views-1.1.2:0",
      "anchor_lang::Key::key",
        "<anchor_lang::accounts::account::Account<'_, T> as anchor_lang::Key>::key"),
    (.accounts_wrapper_key, "anchor-views-1.1.2:1",
      "anchor_lang::Key::key",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
          anchor_lang::Key>::key"),
    (.accounts_wrapper_key, "anchor-views-1.1.2:2",
      "anchor_lang::Key::key",
        "<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Key>::key"),
    (.accounts_wrapper_key, "anchor-views-1.1.2:3",
      "anchor_lang::Key::key",
        "<anchor_lang::accounts::interface::Interface<'_, T> as anchor_lang::Key>::key"),
    (.accounts_wrapper_key, "anchor-views-1.1.2:4",
      "anchor_lang::Key::key",
        "<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Key>::key"),
    (.accounts_wrapper_key, "anchor-views-1.1.2:5",
      "anchor_lang::Key::key",
        "<anchor_lang::accounts::system_account::SystemAccount<'_> as \
          anchor_lang::Key>::key"),
    (.accounts_wrapper_key, "anchor-views-1.1.2:6",
      "anchor_lang::Key::key",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
          anchor_lang::Key>::key"),
    (.accounts_wrapper_key, "anchor-views-1.1.2:7",
      "anchor_lang::Key::key",
        "<anchor_lang::accounts::sysvar::Sysvar<'_, T> as anchor_lang::Key>::key"),
    (.accounts_boxed_Box_exit, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::AccountsExit::exit",
        "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'info> for \
          alloc::boxed::Box<T>>::exit"),
    (.accounts_boxed_Box_exit, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::AccountsExit::exit",
        "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'_> for \
          alloc::boxed::Box<T>>::exit"),
    (.AccountsExit_exit, "anchor-lifecycle-1.1.2",
      "anchor_lang::AccountsExit::exit", "anchor_lang::AccountsExit::exit"),
    (.accounts_unchecked_account_UncheckedAccount_try_from, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'info>::try_from",
        "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'info>::try_from"),
    (.accounts_unchecked_account_UncheckedAccount_try_from, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'_>::try_from",
        "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'_>::try_from")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 29 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "1.1.1" },
  { build0 with version := "1.2.1" },
  { build0 with version := "1.1.3-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 5 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

def build1 : Build where
  package := "anchor-lang"
  version := "1.1.2"
  source := registry
  target := [⟨"pointer_width", "64"⟩]

def rows1 : List Row := [
    (.bpf_writer_BpfWriter_write_all, "anchor-lang-1.1.2-writer",
      "std::io::Write::write_all",
        "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as std::io::Write>::write_all")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_1 :
    rows1.length = 1 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows1.all (identifies { build1 with version := version })) = true := by
  decide +kernel

def rejected1 : List Build := [
  { build1 with version := "1.1.1" },
  { build1 with version := "1.2.1" },
  { build1 with version := "1.1.3-rc.1" },
  { build1 with package := "unrelated-library" },
  { build1 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  { build1 with target := (build1.target.filter (fun fact => fact.field != "pointer_width")) },
  { build1 with target := (build1.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build1 with target := (build1.target ++ [⟨"pointer_width", "32"⟩]) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_1 :
    rejected1.length = 8 ∧
    rejected1.all (fun build => rows1.all (rejects build)) = true := by
  decide +kernel

def build2 : Build where
  package := "anchor-lang"
  version := "1.1.2"
  source := registry

def rows2 : List Row := [
    (.context_Context_new, "anchor-lang-1.1.2-context",
      "anchor_lang::context::Context::<'info, T>::new",
        "anchor_lang::context::Context::<'info, T>::new"),
    (.context_CpiContext_AccountInfoProgram_with_signer, "anchor-lang-1.1.2-signer",
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer",
        "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer"),
    (.context_CpiContext_AccountInfoProgram_new, "anchor-lang-1.1.2-cpi-new",
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new",
        "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new"),
    (.AccountDeserialize_try_deserialize, "anchor-lang-1.1.2-default",
      "anchor_lang::AccountDeserialize::try_deserialize",
        "anchor_lang::AccountDeserialize::try_deserialize"),
    (.AccountDeserialize_try_deserialize, "anchor-lang-1.1.2-default-mint",
      "anchor_lang::AccountDeserialize::try_deserialize",
        "<anchor_spl::token_interface::Mint as \
          anchor_lang::AccountDeserialize>::try_deserialize"),
    (.AccountDeserialize_try_deserialize, "anchor-lang-1.1.2-default-token-account",
      "anchor_lang::AccountDeserialize::try_deserialize",
        "<anchor_spl::token_interface::TokenAccount as \
          anchor_lang::AccountDeserialize>::try_deserialize")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_2 :
    rows2.length = 6 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows2.all (identifies { build2 with version := version })) = true := by
  decide +kernel

def rejected2 : List Build := [
  { build2 with version := "1.1.1" },
  { build2 with version := "1.2.1" },
  { build2 with version := "1.1.3-rc.1" },
  { build2 with package := "unrelated-library" },
  { build2 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_2 :
    rejected2.length = 5 ∧
    rejected2.all (fun build => rows2.all (rejects build)) = true := by
  decide +kernel

def build3 : Build where
  package := "anchor-lang"
  version := "1.1.2"
  source := registry
  dependencies := [
    ⟨"anchor-lang-error", "1.1.2", registry⟩]

def rows3 : List Row := [
    (.accounts_signer_Signer_try_accounts, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Accounts<'info, \
          B>>::try_accounts"),
    (.accounts_signer_Signer_try_accounts, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Accounts<'_, \
          B>>::try_accounts"),
    (.accounts_program_Program_try_accounts, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::program::Program<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"),
    (.accounts_program_Program_try_accounts, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Accounts<'_, \
          B>>::try_accounts"),
    (.accounts_boxed_Box_try_accounts, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'info, B> for \
          alloc::boxed::Box<T>>::try_accounts"),
    (.accounts_boxed_Box_try_accounts, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'_, B> for \
          alloc::boxed::Box<T>>::try_accounts"),
    (.accounts_option_Option_try_accounts, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'info, B> for \
          core::option::Option<T>>::try_accounts"),
    (.accounts_option_Option_try_accounts, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'_, B> for \
          core::option::Option<T>>::try_accounts"),
    (.accounts_interface_Interface_try_accounts, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::interface::Interface<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"),
    (.accounts_interface_Interface_try_accounts, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::interface::Interface<'_, T> as anchor_lang::Accounts<'_, \
          B>>::try_accounts"),
    (.accounts_unchecked_account_UncheckedAccount_try_accounts, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"),
    (.accounts_unchecked_account_UncheckedAccount_try_accounts, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
          anchor_lang::Accounts<'_, B>>::try_accounts")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_3 :
    rows3.length = 12 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows3.all (identifies { build3 with version := version })) = true := by
  decide +kernel

def accepted3 : List Build := [
  dependencyVersion build3 "anchor-lang-error" "1.1.3"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_3 :
    accepted3.length = 1 ∧
    accepted3.all (fun build => rows3.all (identifies build)) = true := by
  decide +kernel

def rejected3 : List Build := [
  { build3 with version := "1.1.1" },
  { build3 with version := "1.2.1" },
  { build3 with version := "1.1.3-rc.1" },
  { build3 with package := "unrelated-library" },
  { build3 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build3 "anchor-lang-error" "1.2.1",
  { build3 with dependencies := (build3.dependencies.filter (fun dep => dep.package !=
    "anchor-lang-error")) },
  { build3 with dependencies := (build3.dependencies ++ [⟨"anchor-lang-error", "1.1.2", registry⟩])
    },
  { build3 with dependencies := (build3.dependencies.map (fun dep =>
        if dep.package == "anchor-lang-error" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_3 :
    rejected3.length = 9 ∧
    rejected3.all (fun build => rows3.all (rejects build)) = true := by
  decide +kernel

def build4 : Build where
  package := "anchor-lang"
  version := "1.1.2"
  source := registry
  dependencies := [
    ⟨"anchor-lang-error", "1.1.2", registry⟩,
    ⟨"solana-account-info", "3.1.1", registry⟩,
    ⟨"solana-program-error", "3.0.1", registry⟩]

def rows4 : List Row := [
    (.accounts_account_Account_try_accounts, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"),
    (.accounts_account_Account_try_accounts, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::account::Account<'_, T> as anchor_lang::Accounts<'_, \
          B>>::try_accounts"),
    (.accounts_account_Account_try_from_unchecked, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked",
        "anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked"),
    (.accounts_account_Account_try_from_unchecked, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::accounts::account::Account::<'_, T>::try_from_unchecked",
        "anchor_lang::accounts::account::Account::<'_, T>::try_from_unchecked"),
    (.accounts_account_Account_exit, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::AccountsExit<'info>>::exit"),
    (.accounts_account_Account_exit, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::account::Account<'_, T> as \
          anchor_lang::AccountsExit<'_>>::exit"),
    (.accounts_interface_account_InterfaceAccount_exit, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          anchor_lang::AccountsExit<'info>>::exit"),
    (.accounts_interface_account_InterfaceAccount_exit, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
          anchor_lang::AccountsExit<'_>>::exit"),
    (.accounts_interface_account_InterfaceAccount_try_accounts, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"),
    (.accounts_interface_account_InterfaceAccount_try_accounts, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
          anchor_lang::Accounts<'_, B>>::try_accounts"),
    (.accounts_interface_account_InterfaceAccount_try_from_unchecked, "anchor-lifecycle-1.1\
      .2:0",
      "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, \
        T>::try_from_unchecked",
        "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, \
          T>::try_from_unchecked"),
    (.accounts_interface_account_InterfaceAccount_try_from_unchecked, "anchor-lifecycle-1.1\
      .2:1",
      "anchor_lang::accounts::interface_account::InterfaceAccount::<'_, \
        T>::try_from_unchecked",
        "anchor_lang::accounts::interface_account::InterfaceAccount::<'_, \
          T>::try_from_unchecked"),
    (.accounts_interface_account_InterfaceAccount_reload_released_guard, "anchor-lifecycle-\
      1.1.2:0",
      "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::reload",
        "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::reload"),
    (.accounts_interface_account_InterfaceAccount_reload_released_guard, "anchor-lifecycle-\
      1.1.2:1",
      "anchor_lang::accounts::interface_account::InterfaceAccount::<'_, T>::reload",
        "anchor_lang::accounts::interface_account::InterfaceAccount::<'_, T>::reload"),
    (.accounts_account_Account_close_checked, "anchor-lifecycle-1.1.2:0",
      "anchor_lang::AccountsClose::close",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::AccountsClose<'info>>::close"),
    (.accounts_account_Account_close_checked, "anchor-lifecycle-1.1.2:1",
      "anchor_lang::AccountsClose::close",
        "<anchor_lang::accounts::account::Account<'_, T> as \
          anchor_lang::AccountsClose<'_>>::close")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_4 :
    rows4.length = 16 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows4.all (identifies { build4 with version := version })) = true := by
  decide +kernel

def accepted4 : List Build := [
  dependencyVersion build4 "anchor-lang-error" "1.1.3",
  dependencyVersion build4 "solana-account-info" "3.1.2",
  dependencyVersion build4 "solana-program-error" "3.0.2"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_4 :
    accepted4.length = 3 ∧
    accepted4.all (fun build => rows4.all (identifies build)) = true := by
  decide +kernel

def rejected4 : List Build := [
  { build4 with version := "1.1.1" },
  { build4 with version := "1.2.1" },
  { build4 with version := "1.1.3-rc.1" },
  { build4 with package := "unrelated-library" },
  { build4 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build4 "anchor-lang-error" "1.2.1",
  dependencyVersion build4 "solana-account-info" "4.0.0",
  dependencyVersion build4 "solana-program-error" "4.0.0",
  { build4 with dependencies := (build4.dependencies.filter (fun dep => dep.package !=
    "anchor-lang-error")) },
  { build4 with dependencies := (build4.dependencies ++ [⟨"anchor-lang-error", "1.1.2", registry⟩])
    },
  { build4 with dependencies := (build4.dependencies.map (fun dep =>
        if dep.package == "anchor-lang-error" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_4 :
    rejected4.length = 11 ∧
    rejected4.all (fun build => rows4.all (rejects build)) = true := by
  decide +kernel

def build5 : Build where
  package := "anchor-lang"
  version := "1.1.2"
  source := registry
  dependencies := [
    ⟨"solana-system-interface", "2.0.0", registry⟩,
    ⟨"solana-account-info", "3.1.1", registry⟩,
    ⟨"solana-program-error", "3.0.1", registry⟩,
    ⟨"solana-pubkey", "3.0.0", registry⟩,
    ⟨"anchor-lang-error", "1.1.2", registry⟩,
    ⟨"bincode", "1.3.3", registry⟩]

def rows5 : List Row := [
    (.system_program_allocate_unit_borsh, "anchor-system-1-1-2",
      "anchor_lang::system_program::allocate", "anchor_lang::system_program::allocate"),
    (.system_program_transfer_unit_borsh, "anchor-system-1-1-2",
      "anchor_lang::system_program::transfer", "anchor_lang::system_program::transfer"),
    (.system_program_assign_unit_borsh, "anchor-system-1-1-2",
      "anchor_lang::system_program::assign", "anchor_lang::system_program::assign"),
    (.system_program_create_account_unit_borsh, "anchor-system-1-1-2",
      "anchor_lang::system_program::create_account", "anchor_lang::system_program::create_a\
        ccount")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_5 :
    rows5.length = 4 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows5.all (identifies { build5 with version := version })) = true := by
  decide +kernel

def accepted5 : List Build := [
  dependencyVersion build5 "solana-system-interface" "2.0.1",
  dependencyVersion build5 "solana-account-info" "3.1.2",
  dependencyVersion build5 "solana-program-error" "3.0.2",
  dependencyVersion build5 "solana-pubkey" "3.0.1",
  dependencyVersion build5 "anchor-lang-error" "1.1.3",
  dependencyVersion build5 "bincode" "1.3.4"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_5 :
    accepted5.length = 6 ∧
    accepted5.all (fun build => rows5.all (identifies build)) = true := by
  decide +kernel

def rejected5 : List Build := [
  { build5 with version := "1.1.1" },
  { build5 with version := "1.2.1" },
  { build5 with version := "1.1.3-rc.1" },
  { build5 with package := "unrelated-library" },
  { build5 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build5 "solana-system-interface" "3.0.0",
  dependencyVersion build5 "solana-account-info" "4.0.0",
  dependencyVersion build5 "solana-program-error" "4.0.0",
  dependencyVersion build5 "solana-pubkey" "4.0.0",
  dependencyVersion build5 "anchor-lang-error" "1.2.1",
  dependencyVersion build5 "bincode" "2.0.0",
  { build5 with dependencies := (build5.dependencies.filter (fun dep => dep.package !=
    "solana-system-interface")) },
  { build5 with dependencies := (build5.dependencies ++ [⟨"solana-system-interface", "2.0.0",
    registry⟩]) },
  { build5 with dependencies := (build5.dependencies.map (fun dep =>
        if dep.package == "solana-system-interface" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_5 :
    rejected5.length = 14 ∧
    rejected5.all (fun build => rows5.all (rejects build)) = true := by
  decide +kernel

def build6 : Build where
  package := "anchor-lang"
  version := "1.1.2"
  source := registry
  dependencies := [
    ⟨"bincode", "1.3.3", registry⟩,
    ⟨"solana-loader-v3-interface", "6.1.1", registry⟩]

def rows6 : List Row := [
    (.bpf_upgradeable_state_UpgradeableLoaderState_try_deserialize_unchecked,
      "anchor-lang-1.1.2-loader",
      "anchor_lang::AccountDeserialize::try_deserialize_unchecked",
        "anchor_lang::bpf_upgradeable_state::<impl anchor_lang::AccountDeserialize for \
          solana_loader_v3_interface::state::UpgradeableLoaderState>::try_deserialize_unche\
          cked")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_6 :
    rows6.length = 1 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows6.all (identifies { build6 with version := version })) = true := by
  decide +kernel

def accepted6 : List Build := [
  dependencyVersion build6 "bincode" "1.3.4",
  dependencyVersion build6 "solana-loader-v3-interface" "6.1.2"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_6 :
    accepted6.length = 2 ∧
    accepted6.all (fun build => rows6.all (identifies build)) = true := by
  decide +kernel

def rejected6 : List Build := [
  { build6 with version := "1.1.1" },
  { build6 with version := "1.2.1" },
  { build6 with version := "1.1.3-rc.1" },
  { build6 with package := "unrelated-library" },
  { build6 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build6 "bincode" "2.0.0",
  dependencyVersion build6 "solana-loader-v3-interface" "7.0.0",
  { build6 with dependencies := (build6.dependencies.filter (fun dep => dep.package != "bin\
    code"))
    },
  { build6 with dependencies := (build6.dependencies ++ [⟨"bincode", "1.3.3", registry⟩]) },
  { build6 with dependencies := (build6.dependencies.map (fun dep =>
        if dep.package == "bincode" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_6 :
    rejected6.length = 10 ∧
    rejected6.all (fun build => rows6.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.UpdatedProfiles

@[expose] public section

namespace SolanalibTest.Specs.AnchorLang.V1_0_2Operations

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.AnchorLang.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

def build0 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lang-1.0.2-remaining").forBuild
        { build0 with version := version }).identities .context_CpiContext_with_remaining_accounts =
          [⟨"anchor-lang", version,
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, \
              T>::with_remaining_accounts",
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, \
              T>::with_remaining_accounts"⟩]))
              = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2",
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_remaining_accounts",
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, \
              T>::with_remaining_accounts"⟩] :
              List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build0).identities .context_CpiContext_with_remaining_accounts)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "anchor-lang-1.0.2-remaining").applicability
      .context_CpiContext_with_remaining_accounts).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lang-1.0.2-remaining").forBuild { build0 with version := version
        }).identities
        .context_CpiContext_with_remaining_accounts).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "anchor-lang-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities
        .context_CpiContext_with_remaining_accounts).isEmpty) = true := by
  decide +kernel

def build1 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"anchor-syn", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile1_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lang-1.0.2-code").forBuild
        { build1 with version := version }).identities
          .error_Error_from_error_code_account_migration =
          [⟨"anchor-lang", version, "core::convert::From::from",
            "<anchor_lang::error::Error as \
              core::convert::From<anchor_lang::error::ErrorCode>>::from"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile1_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "core::convert::From::from",
            "<anchor_lang::error::Error as \
              core::convert::From<anchor_lang::error::ErrorCode>>::from"⟩] : List
                Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build1).identities .error_Error_from_error_code_account_migration)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile1_range_rejections :
    ((selectedProfile "anchor-lang-1.0.2-code").applicability
      .error_Error_from_error_code_account_migration).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lang-1.0.2-code").forBuild { build1 with version := version
        }).identities
        .error_Error_from_error_code_account_migration).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile1_build_rejections :
    ([{ build1 with package := "anchor-lang-other" },
      { build1 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build1 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build1 with dependencies := [] },
      { build1 with dependencies := [⟨"anchor-syn", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"anchor-syn", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-syn", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-syn", "1.0.2-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities
        .error_Error_from_error_code_account_migration).isEmpty) = true := by
  decide +kernel

def build2 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile2_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lang-1.0.2-log").forBuild
        { build2 with version := version }).identities .error_Error_log_modern =
          [⟨"anchor-lang", version, "anchor_lang::error::Error::log",
            "anchor_lang::error::Error::log"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile2_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::error::Error::log",
            "anchor_lang::error::Error::log"⟩] : List Capabilities.RustIdentity).all (fun identity
              =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build2).identities .error_Error_log_modern)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile2_range_rejections :
    ((selectedProfile "anchor-lang-1.0.2-log").applicability .error_Error_log_modern).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lang-1.0.2-log").forBuild { build2 with version := version
        }).identities
        .error_Error_log_modern).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile2_build_rejections :
    ([{ build2 with package := "anchor-lang-other" },
      { build2 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build2 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build2 with dependencies := [] },
      { build2 with dependencies := [⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities
        .error_Error_log_modern).isEmpty) = true := by
  decide +kernel

def build3 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"anchor-syn", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile3_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lang-1.0.2-code-name").forBuild
        { build3 with version := version }).identities .error_ErrorCode_name_account_migration =
          [⟨"anchor-lang", version, "anchor_lang::error::ErrorCode::name",
            "anchor_lang::error::ErrorCode::name"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile3_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::error::ErrorCode::name",
            "anchor_lang::error::ErrorCode::name"⟩] : List Capabilities.RustIdentity).all (fun
              identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build3).identities .error_ErrorCode_name_account_migration)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile3_range_rejections :
    ((selectedProfile "anchor-lang-1.0.2-code-name").applicability
      .error_ErrorCode_name_account_migration).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lang-1.0.2-code-name").forBuild { build3 with version := version
        }).identities
        .error_ErrorCode_name_account_migration).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile3_build_rejections :
    ([{ build3 with package := "anchor-lang-other" },
      { build3 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build3 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build3 with dependencies := [] },
      { build3 with dependencies := [⟨"anchor-syn", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"anchor-syn", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-syn", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-syn", "1.0.2-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities
        .error_ErrorCode_name_account_migration).isEmpty) = true := by
  decide +kernel

def build4 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile4_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lang-1.0.2-context").forBuild
        { build4 with version := version }).identities .context_Context_new =
          [⟨"anchor-lang", version, "anchor_lang::context::Context::<'info, T>::new",
            "anchor_lang::context::Context::<'info, T>::new"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile4_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::context::Context::<'info, T>::new",
            "anchor_lang::context::Context::<'info, T>::new"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build4).identities .context_Context_new)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile4_range_rejections :
    ((selectedProfile "anchor-lang-1.0.2-context").applicability .context_Context_new).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lang-1.0.2-context").forBuild { build4 with version := version
        }).identities
        .context_Context_new).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile4_build_rejections :
    ([{ build4 with package := "anchor-lang-other" },
      { build4 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build4 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities
        .context_Context_new).isEmpty) = true := by
  decide +kernel

def build5 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile5_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lang-1.0.2-cpi-new").forBuild
        { build5 with version := version }).identities .context_CpiContext_AccountInfoProgram_new =
          [⟨"anchor-lang", version, "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, \
            T>::new",
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile5_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, \
      T>::new",
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build5).identities .context_CpiContext_AccountInfoProgram_new)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile5_range_rejections :
    ((selectedProfile "anchor-lang-1.0.2-cpi-new").applicability
      .context_CpiContext_AccountInfoProgram_new).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lang-1.0.2-cpi-new").forBuild { build5 with version := version
        }).identities
        .context_CpiContext_AccountInfoProgram_new).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile5_build_rejections :
    ([{ build5 with package := "anchor-lang-other" },
      { build5 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build5 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities
        .context_CpiContext_AccountInfoProgram_new).isEmpty) = true := by
  decide +kernel

def build6 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile6_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lang-1.0.2-signer").forBuild
        { build6 with version := version }).identities
          .context_CpiContext_AccountInfoProgram_with_signer =
          [⟨"anchor-lang", version,
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer",
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile6_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2",
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer",
            "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build6).identities .context_CpiContext_AccountInfoProgram_with_signer)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile6_range_rejections :
    ((selectedProfile "anchor-lang-1.0.2-signer").applicability
      .context_CpiContext_AccountInfoProgram_with_signer).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lang-1.0.2-signer").forBuild { build6 with version := version
        }).identities
        .context_CpiContext_AccountInfoProgram_with_signer).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile6_build_rejections :
    ([{ build6 with package := "anchor-lang-other" },
      { build6 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build6 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities
        .context_CpiContext_AccountInfoProgram_with_signer).isEmpty) = true := by
  decide +kernel

def build7 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile7_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lang-1.0.2-name").forBuild
        { build7 with version := version }).identities
          .error_Error_GenericProgram_with_account_name =
          [⟨"anchor-lang", version, "anchor_lang::error::Error::with_account_name",
            "anchor_lang::error::Error::with_account_name"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile7_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::error::Error::with_account_name",
            "anchor_lang::error::Error::with_account_name"⟩] : List Capabilities.RustIdentity).all
              (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build7).identities .error_Error_GenericProgram_with_account_name)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile7_range_rejections :
    ((selectedProfile "anchor-lang-1.0.2-name").applicability
      .error_Error_GenericProgram_with_account_name).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lang-1.0.2-name").forBuild { build7 with version := version
        }).identities
        .error_Error_GenericProgram_with_account_name).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile7_build_rejections :
    ([{ build7 with package := "anchor-lang-other" },
      { build7 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build7 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities
        .error_Error_GenericProgram_with_account_name).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.V1_0_2Operations

namespace SolanalibTest.Specs.AnchorLang.LegacyOperationCompatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorLang.Capabilities (Key catalog)

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal Rust identities are independent of generated profile selection. -/
def referenceRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.error_Error_from_legacy_error_code, {
    package := "anchor-lang", version := "0.29.0", source :=
    registry, dependencies := [⟨"anchor-syn", "0.29.0", registry⟩] },
      [("core::convert::From::from",
        "<anchor_lang::error::Error as \
          core::convert::From<anchor_lang::error::ErrorCode>>::from")]),
    (.error_Error_log_legacy_program, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::error::Error::log", "anchor_lang::error::Error::log")]),
    (.error_ErrorCode_name_legacy, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry, dependencies := [⟨"anchor-syn", "0.29.0", registry⟩] },
      [("anchor_lang::error::ErrorCode::name", "anchor_lang::error::ErrorCode::name")]),
    (.bpf_writer_BpfWriter_write_all, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry, target := [⟨"pointer_width", "64"⟩] },
      [("std::io::Write::write_all",
        "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as std::io::Write>::write_all")]),
    (.context_Context_new, {
      package := "anchor-lang", version := "0.29.0", source := registry },
      [("anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new",
        "anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new")]),
    (.context_CpiContext_AccountInfoProgram_new, {
      package := "anchor-lang", version := "0.\
      29.0",
      source := registry },
      [("anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new",
        "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new")]),
    (.context_CpiContext_AccountInfoProgram_new_with_signer, {
      package := "anchor-lang", version :=
      "0.29.0", source := registry },
      [("anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer",
        "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer")]),
    (.context_CpiContext_AccountInfoProgram_with_signer, {
      package := "anchor-lang", version :=
      "0.29.0", source := registry },
      [("anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer",
        "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer")]),
    (.error_Error_GenericProgram_with_account_name, {
      package := "anchor-lang", version :=
      "0.29.0", source := registry },
      [("anchor_lang::error::Error::with_account_name",
        "anchor_lang::error::Error::with_account_name")]),
    (.error_Error_GenericProgram_with_pubkeys, {
      package := "anchor-lang", version := "0.29\
      .0",
      source := registry },
      [("anchor_lang::error::Error::with_pubkeys", "anchor_lang::error::Error::with_pubkeys")]),
    (.error_Error_GenericProgram_with_values, {
      package := "anchor-lang", version := "0.29.\
      0",
      source := registry },
      [("anchor_lang::error::Error::with_values", "anchor_lang::error::Error::with_values")])]

/-- These uninspected patch versions exercise compatibility assumptions only. -/
def compatibleRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.error_Error_from_legacy_error_code, {
    package := "anchor-lang", version := "0.29.1", source :=
    registry, dependencies := [⟨"anchor-syn", "0.29.0", registry⟩] },
      [("core::convert::From::from",
        "<anchor_lang::error::Error as \
          core::convert::From<anchor_lang::error::ErrorCode>>::from")]),
    (.error_Error_log_legacy_program, {
      package := "anchor-lang", version := "0.29.1", source :=
      registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::error::Error::log", "anchor_lang::error::Error::log")]),
    (.error_ErrorCode_name_legacy, {
      package := "anchor-lang", version := "0.29.1", source :=
      registry, dependencies := [⟨"anchor-syn", "0.29.0", registry⟩] },
      [("anchor_lang::error::ErrorCode::name", "anchor_lang::error::ErrorCode::name")]),
    (.bpf_writer_BpfWriter_write_all, {
      package := "anchor-lang", version := "0.29.1", source :=
      registry, target := [⟨"pointer_width", "64"⟩] },
      [("std::io::Write::write_all",
        "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as std::io::Write>::write_all")]),
    (.context_Context_new, {
      package := "anchor-lang", version := "0.29.1", source := registry },
      [("anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new",
        "anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new")]),
    (.context_CpiContext_AccountInfoProgram_new, {
      package := "anchor-lang", version := "0.\
      29.1",
      source := registry },
      [("anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new",
        "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new")]),
    (.context_CpiContext_AccountInfoProgram_new_with_signer, {
      package := "anchor-lang", version :=
      "0.29.1", source := registry },
      [("anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer",
        "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer")]),
    (.context_CpiContext_AccountInfoProgram_with_signer, {
      package := "anchor-lang", version :=
      "0.29.1", source := registry },
      [("anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer",
        "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer")]),
    (.error_Error_GenericProgram_with_account_name, {
      package := "anchor-lang", version :=
      "0.29.1", source := registry },
      [("anchor_lang::error::Error::with_account_name",
        "anchor_lang::error::Error::with_account_name")]),
    (.error_Error_GenericProgram_with_pubkeys, {
      package := "anchor-lang", version := "0.29\
      .1",
      source := registry },
      [("anchor_lang::error::Error::with_pubkeys", "anchor_lang::error::Error::with_pubkeys")]),
    (.error_Error_GenericProgram_with_values, {
      package := "anchor-lang", version := "0.29.\
      1",
      source := registry },
      [("anchor_lang::error::Error::with_values", "anchor_lang::error::Error::with_values")])]

theorem exact_reference_identities :
    referenceRows.length = 11 ∧ referenceRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem compatible_actual_version_identities :
    compatibleRows.length = 11 ∧ compatibleRows.all (fun row => decide
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
  [(.error_Error_from_legacy_error_code, {
    package := "anchor-lang", version := "0.29.0", source :=
    registry, dependencies := [⟨"anchor-syn", "0.29.0", registry⟩] }, ["0.28.999", "0.30.0",
    "0.29.0-rc.1"]),
    (.error_Error_log_legacy_program, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] }, ["0.28.999",
        "0.30.0",
      "0.29.0-rc.1"]),
    (.error_ErrorCode_name_legacy, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry, dependencies := [⟨"anchor-syn", "0.29.0", registry⟩] }, ["0.28.999", "0.30.\
        0",
      "0.29.0-rc.1"]),
    (.bpf_writer_BpfWriter_write_all, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry, target := [⟨"pointer_width", "64"⟩] }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.context_Context_new, {
      package := "anchor-lang", version := "0.29.0", source := registry },
      ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.context_CpiContext_AccountInfoProgram_new, {
      package := "anchor-lang", version := "0.\
      29.0",
      source := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.context_CpiContext_AccountInfoProgram_new_with_signer, {
      package := "anchor-lang", version :=
      "0.29.0", source := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.context_CpiContext_AccountInfoProgram_with_signer, {
      package := "anchor-lang", version :=
      "0.29.0", source := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.error_Error_GenericProgram_with_account_name, {
      package := "anchor-lang", version :=
      "0.29.0", source := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.error_Error_GenericProgram_with_pubkeys, {
      package := "anchor-lang", version := "0.29\
      .0",
      source := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.error_Error_GenericProgram_with_values, {
      package := "anchor-lang", version := "0.29.\
      0",
      source := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"])]

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

/-- Literal provider intervals test selection, without claiming native coverage. -/
def dependencyVersions : List (String × String × List String) :=
  [("anchor-syn", "0.29.1", ["0.28.999", "0.30.0", "0.29.1-rc.1"]),
    ("solana-program", "1.18.27", ["1.18.25", "2.0.0", "1.18.27-rc.1"])]

theorem compatible_dependencies_keep_literal_identities :
    dependencyVersions.length = 2 ∧
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      match dependencyVersions.find? (fun item => item.1 == dep.package) with
      | none => false
      | some item =>
        let build := { row.2.1 with dependencies := row.2.1.dependencies.map (fun d =>
          if d.package = dep.package then { d with version := item.2.1 } else d) }
        decide ((catalog.forBuild build).identities row.1 =
          row.2.2.map (fun names => ⟨build.package, build.version, names.1, names.2⟩)))) = true :=
            by
  decide +kernel

theorem dependency_bounds_prereleases_and_two_compatible_candidates_rejected :
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      match dependencyVersions.find? (fun item => item.1 == dep.package) with
      | none => false
      | some item =>
        item.2.2.all (fun version =>
          ((catalog.forBuild { row.2.1 with dependencies := row.2.1.dependencies.map (fun d =>
            if d.package = dep.package then { d with version } else d) }).identities
              row.1).isEmpty) &&
        ((catalog.forBuild { row.2.1 with dependencies :=
          row.2.1.dependencies ++ [{ dep with version := item.2.1 }] }).identities row.1).isEmpty))
            = true := by
  decide +kernel

theorem required_dependency_cannot_be_omitted :
    referenceRows.any (fun row => !row.2.1.dependencies.isEmpty) = true ∧
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.filter (fun d => d.package != dep.package)) }).identities
          row.1).isEmpty)) = true := by
  decide +kernel

theorem dependency_generation_fork_and_ambiguity_rejected :
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.map (fun d => if d.package = dep.package then
          { d with version := "99.0.0" } else d)) }).identities row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.map (fun d => if d.package = dep.package then
          { d with source := ⟨"git", "https://example.invalid/provider-fork",
            "0123456789012345678901234567890123456789"⟩ } else d)) }).identities row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with dependencies := row.2.1.dependencies ++ [dep] }).identities
        row.1).isEmpty)) = true := by
  decide +kernel

theorem every_selected_target_fact_is_required :
    referenceRows.any (fun row => !row.2.1.target.isEmpty) = true ∧
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.target.all (fun fact =>
      ((catalog.forBuild { row.2.1 with target :=
        (row.2.1.target.filter (fun kept => kept.field != fact.field)) }).identities
          row.1).isEmpty)) = true := by
  decide +kernel

theorem conflicting_or_duplicate_target_facts_rejected :
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.target.all (fun fact =>
      ((catalog.forBuild { row.2.1 with target :=
        (row.2.1.target.map (fun kept => if kept.field = fact.field then
          { kept with value := "incompatible-target" } else kept)) }).identities row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with target := row.2.1.target ++ [fact] }).identities
        row.1).isEmpty)) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.LegacyOperationCompatibility

/- Per-operation compatibility selection. Synthetic versions carry no native or ABI credit. -/
namespace SolanalibTest.Specs.AnchorLang.Operations.LegacyCompatibility

@[expose] public section

set_option autoImplicit false

namespace InlineErrorsAndContext

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorLang.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (Solanalib.Specs.AnchorLang.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.error_Error_from_anchor_error_inline, [⟨"anchor-lang", version, "core::convert::From:\
      :from",
      "<anchor_lang::error::Error as \
        core::convert::From<anchor_lang::error::AnchorError>>::from"⟩]),
    (.error_Error_with_account_name_inline, [⟨"anchor-lang", version,
      "anchor_lang::error::Error::with_account_name",
      "anchor_lang::error::Error::with_account_name"⟩]),
    (.error_Error_with_pubkeys_inline, [⟨"anchor-lang", version,
      "anchor_lang::error::Error::with_pubkeys", "anchor_lang::error::Error::with_pubkeys"⟩]),
    (.error_Error_with_source_inline, [⟨"anchor-lang", version,
      "anchor_lang::error::Error::with_source", "anchor_lang::error::Error::with_source"⟩]),
    (.error_Error_with_values_inline, [⟨"anchor-lang", version,
      "anchor_lang::error::Error::with_values", "anchor_lang::error::Error::with_values"⟩]),
    (.context_Context_new, [⟨"anchor-lang", version,
      "anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new",
      "anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new"⟩]),
    (.context_CpiContext_AccountInfoProgram_new, [⟨"anchor-lang", version,
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new",
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new"⟩]),
    (.context_CpiContext_AccountInfoProgram_new_with_signer, [⟨"anchor-lang", version,
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer",
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer"⟩]),
    (.context_CpiContext_AccountInfoProgram_with_signer, [⟨"anchor-lang", version,
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer",
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["0.26.9", "0.28.0", "0.27.1-rc.1"].all (fun version =>
      (identityCases version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with version := version }).identities
          entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_origin_rejected :
    (identityCases compatibleBuild.version).all (fun entry =>
      ((catalog.forBuild { compatibleBuild with source :=
        ⟨"git", "https://example.org/source-fork", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
          a"⟩ }).identities entry.1).isEmpty) = true := by decide +kernel

end InlineErrorsAndContext

namespace GeneratedErrors

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorLang.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  dependencies := [⟨"anchor-syn", "0.27.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (Solanalib.Specs.AnchorLang.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.error_Error_from_error_code_inline, [⟨"anchor-lang", version, "core::convert::From::f\
      rom",
      "<anchor_lang::error::Error as \
        core::convert::From<anchor_lang::error::ErrorCode>>::from"⟩]),
    (.error_ErrorCode_name_pre_token_program_checks, [⟨"anchor-lang", version,
      "anchor_lang::error::ErrorCode::name", "anchor_lang::error::ErrorCode::name"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["0.26.9", "0.28.0", "0.27.1-rc.1"].all (fun version =>
      (identityCases version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with version := version }).identities
          entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_origin_rejected :
    (identityCases compatibleBuild.version).all (fun entry =>
      ((catalog.forBuild { compatibleBuild with source :=
        ⟨"git", "https://example.org/source-fork", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
          a"⟩ }).identities entry.1).isEmpty) = true := by decide +kernel

theorem every_dependency_is_required_and_unambiguous :
    [referenceBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        (identityCases build.version).all (fun entry =>
          ((catalog.forBuild { build with dependencies := build.dependencies.filter (fun kept =>
            kept.package != dep.package) }).identities entry.1).isEmpty &&
          ((catalog.forBuild { build with dependencies := build.dependencies ++ [dep] }).identities
            entry.1).isEmpty))) = true := by decide +kernel

theorem every_dependency_rejects_wrong_release_or_origin :
    compatibleBuild.dependencies.all (fun dep =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun kept =>
              if kept.package = dep.package then { kept with version := "99.0.0" } else kept)
            }).identities entry.1).isEmpty &&
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun kept =>
              if kept.package = dep.package then { kept with source := ⟨"git", "https://example.org/provider-fork",
                "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else kept) }).identities
                  entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_dependency_actual_identities :
    ([("anchor-syn", "0.27.1")] : List (String × String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry => decide
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1 = entry.2))) = true := by decide +kernel

theorem exact_codecs_and_dependency_boundaries_retained :
    ([("anchor-syn", "0.28.0"), ("anchor-syn", "0.27.1-rc.1")] : List (String × String)).all (fun
      change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1).isEmpty)) = true := by decide +kernel

end GeneratedErrors

namespace ProgramErrors

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorLang.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  dependencies := [⟨"solana-program", "1.15.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (Solanalib.Specs.AnchorLang.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.error_Error_from_program_error_inline, [⟨"anchor-lang", version, "core::convert::From\
      ::from",
      "<anchor_lang::error::Error as \
        core::convert::From<solana_program::program_error::ProgramError>>::from"⟩]),
    (.error_Error_log_inline, [⟨"anchor-lang", version, "anchor_lang::error::Error::log",
      "anchor_lang::error::Error::log"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["0.26.9", "0.28.0", "0.27.1-rc.1"].all (fun version =>
      (identityCases version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with version := version }).identities
          entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_origin_rejected :
    (identityCases compatibleBuild.version).all (fun entry =>
      ((catalog.forBuild { compatibleBuild with source :=
        ⟨"git", "https://example.org/source-fork", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
          a"⟩ }).identities entry.1).isEmpty) = true := by decide +kernel

theorem every_dependency_is_required_and_unambiguous :
    [referenceBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        (identityCases build.version).all (fun entry =>
          ((catalog.forBuild { build with dependencies := build.dependencies.filter (fun kept =>
            kept.package != dep.package) }).identities entry.1).isEmpty &&
          ((catalog.forBuild { build with dependencies := build.dependencies ++ [dep] }).identities
            entry.1).isEmpty))) = true := by decide +kernel

theorem every_dependency_rejects_wrong_release_or_origin :
    compatibleBuild.dependencies.all (fun dep =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun kept =>
              if kept.package = dep.package then { kept with version := "99.0.0" } else kept)
            }).identities entry.1).isEmpty &&
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun kept =>
              if kept.package = dep.package then { kept with source := ⟨"git", "https://example.org/provider-fork",
                "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else kept) }).identities
                  entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_dependency_actual_identities :
    ([("solana-program", "1.15.3")] : List (String × String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry => decide
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1 = entry.2))) = true := by decide +kernel

theorem exact_codecs_and_dependency_boundaries_retained :
    ([("solana-program", "1.16.0"), ("solana-program", "1.15.3-rc.1")] : List (String ×
      String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1).isEmpty)) = true := by decide +kernel

end ProgramErrors

namespace Idl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorLang.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  dependencies := [⟨"borsh", "0.9.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (Solanalib.Specs.AnchorLang.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.idl_IdlInstruction_deserialize, [⟨"anchor-lang", version,
      "borsh::de::BorshDeserialize::deserialize",
      "<anchor_lang::idl::IdlInstruction as borsh::de::BorshDeserialize>::deserialize"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["0.26.9", "0.28.0", "0.27.1-rc.1"].all (fun version =>
      (identityCases version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with version := version }).identities
          entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_origin_rejected :
    (identityCases compatibleBuild.version).all (fun entry =>
      ((catalog.forBuild { compatibleBuild with source :=
        ⟨"git", "https://example.org/source-fork", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
          a"⟩ }).identities entry.1).isEmpty) = true := by decide +kernel

theorem every_dependency_is_required_and_unambiguous :
    [referenceBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        (identityCases build.version).all (fun entry =>
          ((catalog.forBuild { build with dependencies := build.dependencies.filter (fun kept =>
            kept.package != dep.package) }).identities entry.1).isEmpty &&
          ((catalog.forBuild { build with dependencies := build.dependencies ++ [dep] }).identities
            entry.1).isEmpty))) = true := by decide +kernel

theorem every_dependency_rejects_wrong_release_or_origin :
    compatibleBuild.dependencies.all (fun dep =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun kept =>
              if kept.package = dep.package then { kept with version := "99.0.0" } else kept)
            }).identities entry.1).isEmpty &&
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun kept =>
              if kept.package = dep.package then { kept with source := ⟨"git", "https://example.org/provider-fork",
                "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else kept) }).identities
                  entry.1).isEmpty)) = true := by decide +kernel

theorem exact_codecs_and_dependency_boundaries_retained :
    ([("borsh", "0.10.4")] : List (String × String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1).isEmpty)) = true := by decide +kernel

end Idl

namespace Writer

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorLang.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (Solanalib.Specs.AnchorLang.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.bpf_writer_BpfWriter_write_all, [⟨"anchor-lang", version, "std::io::Write::write_all",
      "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as std::io::Write>::write_all"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["0.26.9", "0.28.0", "0.27.1-rc.1"].all (fun version =>
      (identityCases version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with version := version }).identities
          entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_origin_rejected :
    (identityCases compatibleBuild.version).all (fun entry =>
      ((catalog.forBuild { compatibleBuild with source :=
        ⟨"git", "https://example.org/source-fork", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
          a"⟩ }).identities entry.1).isEmpty) = true := by decide +kernel

theorem required_target_facts_are_not_optional :
    compatibleBuild.target.all (fun fact =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with target := compatibleBuild.target.filter (fun kept
          => kept.field != fact.field) }).identities entry.1).isEmpty &&
        ((catalog.forBuild { compatibleBuild with target := compatibleBuild.target ++ [fact]
          }).identities entry.1).isEmpty)) = true := by decide +kernel

theorem conflicting_target_facts_rejected :
    ([⟨"pointer_width", "32"⟩] : List Versioning.TargetFact).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with target := compatibleBuild.target.map (fun fact =>
          if fact.field = change.field then change else fact) }).identities entry.1).isEmpty)) =
            true := by decide +kernel

end Writer

end

end SolanalibTest.Specs.AnchorLang.Operations.LegacyCompatibility
