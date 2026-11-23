/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplToken2022
public import SolanalibTest.Specs.Core.TokenExtensionLegacy
public import Solanalib.Specs.SplToken2022.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false
set_option maxRecDepth 10000

namespace SolanalibTest.Specs.SplToken2022.Models

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Specs.Core.TokenExtensionLegacy
open Solanalib.Specs.SplToken2022

/-- The registered old-version API keeps the allocation/error ordering. -/
theorem listing_early_abort :
    extension.BaseStateWithExtensions.get_extension_types_run abortingReader [] ()
      (.terminated (99 : Nat)) := push_abort_precedes_payload_error

theorem sizing_early_abort :
    extension.ExtensionType.try_calculate_account_len_run ⟨abortingArray, 82⟩ [] variableFirst
      (.terminated (99 : Nat)) := allocation_precedes_variable_size_error

theorem unpack_marker_only :
    extension.StateWithExtensions.unpack_run Legacy.mintUnpacker [] atMarker
      (.returned (.error .InvalidAccountData) []) := marker_only_rejected

/-- The public epoch wrapper switches at equality and retains the whole
configuration, including fields unrelated to this calculation. -/
theorem epoch_activation_from_contract
    (operation : TransferFeeConfig → UInt64 × UInt64 → Option UInt64 × TransferFeeConfig)
    (correct : extension.transfer_fee.TransferFeeConfig.calculate_epoch_fee_contract.RealizedBy
      operation)
    (config : TransferFeeConfig) (amount : UInt64) :
    operation config (config.newer.epoch, amount) = (config.newer.calculateFee amount, config) := by
  have post := correct config (config.newer.epoch, amount) trivial
  change (operation config (config.newer.epoch, amount)).1 =
      config.calculateEpochFee config.newer.epoch amount ∧
    (operation config (config.newer.epoch, amount)).2 = config at post
  exact Prod.ext (post.1.trans (config.calculateEpochFee_at amount).1) post.2

/-- An excessive selected rate still fails the inverse wrapper when its
configured cap is zero; no successful zero fee may replace that failure. -/
theorem inverse_epoch_failure_from_contract
    (operation : TransferFeeConfig → UInt64 × UInt64 → Option UInt64 × TransferFeeConfig)
    (correct :
      extension.transfer_fee.TransferFeeConfig.calculate_inverse_epoch_fee_contract.RealizedBy
      operation)
    (config : TransferFeeConfig) (epoch amount : UInt64)
    (excess : FeeArithmetic.basisPointScale < (config.getEpochFee epoch).basisPoints.toNat)
    (positive : amount.toNat ≠ 0) :
    operation config (epoch, amount) = (none, config) := by
  have post := correct config (epoch, amount) trivial
  change (operation config (epoch, amount)).1 = config.calculateInverseEpochFee epoch amount ∧
    (operation config (epoch, amount)).2 = config at post
  exact Prod.ext (post.1.trans
    ((config.getEpochFee epoch).calculateInverseFee_excess_rate amount excess positive)) post.2

end SolanalibTest.Specs.SplToken2022.Models

namespace SolanalibTest.Specs.SplToken2022.Models.ExtensionProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.SplToken2022.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.extension_BaseStateWithExtensions_get_extension,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"pointer_width", "64"⟩],
        dependencies := [⟨"spl-pod", "0.5.1", registry⟩, ⟨"bytemuck", "1.22.0", registry⟩] },
      [("spl_token_2022::extension::BaseStateWithExtensions::get_extension",
        "spl_token_2022::extension::BaseStateWithExtensions::get_extension")]),
    (.extension_BaseStateWithExtensions_get_extension,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"pointer_width", "64"⟩],
        dependencies := [⟨"spl-pod", "0.5.1", registry⟩, ⟨"bytemuck", "1.24.0", registry⟩] },
      [("spl_token_2022::extension::BaseStateWithExtensions::get_extension",
        "spl_token_2022::extension::BaseStateWithExtensions::get_extension")]),
    (.extension_BaseStateWithExtensions_get_extension_types,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"pointer_width", "64"⟩] },
      [("spl_token_2022::extension::BaseStateWithExtensions::get_extension_types",
        "spl_token_2022::extension::BaseStateWithExtensions::get_extension_types")]),
    (.extension_BaseStateWithExtensions_try_get_new_account_len_for_variable_len_extension,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"pointer_width", "64"⟩] },
      [("spl_token_2022::extension::BaseStateWithExtensions::try_get_new_account_len_for_va\
        riable_len_extension", "spl_token_2022::extension::BaseStateWithExtensions::try_get\
          _new_account_len_for_variable_len_extension")]),
    (.extension_ExtensionType_try_calculate_account_len,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"pointer_width", "64"⟩] },
      [("spl_token_2022::extension::ExtensionType::try_calculate_account_len",
        "spl_token_2022::extension::ExtensionType::try_calculate_account_len")]),
    (.extension_StateWithExtensions_unpack,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"pointer_width", "64"⟩] },
      [("spl_token_2022::extension::StateWithExtensions::<'data, S>::unpack",
        "spl_token_2022::extension::StateWithExtensions::<'data, S>::unpack")]),
    (.extension_metadata_pointer_instruction_initialize,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩],
        dependencies := [⟨"solana-pubkey", "2.2.1", registry⟩, ⟨"solana-instruction", "2.2.\
          1",
          registry⟩, ⟨"solana-program-error", "2.2.0", registry⟩, ⟨"spl-pod", "0.5.1", registry⟩,
          ⟨"bytemuck", "1.22.0", registry⟩] },
      [("spl_token_2022::extension::metadata_pointer::instruction::initialize",
        "spl_token_2022::extension::metadata_pointer::instruction::initialize")]),
    (.extension_metadata_pointer_instruction_initialize,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩],
        dependencies := [⟨"solana-pubkey", "2.4.0", registry⟩, ⟨"solana-instruction", "2.3.\
          3",
          registry⟩, ⟨"solana-program-error", "2.2.0", registry⟩, ⟨"spl-pod", "0.5.1", registry⟩,
          ⟨"bytemuck", "1.24.0", registry⟩] },
      [("spl_token_2022::extension::metadata_pointer::instruction::initialize",
        "spl_token_2022::extension::metadata_pointer::instruction::initialize")]),
    (.extension_permanent_delegate_get_permanent_delegate,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        dependencies := [⟨"spl-pod", "0.5.1", registry⟩, ⟨"solana-pubkey", "2.4.0", registry⟩] },
      [("spl_token_2022::extension::permanent_delegate::get_permanent_delegate",
        "spl_token_2022::extension::permanent_delegate::get_permanent_delegate")]),
    (.extension_transfer_fee_TransferFeeConfig_calculate_epoch_fee,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        dependencies := [⟨"spl-pod", "0.5.1", registry⟩] },
      [("spl_token_2022::extension::transfer_fee::TransferFeeConfig::calculate_epoch_fee",
        "spl_token_2022::extension::transfer_fee::TransferFeeConfig::calculate_epoch_fee")]),
    (.extension_transfer_fee_TransferFeeConfig_calculate_inverse_epoch_fee,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        dependencies := [⟨"spl-pod", "0.5.1", registry⟩] },
      [("spl_token_2022::extension::transfer_fee::TransferFeeConfig::calculate_inverse_epoc\
        h_fee",
        "spl_token_2022::extension::transfer_fee::TransferFeeConfig::calculate_inverse_epoc\
          h_fee")]),
    (.instruction_initialize_mint_close_authority,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩],
        dependencies := [⟨"solana-pubkey", "2.2.1", registry⟩, ⟨"solana-instruction", "2.2.\
          1",
          registry⟩, ⟨"solana-program-error", "2.2.0", registry⟩] },
      [("spl_token_2022::instruction::initialize_mint_close_authority",
        "spl_token_2022::instruction::initialize_mint_close_authority")]),
    (.instruction_initialize_mint_close_authority,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩],
        dependencies := [⟨"solana-pubkey", "2.4.0", registry⟩, ⟨"solana-instruction", "2.3.\
          3",
          registry⟩, ⟨"solana-program-error", "2.2.0", registry⟩] },
      [("spl_token_2022::instruction::initialize_mint_close_authority",
        "spl_token_2022::instruction::initialize_mint_close_authority")]),
    (.id,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩],
        dependencies := [⟨"solana-pubkey", "2.2.1", registry⟩] },
      [("spl_token_2022::id", "spl_token_2022::id")]),
    (.id,
      {
        package := "spl-token-2022",
        version := "8.0.0",
        source := registry,
        target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩],
        dependencies := [⟨"solana-pubkey", "2.4.0", registry⟩] },
      [("spl_token_2022::id", "spl_token_2022::id")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"spl-token-2022", build.version, item, implementation⟩))

def members : List Key := [.extension_BaseStateWithExtensions_get_extension,
  .extension_BaseStateWithExtensions_get_extension_types,
  .extension_BaseStateWithExtensions_try_get_new_account_len_for_variable_len_extension,
  .extension_ExtensionType_try_calculate_account_len, .extension_StateWithExtensions_unpack,
  .extension_metadata_pointer_instruction_initialize,
  .extension_permanent_delegate_get_permanent_delegate,
  .extension_transfer_fee_TransferFeeConfig_calculate_epoch_fee,
  .extension_transfer_fee_TransferFeeConfig_calculate_inverse_epoch_fee,
  .instruction_initialize_mint_close_authority, .id]

theorem every_member_has_a_literal_case :
    members.length = 11 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["8.0.0", "8.0.1"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["8.0.2", "8.9.99+fixture"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["7.0.0", "9.0.0", "8.0.2-rc.1"].all (fun version => fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- An interval must not conceal a missing reference or a changed item range. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      !(Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability key).isEmpty &&
      (Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability key).all (fun profile =>
        decide (profile.releases = ["8.0.0", "8.0.1"] ∧
          profile.compatibleRanges = [⟨"8.0.0", "9.0.0"⟩]))) = true := by
  decide +kernel

theorem a_version_cannot_replace_the_defining_source :
    fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with package := "wrong-defining-package" } [] &&
      identitiesMatch key { build with source :=
        ⟨"git", "https://example.invalid/library", "012345678901234567890123456789012345678\
          9"⟩ } [] &&
      identitiesMatch key { build with source :=
        ⟨"registry", "https://example.invalid/registry", ""⟩ } []) = true := by
  decide +kernel

/-- Each required edge is checked independently. Duplicate compatible
candidates remain ambiguous actual dependency facts. -/
theorem dependency_facts_cannot_be_missing_wrong_or_ambiguous :
    fixtures.all (fun (key, build, _) => build.dependencies.all (fun required =>
      identitiesMatch key { build with dependencies := (build.dependencies.filter
        (fun dependency => dependency.package != required.package)) } [] &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with version := "99.0.0" } else dependency)) } [] &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with source :=
            ⟨"git", "https://example.invalid/dependency", "01234567890123456789012345678901\
              23456789"⟩ }
          else dependency)) } [] &&
      identitiesMatch key { build with dependencies := build.dependencies ++ [required] } [])) =
        true := by
  decide +kernel

/-- Provider references and compatible fixtures preserve the actual
identity of the caller; the provider version is not substituted for the defining crate. -/
theorem dependency_references_and_compatible_versions :
    ([("solana-program-error", ["2.2.0", "2.2.1", "2.2.2", "2.9.99", "2.9.99+fixture"])] : List
      (String × List String)).all (fun (package, versions) =>
      fixtures.all (fun (key, build, expected) => versions.all (fun version =>
        identitiesMatch key { build with dependencies := (build.dependencies.map
          (fun dependency => if dependency.package == package then
            { dependency with version := version } else dependency)) } expected))) = true := by
  decide +kernel

/-- In particular, the unit BorshIoError of ProgramError 3 cannot replace the
selected owned String carrier. Other rows enforce their declared bounds. -/
theorem dependency_bounds_retain_the_selected_domains :
    ([("solana-program-error", ["2.1.0", "3.0.0", "2.2.2-rc.1"])] : List (String × List
      String)).all (fun (package, versions) =>
      fixtures.all (fun (key, build, _) => if (build.dependency package).isSome then
        versions.all (fun version => identitiesMatch key
          { build with dependencies := (build.dependencies.map (fun dependency =>
            if dependency.package == package then { dependency with version := version }
            else dependency)) } []) else true)) = true := by
  decide +kernel

/-- A missing fact is unknown. Wrong and duplicated facts cannot be supplied
by the host machine or hidden by another valid field. -/
theorem target_facts_are_operation_specific :
    fixtures.all (fun (key, build, _) => build.target.all (fun required =>
      let changed : Versioning.TargetFact :=
        ⟨required.field, if required.field == "pointer_width" then "32"
          else if required.field == "os" then "linux"
          else if required.field == "endian" then "big" else "unwind"⟩
      identitiesMatch key { build with target := (build.target.filter
        (fun fact => fact.field != required.field)) } [] &&
      identitiesMatch key { build with target := (build.target.map
        (fun fact => if fact.field == required.field then changed else fact)) } [] &&
      identitiesMatch key { build with target := build.target ++ [required] } [])) = true := by
  decide +kernel

end SolanalibTest.Specs.SplToken2022.Models.ExtensionProfiles

namespace SolanalibTest.Specs.SplToken2022.Models.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def extension_StateWithExtensions_get_tlv_dataBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def extension_StateWithExtensions_get_tlv_dataCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (extension_StateWithExtensions_get_tlv_dataBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ extension_StateWithExtensions_get_tlv_dataBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (extension_StateWithExtensions_get_tlv_dataBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ extension_StateWithExtensions_get_tlv_dataBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ extension_StateWithExtensions_get_tlv_dataBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ extension_StateWithExtensions_get_tlv_dataBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ extension_StateWithExtensions_get_tlv_dataBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ extension_StateWithExtensions_get_tlv_dataBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ extension_StateWithExtensions_get_tlv_dataBuild with version := "7.999.999" }, false)
]

set_option maxRecDepth 8192 in
theorem extension_StateWithExtensions_get_tlv_data_profile_controls :
    extension_StateWithExtensions_get_tlv_dataCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .extension_StateWithExtensions_get_tlv_data).any
        (fun profile =>
          ["spl-token-2022-8.0.1-extension-StateWithExtensions-get_tlv_data"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem extension_StateWithExtensions_get_tlv_data_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { extension_StateWithExtensions_get_tlv_dataBuild with version := version }).identities
          .extension_StateWithExtensions_get_tlv_data).eraseDups ==
        [⟨"spl-token-2022", version,
          "spl_token_2022::extension::BaseStateWithExtensions::get_tlv_data",
          "<spl_token_2022::extension::StateWithExtensions<'_, S> as \
            spl_token_2022::extension::BaseStateWithExtensions<S>>::get_tlv_data"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def extension_transfer_fee_TransferFee_calculate_feeBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := [⟨"spl-pod", "0.5.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def extension_transfer_fee_TransferFee_calculate_feeCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (extension_transfer_fee_TransferFee_calculate_feeBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (extension_transfer_fee_TransferFee_calculate_feeBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with package := "unrelated-sourc\
    e" },
    false),
  -- wrong-origin; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- dependency-reference-spl-pod-0.5.1; eligible
  (extension_transfer_fee_TransferFee_calculate_feeBuild, true),
  -- dependency-spl-pod-lower; eligible
  (extension_transfer_fee_TransferFee_calculate_feeBuild, true),
  -- dependency-spl-pod-hypothetical-declaration-probe; eligible
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_feeBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.5.98" } else dependency))
    }, true),
  -- dependency-spl-pod-exclusive-upper; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_feeBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.6.0" } else dependency))
    }, false),
  -- dependency-spl-pod-unlisted-prerelease; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_feeBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.5.1-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-spl-pod; unresolved
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_feeBuild.dependencies.filter (fun dependency =>
    dependency.package != "spl-pod")) }, false),
  -- wrong-dependency-origin-spl-pod; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_feeBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "spl-pod" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-spl-pod; ValueError containing Ambiguous dependency
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_feeBuild.dependencies ++ [⟨
    "spl-pod", "0.5.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with version := "7.999.999" }, false),
  -- dependency-spl-pod-below-lower-bound-fixture-0.5.0; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_feeBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.5.0" } else dependency))
    }, false)
]

set_option maxRecDepth 8192 in
theorem extension_transfer_fee_TransferFee_calculate_fee_profile_controls :
    extension_transfer_fee_TransferFee_calculate_feeCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .extension_transfer_fee_TransferFee_calculate_fee).any
        (fun profile =>
          ["spl-token-2022-8.0.1-extension-transfer_fee-TransferFee-calculate_fee"].contains
          profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem extension_transfer_fee_TransferFee_calculate_fee_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { extension_transfer_fee_TransferFee_calculate_feeBuild with version := version
          }).identities .extension_transfer_fee_TransferFee_calculate_fee).eraseDups ==
        [⟨"spl-token-2022", version,
          "spl_token_2022::extension::transfer_fee::TransferFee::calculate_fee",
          "spl_token_2022::extension::transfer_fee::TransferFee::calculate_fee"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def extension_transfer_fee_TransferFee_calculate_inverse_feeBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := [⟨"spl-pod", "0.5.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def extension_transfer_fee_TransferFee_calculate_inverse_feeCases : List (Versioning.Build × Bool)
  := [
  -- inspected-reference-8.0.0; eligible
  (extension_transfer_fee_TransferFee_calculate_inverse_feeBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (extension_transfer_fee_TransferFee_calculate_inverse_feeBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with version := "8.0.97" },
    true),
  -- exclusive-upper; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with version := "9.0.0" },
    false),
  -- unlisted-prerelease; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with version := "8.0.0-r\
    c.1" },
    false),
  -- wrong-package; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with package :=
    "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- dependency-reference-spl-pod-0.5.1; eligible
  (extension_transfer_fee_TransferFee_calculate_inverse_feeBuild, true),
  -- dependency-spl-pod-lower; eligible
  (extension_transfer_fee_TransferFee_calculate_inverse_feeBuild, true),
  -- dependency-spl-pod-hypothetical-declaration-probe; eligible
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_inverse_feeBuild.dependencies.map (fun dependency
    => if dependency.package == "spl-pod" then { dependency with version := "0.5.98" } else
    dependency)) }, true),
  -- dependency-spl-pod-exclusive-upper; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_inverse_feeBuild.dependencies.map (fun dependency
    => if dependency.package == "spl-pod" then { dependency with version := "0.6.0" } else
    dependency)) }, false),
  -- dependency-spl-pod-unlisted-prerelease; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_inverse_feeBuild.dependencies.map (fun dependency
    => if dependency.package == "spl-pod" then { dependency with version := "0.5.1-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-spl-pod; unresolved
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_inverse_feeBuild.dependencies.filter (fun
    dependency => dependency.package != "spl-pod")) }, false),
  -- wrong-dependency-origin-spl-pod; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_inverse_feeBuild.dependencies.map (fun dependency
    => if dependency.package ==
    "spl-pod" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-spl-pod; ValueError containing Ambiguous dependency
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_inverse_feeBuild.dependencies ++ [⟨
    "spl-pod", "0.5.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with version := "7.999.9\
    99" },
    false),
  -- dependency-spl-pod-below-lower-bound-fixture-0.5.0; unsupported
  ({ extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFee_calculate_inverse_feeBuild.dependencies.map (fun dependency
    => if dependency.package == "spl-pod" then { dependency with version := "0.5.0" } else
    dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem extension_transfer_fee_TransferFee_calculate_inverse_fee_profile_controls :
    extension_transfer_fee_TransferFee_calculate_inverse_feeCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .extension_transfer_fee_TransferFee_calculate_inverse_fee).any
        (fun profile =>
          ["spl-token-2022-8.0.1-extension-transfer_\
        fee-TransferFee-calculate_inverse_fee"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem extension_transfer_fee_TransferFee_calculate_inverse_fee_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { extension_transfer_fee_TransferFee_calculate_inverse_feeBuild with version := version
          }).identities .extension_transfer_fee_TransferFee_calculate_inverse_fee).eraseDups ==
        [⟨"spl-token-2022", version,
          "spl_token_2022::extension::transfer_fee::TransferFee::calculate_inverse_fee",
          "spl_token_2022::extension::transfer_fee::TransferFee::calculate_inverse_fee"⟩])) = true
          := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := [⟨"spl-pod", "0.5.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def extension_transfer_fee_TransferFeeConfig_get_epoch_feeCases : List (Versioning.Build × Bool) :=
  [
  -- inspected-reference-8.0.0; eligible
  (extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with version := "8.0.0-rc.\
    1" },
    false),
  -- wrong-package; unsupported
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with package := "unrelated\
    -source"
    }, false),
  -- wrong-origin; unsupported
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- dependency-reference-spl-pod-0.5.1; eligible
  (extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild, true),
  -- dependency-spl-pod-lower; eligible
  (extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild, true),
  -- dependency-spl-pod-hypothetical-declaration-probe; eligible
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild.dependencies.map (fun dependency
    => if dependency.package == "spl-pod" then { dependency with version := "0.5.98" } else
    dependency)) }, true),
  -- dependency-spl-pod-exclusive-upper; unsupported
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild.dependencies.map (fun dependency
    => if dependency.package == "spl-pod" then { dependency with version := "0.6.0" } else
    dependency)) }, false),
  -- dependency-spl-pod-unlisted-prerelease; unsupported
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild.dependencies.map (fun dependency
    => if dependency.package == "spl-pod" then { dependency with version := "0.5.1-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-spl-pod; unresolved
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild.dependencies.filter (fun
    dependency => dependency.package != "spl-pod")) }, false),
  -- wrong-dependency-origin-spl-pod; unsupported
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild.dependencies.map (fun dependency
    => if dependency.package ==
    "spl-pod" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-spl-pod; ValueError containing Ambiguous dependency
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild.dependencies ++ [⟨
    "spl-pod", "0.5.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with version := "7.999.999" },
    false),
  -- dependency-spl-pod-below-lower-bound-fixture-0.5.0; unsupported
  ({ extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with dependencies :=
    (extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild.dependencies.map (fun dependency
    => if dependency.package == "spl-pod" then { dependency with version := "0.5.0" } else
    dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem extension_transfer_fee_TransferFeeConfig_get_epoch_fee_profile_controls :
    extension_transfer_fee_TransferFeeConfig_get_epoch_feeCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .extension_transfer_fee_TransferFeeConfig_get_epoch_fee).any
        (fun profile =>
          ["spl-token-2022-8.0.1-extension-transfer_fee-TransferFeeConfig-get_epoch_fee"].contains
          profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem extension_transfer_fee_TransferFeeConfig_get_epoch_fee_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { extension_transfer_fee_TransferFeeConfig_get_epoch_feeBuild with version := version
          }).identities .extension_transfer_fee_TransferFeeConfig_get_epoch_fee).eraseDups ==
        [⟨"spl-token-2022", version,
          "spl_token_2022::extension::transfer_fee::TransferFeeConfig::get_epoch_fee",
          "spl_token_2022::extension::transfer_fee::TransferFeeConfig::get_epoch_fee"⟩])) = true :=
          by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def extension_transfer_hook_get_program_idBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := [⟨"spl-pod", "0.5.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def extension_transfer_hook_get_program_idCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (extension_transfer_hook_get_program_idBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ extension_transfer_hook_get_program_idBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (extension_transfer_hook_get_program_idBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ extension_transfer_hook_get_program_idBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ extension_transfer_hook_get_program_idBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ extension_transfer_hook_get_program_idBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ extension_transfer_hook_get_program_idBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ extension_transfer_hook_get_program_idBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- dependency-reference-spl-pod-0.5.1; eligible
  (extension_transfer_hook_get_program_idBuild, true),
  -- dependency-spl-pod-lower; eligible
  (extension_transfer_hook_get_program_idBuild, true),
  -- dependency-spl-pod-hypothetical-declaration-probe; eligible
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.5.98" } else dependency))
    }, true),
  -- dependency-spl-pod-exclusive-upper; unsupported
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.6.0" } else dependency))
    }, false),
  -- dependency-spl-pod-unlisted-prerelease; unsupported
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.5.1-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-spl-pod; unresolved
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.filter (fun dependency =>
    dependency.package != "spl-pod")) }, false),
  -- wrong-dependency-origin-spl-pod; unsupported
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "spl-pod" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-spl-pod; ValueError containing Ambiguous dependency
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies ++ [⟨
    "spl-pod", "0.5.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (extension_transfer_hook_get_program_idBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.3.0" } else
    dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.4.0" } else
    dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (extension_transfer_hook_get_program_idBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.98" } else
    dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ extension_transfer_hook_get_program_idBuild with version := "7.999.999" }, false),
  -- dependency-spl-pod-below-lower-bound-fixture-0.5.0; unsupported
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package == "spl-pod" then { dependency with version := "0.5.0" } else dependency))
    }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ extension_transfer_hook_get_program_idBuild with dependencies :=
    (extension_transfer_hook_get_program_idBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.0" } else
    dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem extension_transfer_hook_get_program_id_profile_controls :
    extension_transfer_hook_get_program_idCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .extension_transfer_hook_get_program_id).any
        (fun profile => ["spl-token-2022-8.0.1-extension-transfer_hook-get_program_id"].contains
          profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem extension_transfer_hook_get_program_id_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { extension_transfer_hook_get_program_idBuild with version := version }).identities
          .extension_transfer_hook_get_program_id).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::extension::transfer_hook::get_program\
          _id",
          "spl_token_2022::extension::transfer_hook::get_program_id"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def state_Account_is_frozenBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def state_Account_is_frozenCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (state_Account_is_frozenBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ state_Account_is_frozenBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (state_Account_is_frozenBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ state_Account_is_frozenBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ state_Account_is_frozenBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ state_Account_is_frozenBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ state_Account_is_frozenBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ state_Account_is_frozenBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ state_Account_is_frozenBuild with version := "7.999.999" }, false)
]

set_option maxRecDepth 8192 in
theorem state_Account_is_frozen_profile_controls :
    state_Account_is_frozenCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .state_Account_is_frozen).any
        (fun profile => ["spl-token-2022-8.0.1-state-Account-is_frozen"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem state_Account_is_frozen_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { state_Account_is_frozenBuild with version := version }).identities
          .state_Account_is_frozen).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::state::Account::is_frozen",
          "spl_token_2022::state::Account::is_frozen"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.SplToken2022.Models.Pr575Compatibility
