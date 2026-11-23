/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaAccountInfo
public import Solanalib.Specs.SolanaAccountInfo.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaAccountInfo.AccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AccountInfo

def mutablyBorrowed : State := (tryBorrowMutData sampleState sampleArgs).2

/-- the mutable borrow of AccountInfo has no metadata writability check. -/
theorem readonly_mutable_borrow : sampleInfo.isWritable = false ∧
    (tryBorrowMutData sampleState sampleArgs).1 = .ok ⟨0, 0⟩ := ⟨rfl, rfl⟩

/-- Both cloned handles alias the original cells; an outstanding data guard
therefore blocks a shared borrow through the clone. -/
theorem clone_alias_conflict :
    tryBorrowData mutablyBorrowed { sampleArgs with info := clone sampleInfo } =
      (.error .accountBorrowFailed, mutablyBorrowed) := rfl

/-- The unchecked getter panics at the same conflict that the checked method
reports as an ordinary SDK error. -/
theorem data_len_panics : observeReference .dataLen mutablyBorrowed sampleArgs
    (.unwound .borrowFailed mutablyBorrowed) := rfl

/-- Panic-abort has no invented state after termination. -/
theorem data_len_aborts : observeReference .dataLen mutablyBorrowed
    { sampleArgs with profile := { sampleProfile with aborts := true } }
    (.terminated .borrowFailed) := rfl

/-- Borrowing the data cell does not prevent reading the independent balance. -/
theorem independent_lamports :
    (observe .lamports mutablyBorrowed sampleInfo).1 = .value 40 ∧
    (observe .lamports mutablyBorrowed sampleInfo).2.exclusiveCount sampleInfo.data = 1 ∧
    (observe .lamports mutablyBorrowed sampleInfo).2.sharedCount sampleInfo.lamports = 0 :=
  ⟨rfl, rfl, rfl⟩

def changed : State :=
  (Borrow.write mutablyBorrowed ⟨0, 0⟩ (.data [99, 98, 97, 96])).2

/-- A guard observes current data, and releasing it does not restore old bytes. -/
theorem mutation_then_release :
    Borrow.current changed ⟨0, 0⟩ = .ok (.whole, .data [99, 98, 97, 96]) ∧
    (observe .dataLen (Borrow.release changed ⟨0, 0⟩).2 (clone sampleInfo)).1 = .value 4 :=
  ⟨rfl, rfl⟩

/-- Releasing a guard consumes its token; neither the old token nor a clone of
that token can be used to release the lease again. -/
theorem consumed_guard :
    (Borrow.release (Borrow.release changed ⟨0, 0⟩).2 ⟨0, 0⟩).1 = .error .invalidGuard := rfl

def smallProfile : Profile := ⟨2, false⟩
def smallState : State :=
  ⟨[⟨.lamports 1, smallProfile.policy⟩, ⟨.data [], smallProfile.policy⟩], []⟩
def smallArgs : Args := ⟨smallProfile, sampleInfo⟩

/-- A second shared acquisition reaches the explicitly chosen signed-counter
bound. This is a small mathematical instance, not a claim about target width. -/
theorem configured_saturation :
    (tryBorrowData (tryBorrowData smallState smallArgs).2 smallArgs).1 =
      .error .accountBorrowFailed := rfl

theorem target_limit : sampleProfile.policy.sharedLimit = 2^63 - 1 := rfl

/-- An arbitrary interpretation satisfying the checked contract must expose
the exact common acquisition result; the client does not unfold that interpreter. -/
theorem shared_result_of_contract
    (run : State → Args → Outcome State (Except ProgramError.Value Borrow.Guard) Empty Empty → Prop)
    (spec : Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_data_contract.Holds run)
    (value : Except ProgramError.Value Borrow.Guard) (after : State)
    (step : run sampleState sampleArgs (.returned value after)) :
    value = .ok ⟨0, 0⟩ ∧ after = (tryBorrowData sampleState sampleArgs).2 := by
  have post := spec sampleState sampleArgs (.returned value after) sample_valid.dataBorrowReady step
  have pair := post.1
  change tryBorrowData sampleState sampleArgs = (value, after) at pair
  exact ⟨(congrArg Prod.fst pair).symm, (congrArg Prod.snd pair).symm⟩

/-- Conversion preserves the special custom-zero encoding of the SDK and its
truncating fallback for unrecognized raw status words. -/
theorem program_error_encoding :
    ProgramError.V3_0_1.toStatus (.custom 0) = 4294967296 ∧
    ProgramError.V3_0_1.fromStatus 4294967297 = .custom 1 ∧
    ProgramError.V3_0_1.fromStatus 51539607552 = .accountBorrowFailed := ⟨rfl, rfl, rfl⟩

/-- This mathematical input has only data, with no source-shaped AccountInfo
lamports cell or target width. Its actual data-cell policy still governs borrowing. -/
def dataOnly : State := ⟨[⟨.data [7, 8, 9], .refCell 64⟩], []⟩

def abstractArgs : Args :=
  { sampleArgs with profile := ⟨0, false⟩, info := { sampleInfo with data := ⟨0⟩ } }

/-- The exact checked contract admits the narrower input and proves both final
protocol validity and readability of its returned data guard. -/
theorem data_only_borrow_has_typed_post :
    ¬ Valid abstractArgs.profile dataOnly abstractArgs.info ∧
      Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_data_contract.requires dataOnly
        abstractArgs ∧
      Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_data_contract.post dataOnly
        abstractArgs
        (.returned (.ok ⟨0, 0⟩) (tryBorrowData dataOnly abstractArgs).2) := by
  have ready : DataBorrowReady dataOnly abstractArgs.info :=
    ⟨Borrow.State.valid_empty_slots _, [7, 8, 9], .refCell 64, rfl⟩
  refine ⟨?_, ready, ?_⟩
  · intro valid
    exact (by decide : ¬ 2 ≤ (0 : Nat)) valid.1
  · exact Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_data_reference_holds
      dataOnly abstractArgs _ ready rfl

/-- A getter uses the selected typed cell without requiring the unused cell. -/
theorem selected_cell_getter_executes :
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_len_contract.requires dataOnly abstractArgs ∧
      Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_len_reference dataOnly abstractArgs
        (.returned 3 (observe .dataLen dataOnly abstractArgs.info).2) :=
  ⟨⟨_, 3, rfl, rfl⟩, rfl⟩

/-- A present lamports cell is not sufficient for a data borrow or data getter. -/
theorem wrong_cell_kind_is_not_admitted :
    let wrong : State := ⟨[⟨.lamports 7, .refCell 64⟩], []⟩
    ¬ DataBorrowReady wrong abstractArgs.info ∧
      ¬ ObservationReady .dataLen wrong abstractArgs.info := by
  constructor
  · rintro ⟨_, bytes, policy, present⟩
    simp [abstractArgs, sampleInfo, Borrow.State.lookupCell] at present
  · rintro ⟨cell, value, present, project⟩
    have same : cell = ⟨.lamports 7, .refCell 64⟩ := by
      simpa [abstractArgs, sampleInfo, Observation.handle, Borrow.State.lookupCell] using
        present.symm
    subst cell
    cases project

/-- The supporting clone observation is total even without source cells. -/
theorem clone_observation_needs_no_cells :
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_observation_contract.requires
      Borrow.State.empty abstractArgs ∧
      Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_observation_reference
        Borrow.State.empty abstractArgs (.returned abstractArgs.info Borrow.State.empty) :=
  ⟨True.intro, rfl⟩

end SolanalibTest.Specs.SolanaAccountInfo.AccountInfo

namespace SolanalibTest.Specs.SolanaAccountInfo.AccountInfo.AsRefProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.SolanaAccountInfo.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.AccountInfo_as_ref,
      {
        package := "solana-account-info",
        version := "2.3.0",
        source := registry },
      [("core::convert::AsRef::as_ref",
        "<solana_account_info::AccountInfo<'a> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'a>>>::as_ref"),
        ("core::convert::AsRef::as_ref",
          "<solana_account_info::AccountInfo<'_> as \
            core::convert::AsRef<solana_account_info::AccountInfo<'_>>>::as_ref")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.SolanaAccountInfo.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"solana-account-info", build.version, item, implementation⟩))

def members : List Key := [.AccountInfo_as_ref]

theorem every_member_has_a_literal_case :
    members.length = 1 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["2.3.0"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["2.3.1", "2.9.99+fixture"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["2.2.1", "3.0.0", "2.3.1-rc.1"].all (fun version => fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- An interval must not conceal a missing reference or a changed item range. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      let profiles := (Solanalib.Specs.SolanaAccountInfo.Capabilities.catalog.applicability
        key).filter
        (fun profile =>
          ["sdk-account-info-solana-account-info-2.3.0:0",
            "sdk-account-info-solana-account-info-2.3.0:1"].contains profile.id)
      !profiles.isEmpty &&
      profiles.all (fun profile =>
        decide (profile.releases = ["2.3.0"] ∧
          profile.compatibleRanges = [⟨"2.3.0", "3.0.0"⟩]))) = true := by
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

end SolanalibTest.Specs.SolanaAccountInfo.AccountInfo.AsRefProfiles

namespace SolanalibTest.Specs.SolanaAccountInfo.AccountInfo.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def AccountInfo_data_is_emptyBuild : Versioning.Build where
  package := "solana-account-info"
  version := "2.1.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def AccountInfo_data_is_emptyCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-2.1.0; eligible
  (AccountInfo_data_is_emptyBuild, true),
  -- inspected-reference-2.2.1; eligible
  ({ AccountInfo_data_is_emptyBuild with version := "2.2.1" }, true),
  -- inspected-reference-2.3.0; eligible
  ({ AccountInfo_data_is_emptyBuild with version := "2.3.0" }, true),
  -- lower; eligible
  (AccountInfo_data_is_emptyBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ AccountInfo_data_is_emptyBuild with version := "2.1.97" }, true),
  -- exclusive-upper; unsupported
  ({ AccountInfo_data_is_emptyBuild with version := "3.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ AccountInfo_data_is_emptyBuild with version := "2.1.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ AccountInfo_data_is_emptyBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ AccountInfo_data_is_emptyBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-2.0.999; unsupported
  ({ AccountInfo_data_is_emptyBuild with version := "2.0.999" }, false)
]

set_option maxRecDepth 8192 in
theorem AccountInfo_data_is_empty_profile_controls :
    AccountInfo_data_is_emptyCases.all (fun test =>
      (((Solanalib.Specs.SolanaAccountInfo.Capabilities.catalog.applicability
        .AccountInfo_data_is_empty).any
        (fun profile => ["sdk-account-info-solana-account-info-2.3.0:0",
          "sdk-account-info-solana-account-info-2.3.0:1"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem AccountInfo_data_is_empty_callable_identities :
    ["2.1.0", "2.2.1", "2.3.0", "2.1.97"].all (fun version =>
      (((Solanalib.Specs.SolanaAccountInfo.Capabilities.catalog.forBuild
        { AccountInfo_data_is_emptyBuild with version := version }).identities
          .AccountInfo_data_is_empty).eraseDups ==
        [⟨"solana-account-info", version, "solana_account_info::AccountInfo::<'a>::data_is_\
          empty",
          "solana_account_info::AccountInfo::<'a>::data_is_empty"⟩, ⟨"solana-account-info",
          version, "solana_account_info::AccountInfo::<'_>::data_is_empty",
          "solana_account_info::AccountInfo::<'_>::data_is_empty"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaAccountInfo.AccountInfo.Pr575Compatibility

namespace SolanalibTest.Specs.SolanaAccountInfo.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SolanaAccountInfo.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SolanaAccountInfo.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

abbrev Row := Solanalib.Specs.SolanaAccountInfo.Capabilities.Key × String × String × String

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
  package := "solana-account-info"
  version := "3.1.1"
  source := registry

def rows0 : List Row := [
    (.AccountInfo_assign, "sdk-account-info-solana-account-info-3.1.1:0",
      "solana_account_info::AccountInfo::<'a>::assign",
        "solana_account_info::AccountInfo::<'a>::assign"),
    (.AccountInfo_assign, "sdk-account-info-solana-account-info-3.1.1:1",
      "solana_account_info::AccountInfo::<'_>::assign",
        "solana_account_info::AccountInfo::<'_>::assign"),
    (.AccountInfo_try_data_len, "sdk-account-info-solana-account-info-3.1.1:0",
      "solana_account_info::AccountInfo::<'a>::try_data_len",
        "solana_account_info::AccountInfo::<'a>::try_data_len"),
    (.AccountInfo_try_data_len, "sdk-account-info-solana-account-info-3.1.1:1",
      "solana_account_info::AccountInfo::<'_>::try_data_len",
        "solana_account_info::AccountInfo::<'_>::try_data_len"),
    (.AccountInfo_as_ref, "sdk-account-info-solana-account-info-3.1.1:0",
      "core::convert::AsRef::as_ref",
        "<solana_account_info::AccountInfo<'a> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'a>>>::as_ref"),
    (.AccountInfo_as_ref, "sdk-account-info-solana-account-info-3.1.1:1",
      "core::convert::AsRef::as_ref",
        "<solana_account_info::AccountInfo<'_> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'_>>>::as_ref"),
    (.AccountInfo_data_is_empty, "sdk-account-info-solana-account-info-3.1.1:0",
      "solana_account_info::AccountInfo::<'a>::data_is_empty",
        "solana_account_info::AccountInfo::<'a>::data_is_empty"),
    (.AccountInfo_data_is_empty, "sdk-account-info-solana-account-info-3.1.1:1",
      "solana_account_info::AccountInfo::<'_>::data_is_empty",
        "solana_account_info::AccountInfo::<'_>::data_is_empty"),
    (.AccountInfo_try_borrow_mut_lamports, "sdk-account-info-solana-account-info-3.1.1:0",
      "solana_account_info::AccountInfo::<'a>::try_borrow_mut_lamports",
        "solana_account_info::AccountInfo::<'a>::try_borrow_mut_lamports"),
    (.AccountInfo_try_borrow_mut_lamports, "sdk-account-info-solana-account-info-3.1.1:1",
      "solana_account_info::AccountInfo::<'_>::try_borrow_mut_lamports",
        "solana_account_info::AccountInfo::<'_>::try_borrow_mut_lamports")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 10 ∧
    ["3.1.1", "3.1.2"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "3.1.0" },
  { build0 with version := "4.0.0" },
  { build0 with version := "3.1.2-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 5 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

def build1 : Build where
  package := "solana-account-info"
  version := "3.1.1"
  source := registry
  target := [⟨"os", "solana"⟩]
  dependencies := [
    ⟨"solana-program-memory", "3.0.0", registry⟩]

def rows1 : List Row := [
    (.AccountInfo_resize, "sdk-account-info-solana-account-info-3.1.1:0",
      "solana_account_info::AccountInfo::<'a>::resize",
        "solana_account_info::AccountInfo::<'a>::resize"),
    (.AccountInfo_resize, "sdk-account-info-solana-account-info-3.1.1:1",
      "solana_account_info::AccountInfo::<'_>::resize",
        "solana_account_info::AccountInfo::<'_>::resize")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_1 :
    rows1.length = 2 ∧
    ["3.1.1", "3.1.2"].all (fun version =>
      rows1.all (identifies { build1 with version := version })) = true := by
  decide +kernel

def accepted1 : List Build := [
  dependencyVersion build1 "solana-program-memory" "3.1.0",
  dependencyVersion build1 "solana-program-memory" "3.0.1"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_1 :
    accepted1.length = 2 ∧
    accepted1.all (fun build => rows1.all (identifies build)) = true := by
  decide +kernel

def rejected1 : List Build := [
  { build1 with version := "3.1.0" },
  { build1 with version := "4.0.0" },
  { build1 with version := "3.1.2-rc.1" },
  { build1 with package := "unrelated-library" },
  { build1 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build1 "solana-program-memory" "4.0.0",
  { build1 with dependencies := (build1.dependencies.filter (fun dep => dep.package !=
    "solana-program-memory")) },
  { build1 with dependencies := (build1.dependencies ++ [⟨"solana-program-memory", "3.0.0",
    registry⟩]) },
  { build1 with dependencies := (build1.dependencies.map (fun dep =>
        if dep.package == "solana-program-memory" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build1 with target := (build1.target.filter (fun fact => fact.field != "os")) },
  { build1 with target := (build1.target.map (fun fact =>
        if fact.field == "os" then { fact with value := "linux" } else fact)) },
  { build1 with target := (build1.target ++ [⟨"os", "linux"⟩]) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_1 :
    rejected1.length = 12 ∧
    rejected1.all (fun build => rows1.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaAccountInfo.UpdatedProfiles
