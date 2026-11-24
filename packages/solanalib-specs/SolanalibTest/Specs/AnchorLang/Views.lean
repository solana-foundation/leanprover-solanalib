/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.Views
public import Solanalib.Specs.AnchorLang.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.Views

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews
open Solanalib.Specs.AnchorLang

/-- The returned mutable view writes the real decoded field immediately. -/
theorem mutable_write_visible :
    readPayload (writePayload Sample.store ⟨Sample.guard, true⟩ 91).2
      ⟨Sample.guard, true⟩ = some 91 :=
  read_after_write rfl Sample.writable.2 91

/-- A shared projection can read but cannot authorize a write. -/
theorem shared_write_rejected :
    writePayload Sample.store ⟨Sample.guard, false⟩ 91 = (.error .wrongMode, Sample.store) := rfl

/-- Even a mutable marker cannot manufacture an exclusive parent loan. -/
theorem shared_parent_rejected :
    let store : Store Nat :=
      ⟨Sample.store.cells, [some { Sample.slot with mode := .shared }]⟩
    (writePayload store ⟨Sample.guard, true⟩ 91).1 = .error .wrongMode := rfl

/-- A reference is unusable after its source loan ends. -/
theorem released_reference_dead :
    readPayload (Borrow.release Sample.store Sample.guard).2 ⟨Sample.guard, true⟩ = none :=
  read_after_release rfl true

/-- Different wrapper objects can refer to the same AccountInfo object while
their decoded field identities remain different. -/
theorem cloned_info_alias_payload_distinct :
    let store : Store Nat :=
      ⟨(Sample.cloneAfter .borrowed).1.cells,
        [some Sample.slot, some { Sample.slot with cell := ⟨1⟩ }]⟩
    let first := (infoReference .borrowed (store, ()) Sample.guard).1
    let second := (infoReference .borrowed (store, ()) ⟨1, 0⟩).1
    first.location = second.location ∧
      payloadLocation store ⟨Sample.guard, false⟩ ≠ payloadLocation store ⟨⟨1, 0⟩, false⟩ := by
  decide

/-- Clone invokes the supplied trait and can return a different decoded value.
Reference storage skips both Rc clone operations. -/
theorem clone_calls_actual_payload :
    Solanalib.Specs.AnchorLang.accounts.account.Account.clone_borrowed_info_run (Sample.cloneTypes
      .borrowed) Sample.before Sample.guard
      (.returned ⟨1⟩ (Sample.cloneAfter .borrowed)) ∧
      (Sample.cloneAfter .borrowed).2 = ["clone"] :=
  ⟨Sample.clone_run .borrowed, rfl⟩

def readonlyWrapper : Wrapper Nat :=
  { Sample.wrapper with account := { Sample.wrapper.account with info := AccountInfo.sampleInfo } }
def readonlyStore : Store Nat := ⟨[⟨some readonlyWrapper, Sample.policy⟩], [some Sample.slot]⟩

/-- The debug-disabled source does not inspect is_writable. -/
theorem nondebug_mutable_readonly :
    mutableRun { Sample.mutableTypes with debug := false } (readonlyStore, []) Sample.guard
      (.returned ⟨Sample.guard, true⟩ (readonlyStore, [])) := rfl

/-- A valid exclusive source loan does not remove the debug writability check.
The message reaches the panic callback in its updated auxiliary state. -/
theorem debug_readonly_logs_before_panic :
    (Solanalib.Specs.AnchorLang.accounts.account.Account.deref_mut_contract.contract
      Sample.mutableTypes).requires
      (readonlyStore, ["before"]) Sample.guard ∧
    Solanalib.Specs.AnchorLang.accounts.account.Account.deref_mut_run Sample.mutableTypes
      (readonlyStore, ["before"]) Sample.guard
      (.unwound "explicit panic"
        (readonlyStore, ["before", "The given Account is not mutable"])) := by
  constructor
  · exact ⟨⟨readonlyWrapper, rfl⟩, Sample.slot, rfl, rfl⟩
  · refine ⟨.returned () (readonlyStore, ["before", "The given Account is not mutable"]),
      ⟨.returned () ["before", "The given Account is not mutable"], rfl, rfl⟩, ?_⟩
    exact ⟨.unwound "explicit panic"
      (readonlyStore, ["before", "The given Account is not mutable"]),
      ⟨.unwound "explicit panic" ["before", "The given Account is not mutable"], rfl, rfl⟩,
      rfl⟩

def terminatingLog : MutableTypes :=
  { Sample.mutableTypes with
    log := Callback.ofFunction fun _ _ => .terminated "log exhausted" }

/-- A terminal logging dependency stops before the panic dependency and
provides no fictitious post-state. -/
theorem debug_log_terminal_is_retained :
    Solanalib.Specs.AnchorLang.accounts.account.Account.deref_mut_run terminatingLog
      (readonlyStore, []) Sample.guard
      (.terminated "log exhausted") :=
  ⟨.terminated "log exhausted", ⟨.terminated "log exhausted", rfl, rfl⟩, rfl⟩

def unwindingLog : MutableTypes where
  Payload := Nat
  Aux := List String
  Unwind := String
  Terminal := String
  debug := true
  log := Callback.ofFunction fun state message => .unwound "log failed" (state ++ [message])
  panic := Sample.mutableTypes.panic

/-- An unwind from logging preserves its effects and skips the later panic. -/
theorem debug_log_unwind_is_retained :
    Solanalib.Specs.AnchorLang.accounts.account.Account.deref_mut_run unwindingLog (readonlyStore,
      ["before"]) Sample.guard
      (.unwound "log failed"
        (readonlyStore, ["before", "The given Account is not mutable"])) :=
  ⟨.unwound "log failed" (readonlyStore, ["before", "The given Account is not mutable"]),
    ⟨.unwound "log failed" ["before", "The given Account is not mutable"], rfl, rfl⟩, rfl⟩

open Solanalib.Contracts.Model.Versioning
open Solanalib.Contracts.Model.Capabilities (RustIdentity)
open Solanalib.Specs.AnchorLang.Capabilities (catalog)

/-- None of these five source profiles adds a target, provider or feature gate.
The debug index of the mutable family remains explicit. -/
def viewBuild : Build where
  package := "anchor-lang"
  version := "0.32.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Exact source mappings, including distinct borrowed receivers sharing a family.
The expected identities are independent of the generated catalog. -/
def viewCases (version : String) :
    List (Solanalib.Specs.AnchorLang.Capabilities.Key × List RustIdentity) :=
  [(.accounts_account_Account_clone_borrowed_info,
      [⟨"anchor-lang", version, "core::clone::Clone::clone",
        "<anchor_lang::accounts::account::Account<'info, T> as core::clone::Clone>::clone"⟩,
       ⟨"anchor-lang", version, "core::clone::Clone::clone",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          core::clone::Clone>::clone"⟩]),
   (.accounts_borrowed_info_ref,
      [⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
       ⟨"anchor-lang", version, "core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::program::Program<'info, T> as \
          core::ops::deref::Deref>::deref"⟩,
       ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::signer::Signer<'info> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
       ⟨"anchor-lang", version, "core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::signer::Signer<'info> as core::ops::deref::Deref>::deref"⟩,
       ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
       ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::program::Program<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
       ⟨"anchor-lang", version, "core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::interface::Interface<'info, T> as \
          core::ops::deref::Deref>::deref"⟩,
       ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::interface::Interface<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
       ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
       ⟨"anchor-lang", version, "core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
          core::ops::deref::Deref>::deref"⟩,
       ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
       ⟨"anchor-lang", version, "core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
          core::ops::deref::Deref>::deref"⟩,
       ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩]),
   (.accounts_account_Account_deref_mut,
      [⟨"anchor-lang", version, "core::ops::deref::DerefMut::deref_mut",
        "<anchor_lang::accounts::account::Account<'_, T> as \
          core::ops::deref::DerefMut>::deref_mut"⟩,
       ⟨"anchor-lang", version, "core::ops::deref::DerefMut::deref_mut",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
          core::ops::deref::DerefMut>::deref_mut"⟩]),
   (.Pubkey_key,
      [⟨"anchor-lang", version, "anchor_lang::Key::key",
        "<solana_pubkey::Pubkey as anchor_lang::Key>::key"⟩]),
   (.accounts_wrapper_key,
      [⟨"anchor-lang", version, "anchor_lang::Key::key",
        "<anchor_lang::accounts::account::Account<'_, T> as anchor_lang::Key>::key"⟩,
       ⟨"anchor-lang", version, "anchor_lang::Key::key",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
          anchor_lang::Key>::key"⟩,
       ⟨"anchor-lang", version, "anchor_lang::Key::key",
        "<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Key>::key"⟩,
       ⟨"anchor-lang", version, "anchor_lang::Key::key",
        "<anchor_lang::accounts::interface::Interface<'_, T> as anchor_lang::Key>::key"⟩,
       ⟨"anchor-lang", version, "anchor_lang::Key::key",
        "<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Key>::key"⟩,
       ⟨"anchor-lang", version, "anchor_lang::Key::key",
        "<anchor_lang::accounts::system_account::SystemAccount<'_> as \
          anchor_lang::Key>::key"⟩,
       ⟨"anchor-lang", version, "anchor_lang::Key::key",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
          anchor_lang::Key>::key"⟩,
       ⟨"anchor-lang", version, "anchor_lang::Key::key",
        "<anchor_lang::accounts::sysvar::Sysvar<'_, T> as anchor_lang::Key>::key"⟩])]

/-- All three inspected references and a synthetic compatible patch retain all
all 26 mappings at the actual release. The synthetic case is selection evidence only. -/
theorem view_reference_and_compatible_identities :
    ["0.32.1", "0.32.2", "0.32.3", "0.32.4"].all (fun version =>
      (viewCases version).all (fun entry => decide
        ((catalog.forBuild { viewBuild with version := version }).identities entry.1 =
          entry.2))) = true := by
  decide +kernel

theorem view_boundaries_and_prerelease_rejected :
    ["0.32.0", "0.33.0", "0.32.4-rc.1"].all (fun version =>
      (viewCases version).all (fun entry =>
        ((catalog.forBuild { viewBuild with version := version }).identities entry.1).isEmpty)) =
      true := by
  decide +kernel

/-- Declared compatibility does not turn a same-name Git fork into the registry source. -/
theorem view_reference_and_compatible_forks_rejected :
    ["0.32.2", "0.32.4"].all (fun version =>
      (viewCases version).all (fun entry =>
        ((catalog.forBuild { viewBuild with version := version, source := ⟨"git", "https://example.org/anchor-fork",
            "0123456789012345678901234567890123456789"⟩ }).identities entry.1).isEmpty)) =
      true := by
  decide +kernel

/-- The complete mutable family retains both debug branches. This does not
extend the separate callable Entry, whose index remains debug = false. -/
theorem mutable_debug_choice_keeps_source_identity :
    ["0.32.2", "0.32.4"].all (fun version =>
      [none, some [], some ["anchor-debug"]].all (fun features => decide
        ((catalog.forBuild { viewBuild with version := version, features := features }).identities
          .accounts_account_Account_deref_mut =
          [⟨"anchor-lang", version, "core::ops::deref::DerefMut::deref_mut",
            "<anchor_lang::accounts::account::Account<'_, T> as \
              core::ops::deref::DerefMut>::deref_mut"⟩,
           ⟨"anchor-lang", version, "core::ops::deref::DerefMut::deref_mut",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
              core::ops::deref::DerefMut>::deref_mut"⟩]))) =
      true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.Views

namespace SolanalibTest.Specs.AnchorLang.Views.BorrowedCloneProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.AnchorLang.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.accounts_clone_borrowed_info,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry },
      [("core::clone::Clone::clone",
        "<anchor_lang::accounts::program::Program<'info, T> as core::clone::Clone>::clone"),
        ("core::clone::Clone::clone",
          "<anchor_lang::accounts::interface::Interface<'info, T> as \
            core::clone::Clone>::clone"),
        ("core::clone::Clone::clone",
          "<anchor_lang::accounts::signer::Signer<'info> as core::clone::Clone>::clone"),
        ("core::clone::Clone::clone",
          "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
            core::clone::Clone>::clone"),
        ("core::clone::Clone::clone",
          "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
            core::clone::Clone>::clone")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"anchor-lang", build.version, item, implementation⟩))

def members : List Key := [.accounts_clone_borrowed_info]

theorem every_member_has_a_literal_case :
    members.length = 1 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3"].all (fun version => fixtures.all (fun (key, build,
      expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["0.32.4", "0.32.99+fixture"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["0.27.0", "0.31.99", "0.33.0", "1.0.2", "0.32.4-rc.1"].all (fun version => fixtures.all (fun
      (key, build, _) =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- An interval must not conceal a missing reference or a changed item range. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      !(Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).isEmpty &&
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).all (fun profile =>
        decide (profile.releases = ["0.32.0", "0.32.1", "0.32.2", "0.32.3"] ∧
          profile.compatibleRanges = [⟨"0.32.0", "0.33.0"⟩]))) = true := by
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

end SolanalibTest.Specs.AnchorLang.Views.BorrowedCloneProfiles

namespace SolanalibTest.Specs.AnchorLang.Views.AddedAliases

open Solanalib.Contracts.Model Solanalib.Specs.Core

def build (version : String) : Versioning.Build :=
  {
    package := "anchor-lang", version := version,
    source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩ }

/-- The four shared members retain all old aliases and append only the newly
reviewed receiver implementations, with no broader inherited minor bound. -/
def aliases : List (Solanalib.Specs.AnchorLang.Capabilities.Key × List (String × String)) :=
  [(.accounts_account_Account_clone_borrowed_info, [("core::clone::Clone::clone",
    "<anchor_lang::accounts::account::Account<'info, T> as core::clone::Clone>::clone"),
      ("core::clone::Clone::clone",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          core::clone::Clone>::clone")]),
    (.accounts_borrowed_info_ref, [("core::convert::AsRef::as_ref",
      "<anchor_lang::accounts::account::Account<'info, T> as \
        core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
      ("core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::program::Program<'info, T> as \
          core::ops::deref::Deref>::deref"),
      ("core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::signer::Signer<'info> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
      ("core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::signer::Signer<'info> as core::ops::deref::Deref>::deref"),
      ("core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
      ("core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::program::Program<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
      ("core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::interface::Interface<'info, T> as \
          core::ops::deref::Deref>::deref"),
      ("core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::interface::Interface<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
      ("core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
      ("core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
          core::ops::deref::Deref>::deref"),
      ("core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
      ("core::ops::deref::Deref::deref",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
          core::ops::deref::Deref>::deref"),
      ("core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref")]),
    (.accounts_account_Account_deref_mut, [("core::ops::deref::DerefMut::deref_mut",
      "<anchor_lang::accounts::account::Account<'_, T> as \
        core::ops::deref::DerefMut>::deref_mut"),
      ("core::ops::deref::DerefMut::deref_mut",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
          core::ops::deref::DerefMut>::deref_mut")]),
    (.accounts_wrapper_key, [("anchor_lang::Key::key",
      "<anchor_lang::accounts::account::Account<'_, T> as anchor_lang::Key>::key"),
      ("anchor_lang::Key::key",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
          anchor_lang::Key>::key"),
      ("anchor_lang::Key::key",
        "<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Key>::key"),
      ("anchor_lang::Key::key",
        "<anchor_lang::accounts::interface::Interface<'_, T> as anchor_lang::Key>::key"),
      ("anchor_lang::Key::key",
        "<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Key>::key"),
      ("anchor_lang::Key::key",
        "<anchor_lang::accounts::system_account::SystemAccount<'_> as \
          anchor_lang::Key>::key"),
      ("anchor_lang::Key::key",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
          anchor_lang::Key>::key"),
      ("anchor_lang::Key::key",
        "<anchor_lang::accounts::sysvar::Sysvar<'_, T> as anchor_lang::Key>::key")])]

theorem old_and_new_aliases_keep_actual_identities :
    ["0.32.1", "0.32.2", "0.32.3", "0.32.4", "0.32.99+fixture"].all (fun version =>
      aliases.all (fun (key, expected) => decide
        ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild (build version)).identities key =
          expected.map (fun (item, implementation) =>
            ⟨"anchor-lang", version, item, implementation⟩)))) = true := by
  decide +kernel

/-- The original receiver profiles remain separate from later minor-line additions. -/
def inheritedCatalog :=
  { Solanalib.Specs.AnchorLang.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).filter (fun profile =>
        ["anchor-views-0.32.1:0", "anchor-views-0.32.1:1", "anchor-views-0.32.1:2",
          "anchor-views-0.32.1:3", "anchor-views-0.32.1:4", "anchor-views-0.32.1:5",
          "anchor-views-0.32.1:6", "anchor-views-0.32.1:7", "anchor-views-0.32.1:8",
          "anchor-views-0.32.1:9", "anchor-views-0.32.1:10", "anchor-views-0.32.1:11",
          "anchor-views-0.32.1:12"].contains profile.id) }

/-- Every original alias has a retained profile; the bounds test cannot pass by absence. -/
theorem inherited_profiles_keep_exact_alias_counts :
    aliases.all (fun (key, expected) =>
      !(inheritedCatalog.applicability key).isEmpty &&
      decide ((inheritedCatalog.applicability key).length = expected.length)) = true := by
  decide +kernel

theorem adding_aliases_does_not_widen_the_inherited_lower_bound :
    ["0.27.0", "0.32.0", "0.33.0", "1.0.2", "0.32.4-rc.1"].all (fun version =>
      aliases.all (fun (key, _) =>
        ((inheritedCatalog.forBuild (build version)).identities key).isEmpty)) = true := by
  decide +kernel

/-- The legacy profiles preserve mutable payload and key identities while
leaving the two borrowed-info families unavailable. -/
theorem legacy_aliases_keep_full_catalog_selection :
    aliases.length = 4 ∧
    ([.accounts_account_Account_clone_borrowed_info, .accounts_borrowed_info_ref] :
      List Solanalib.Specs.AnchorLang.Capabilities.Key).all (fun key =>
        ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild (build "0.27.0")).identities
          key).isEmpty) =
      true ∧
    (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild (build "0.27.0")).identities
      .accounts_account_Account_deref_mut =
      [⟨"anchor-lang", "0.27.0", "core::ops::deref::DerefMut::deref_mut",
        "<anchor_lang::accounts::account::Account<'a, T> as \
          core::ops::deref::DerefMut>::deref_mut"⟩] ∧
    (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild (build "0.27.0")).identities
      .accounts_wrapper_key =
      [⟨"anchor-lang", "0.27.0", "anchor_lang::Key::key",
        "<anchor_lang::accounts::account::Account<'info, T> as anchor_lang::Key>::key"⟩,
       ⟨"anchor-lang", "0.27.0", "anchor_lang::Key::key",
        "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
          anchor_lang::Key>::key"⟩,
       ⟨"anchor-lang", "0.27.0", "anchor_lang::Key::key",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
          anchor_lang::Key>::key"⟩] := by
  decide +kernel

/-- The new 1.0 profiles cover shared views and keys, not borrowed cloning or
mutable decoded-payload projection. -/
theorem unextended_aliases_reject_1_0_2_in_full_catalog :
    ([.accounts_account_Account_clone_borrowed_info, .accounts_account_Account_deref_mut] :
      List Solanalib.Specs.AnchorLang.Capabilities.Key).all (fun key =>
        ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild (build "1.0.2")).identities
          key).isEmpty) =
      true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.Views.AddedAliases

namespace SolanalibTest.Specs.AnchorLang.Views.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def Lamports_get_lamportsBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.32.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def Lamports_get_lamportsCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.32.0; eligible
  (Lamports_get_lamportsBuild, true),
  -- inspected-reference-0.32.1; eligible
  ({ Lamports_get_lamportsBuild with version := "0.32.1" }, true),
  -- inspected-reference-0.32.2; eligible
  ({ Lamports_get_lamportsBuild with version := "0.32.2" }, true),
  -- inspected-reference-0.32.3; eligible
  ({ Lamports_get_lamportsBuild with version := "0.32.3" }, true),
  -- lower; eligible
  (Lamports_get_lamportsBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ Lamports_get_lamportsBuild with version := "0.32.97" }, true),
  -- exclusive-upper; unsupported
  ({ Lamports_get_lamportsBuild with version := "0.33.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ Lamports_get_lamportsBuild with version := "0.32.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ Lamports_get_lamportsBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ Lamports_get_lamportsBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.31.999; unsupported
  ({ Lamports_get_lamportsBuild with version := "0.31.999" }, false)
]

set_option maxRecDepth 8192 in
theorem Lamports_get_lamports_profile_controls :
    Lamports_get_lamportsCases.all (fun test =>
      (((Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability .Lamports_get_lamports).any
        (fun profile => ["anchor-views-0.32.1"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem Lamports_get_lamports_callable_identities :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "0.32.97"].all (fun version =>
      (((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        { Lamports_get_lamportsBuild with version := version }).identities
          .Lamports_get_lamports).eraseDups ==
        [⟨"anchor-lang", version, "anchor_lang::Lamports::get_lamports",
          "anchor_lang::Lamports::get_lamports"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.Views.Pr575Compatibility

@[expose] public section

namespace SolanalibTest.Specs.AnchorLang.V1_0_2Views

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.AnchorLang.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id || (id ++ ":").toList.isPrefixOf profile.id.toList) }

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
      decide (((selectedProfile "anchor-views-1.0.2").forBuild
        { build0 with version := version }).identities .Pubkey_key =
          [⟨"anchor-lang", version, "anchor_lang::Key::key",
            "<solana_address::Address as anchor_lang::Key>::key"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::Key::key",
            "<solana_address::Address as anchor_lang::Key>::key"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build0).identities .Pubkey_key)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "anchor-views-1.0.2").applicability .Pubkey_key).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-views-1.0.2").forBuild { build0 with version := version
        }).identities
        .Pubkey_key).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "anchor-lang-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities
        .Pubkey_key).isEmpty) = true := by
  decide +kernel

def build1 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile1_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-views-1.0.2").forBuild
        { build1 with version := version }).identities .accounts_borrowed_info_ref =
          [⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::account::Account<'info, T> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::program::Program<'info, T> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", version, "core::ops::deref::Deref::deref",
            "<anchor_lang::accounts::program::Program<'info, T> as \
              core::ops::deref::Deref>::deref"⟩,
          ⟨"anchor-lang", version, "core::ops::deref::Deref::deref",
            "<anchor_lang::accounts::interface::Interface<'info, T> as \
              core::ops::deref::Deref>::deref"⟩,
          ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::interface::Interface<'info, T> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::signer::Signer<'info> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", version, "core::ops::deref::Deref::deref",
            "<anchor_lang::accounts::signer::Signer<'info> as \
              core::ops::deref::Deref>::deref"⟩,
          ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", version, "core::ops::deref::Deref::deref",
            "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
              core::ops::deref::Deref>::deref"⟩,
          ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", version, "core::ops::deref::Deref::deref",
            "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
              core::ops::deref::Deref>::deref"⟩,
          ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩])) = true :=
                by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile1_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::account::Account<'info, T> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::program::Program<'info, T> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::ops::deref::Deref::deref",
            "<anchor_lang::accounts::program::Program<'info, T> as \
              core::ops::deref::Deref>::deref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::ops::deref::Deref::deref",
            "<anchor_lang::accounts::interface::Interface<'info, T> as \
              core::ops::deref::Deref>::deref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::interface::Interface<'info, T> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::signer::Signer<'info> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::ops::deref::Deref::deref",
            "<anchor_lang::accounts::signer::Signer<'info> as \
              core::ops::deref::Deref>::deref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::ops::deref::Deref::deref",
            "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
              core::ops::deref::Deref>::deref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::ops::deref::Deref::deref",
            "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
              core::ops::deref::Deref>::deref"⟩,
          ⟨"anchor-lang", "1.0.2", "core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as \
              core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"⟩] : List
                Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build1).identities .accounts_borrowed_info_ref)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile1_range_rejections :
    ((selectedProfile "anchor-views-1.0.2").applicability .accounts_borrowed_info_ref).length = 13 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-views-1.0.2").forBuild { build1 with version := version
        }).identities
        .accounts_borrowed_info_ref).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile1_build_rejections :
    ([{ build1 with package := "anchor-lang-other" },
      { build1 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build1 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_borrowed_info_ref).isEmpty) = true := by
  decide +kernel

def build2 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile2_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-views-1.0.2").forBuild
        { build2 with version := version }).identities .accounts_wrapper_key =
          [⟨"anchor-lang", version, "anchor_lang::Key::key",
            "<anchor_lang::accounts::account::Account<'_, T> as anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Key::key",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
              anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Key::key",
            "<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Key::key",
            "<anchor_lang::accounts::interface::Interface<'_, T> as anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Key::key",
            "<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Key::key",
            "<anchor_lang::accounts::system_account::SystemAccount<'_> as \
              anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Key::key",
            "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
              anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Key::key",
            "<anchor_lang::accounts::sysvar::Sysvar<'_, T> as anchor_lang::Key>::key"⟩])) = true :=
              by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile2_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::Key::key",
            "<anchor_lang::accounts::account::Account<'_, T> as anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Key::key",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
              anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Key::key",
            "<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Key::key",
            "<anchor_lang::accounts::interface::Interface<'_, T> as anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Key::key",
            "<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Key::key",
            "<anchor_lang::accounts::system_account::SystemAccount<'_> as \
              anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Key::key",
            "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
              anchor_lang::Key>::key"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Key::key",
            "<anchor_lang::accounts::sysvar::Sysvar<'_, T> as anchor_lang::Key>::key"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build2).identities .accounts_wrapper_key)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile2_range_rejections :
    ((selectedProfile "anchor-views-1.0.2").applicability .accounts_wrapper_key).length = 8 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-views-1.0.2").forBuild { build2 with version := version
        }).identities
        .accounts_wrapper_key).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile2_build_rejections :
    ([{ build2 with package := "anchor-lang-other" },
      { build2 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build2 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_wrapper_key).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.V1_0_2Views

namespace SolanalibTest.Specs.AnchorLang.LegacyViewCompatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorLang.Capabilities (Key catalog)

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal Rust identities are independent of generated profile selection. -/
def referenceRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.accounts_account_Account_into_inner, {
    package := "anchor-lang", version := "0.29.0", source
    := registry },
      [("anchor_lang::accounts::account::Account::<'a, T>::into_inner",
        "anchor_lang::accounts::account::Account::<'a, T>::into_inner"),
        ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::into_inner",
        "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::into_inner")]),
    (.Pubkey_key, {
      package := "anchor-lang", version := "0.29.0", source := registry },
      [("anchor_lang::Key::key", "<solana_program::pubkey::Pubkey as anchor_lang::Key>::key")]),
    (.accounts_account_Account_clone_borrowed_info, {
      package := "anchor-lang", version :=
      "0.29.0", source := registry },
      [("core::clone::Clone::clone",
        "<anchor_lang::accounts::account::Account<'info, T> as core::clone::Clone>::clone"),
        ("core::clone::Clone::clone",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          core::clone::Clone>::clone")]),
    (.accounts_account_Account_deref_mut, {
      package := "anchor-lang", version := "0.29.0", source
      := registry },
      [("core::ops::deref::DerefMut::deref_mut",
        "<anchor_lang::accounts::account::Account<'a, T> as \
          core::ops::deref::DerefMut>::deref_mut"), ("core::ops::deref::DerefMut::deref_mut",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'a, T> as \
              core::ops::deref::DerefMut>::deref_mut")]),
    (.accounts_borrowed_info_ref, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry },
      [("core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref"),
            ("core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::convert::AsRef::as_ref", "<anchor_lang::accounts::program::Prog\
              ram<'info, T> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::ops::deref::Deref::deref", "<anchor_lang::accounts::program::Pr\
              ogram<'info, T> as core::ops::deref::Deref>::deref"), ("core::ops::deref::Der\
              ef::deref", "<anchor_lang::accounts::interface::Interface<'info, T> as \
              core::ops::deref::Deref>::deref"), ("core::convert::AsRef::as_ref",
              "<anchor_lang::accounts::interface::Interface<'info, T> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::convert::AsRef::as_ref", "<anchor_lang::accounts::signer::Signe\
              r<'info> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::ops::deref::Deref::deref", "<anchor_lang::accounts::signer::Sig\
              ner<'info> as core::ops::deref::Deref>::deref"), ("core::convert::AsRef::as_r\
              ef", "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::ops::deref::Deref::deref", "<anchor_lang::accounts::system_acco\
              unt::SystemAccount<'info> as core::ops::deref::Deref>::deref"), ("core::conve\
              rt::AsRef::as_ref", "<anchor_lang::accounts::unchecked_account::UncheckedAcco\
              unt<'info> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::ops::deref::Deref::deref", "<anchor_lang::accounts::unchecked_a\
              ccount::UncheckedAccount<'info> as core::ops::deref::Deref>::deref"), (
              "core::convert::AsRef::as_ref", "<anchor_lang::accounts::sysvar::Sysvar<'info\
              , T> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef")]),
    (.accounts_wrapper_key, {
      package := "anchor-lang", version := "0.29.0", source := registry },
      [("anchor_lang::Key::key",
        "<anchor_lang::accounts::account::Account<'info, T> as anchor_lang::Key>::key"),
        ("anchor_lang::Key::key",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          anchor_lang::Key>::key"), ("anchor_lang::Key::key", "<anchor_lang::accounts::prog\
            ram::Program<'info, T> as anchor_lang::Key>::key"), ("anchor_lang::Key::key",
              "<anchor_lang::accounts::interface::Interface<'info, T> as \
                anchor_lang::Key>::key"),
              ("anchor_lang::Key::key",
              "<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Key>::key"),
              ("anchor_lang::Key::key",
              "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
                anchor_lang::Key>::key"), ("anchor_lang::Key::key", "<anchor_lang::accounts\
                ::unchecked_account::UncheckedAccount<'info> as anchor_lang::Key>::key"), (
                "anchor_lang::Key::key", "<anchor_lang::accounts::sysvar::Sysvar<'info, T> \
                as anchor_lang::Key>::key")])]

/-- These uninspected patch versions exercise compatibility assumptions only. -/
def compatibleRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.accounts_account_Account_into_inner, {
    package := "anchor-lang", version := "0.29.1", source
    := registry },
      [("anchor_lang::accounts::account::Account::<'a, T>::into_inner",
        "anchor_lang::accounts::account::Account::<'a, T>::into_inner"),
        ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::into_inner",
        "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::into_inner")]),
    (.Pubkey_key, {
      package := "anchor-lang", version := "0.29.1", source := registry },
      [("anchor_lang::Key::key", "<solana_program::pubkey::Pubkey as anchor_lang::Key>::key")]),
    (.accounts_account_Account_clone_borrowed_info, {
      package := "anchor-lang", version :=
      "0.29.1", source := registry },
      [("core::clone::Clone::clone",
        "<anchor_lang::accounts::account::Account<'info, T> as core::clone::Clone>::clone"),
        ("core::clone::Clone::clone",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          core::clone::Clone>::clone")]),
    (.accounts_account_Account_deref_mut, {
      package := "anchor-lang", version := "0.29.1", source
      := registry },
      [("core::ops::deref::DerefMut::deref_mut",
        "<anchor_lang::accounts::account::Account<'a, T> as \
          core::ops::deref::DerefMut>::deref_mut"), ("core::ops::deref::DerefMut::deref_mut",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'a, T> as \
              core::ops::deref::DerefMut>::deref_mut")]),
    (.accounts_borrowed_info_ref, {
      package := "anchor-lang", version := "0.29.1", source :=
      registry },
      [("core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref"),
            ("core::convert::AsRef::as_ref",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::convert::AsRef::as_ref", "<anchor_lang::accounts::program::Prog\
              ram<'info, T> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::ops::deref::Deref::deref", "<anchor_lang::accounts::program::Pr\
              ogram<'info, T> as core::ops::deref::Deref>::deref"), ("core::ops::deref::Der\
              ef::deref", "<anchor_lang::accounts::interface::Interface<'info, T> as \
              core::ops::deref::Deref>::deref"), ("core::convert::AsRef::as_ref",
              "<anchor_lang::accounts::interface::Interface<'info, T> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::convert::AsRef::as_ref", "<anchor_lang::accounts::signer::Signe\
              r<'info> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::ops::deref::Deref::deref", "<anchor_lang::accounts::signer::Sig\
              ner<'info> as core::ops::deref::Deref>::deref"), ("core::convert::AsRef::as_r\
              ef", "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::ops::deref::Deref::deref", "<anchor_lang::accounts::system_acco\
              unt::SystemAccount<'info> as core::ops::deref::Deref>::deref"), ("core::conve\
              rt::AsRef::as_ref", "<anchor_lang::accounts::unchecked_account::UncheckedAcco\
              unt<'info> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef"), ("core::ops::deref::Deref::deref", "<anchor_lang::accounts::unchecked_a\
              ccount::UncheckedAccount<'info> as core::ops::deref::Deref>::deref"), (
              "core::convert::AsRef::as_ref", "<anchor_lang::accounts::sysvar::Sysvar<'info\
              , T> as \
              core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_r\
              ef")]),
    (.accounts_wrapper_key, {
      package := "anchor-lang", version := "0.29.1", source := registry },
      [("anchor_lang::Key::key",
        "<anchor_lang::accounts::account::Account<'info, T> as anchor_lang::Key>::key"),
        ("anchor_lang::Key::key",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          anchor_lang::Key>::key"), ("anchor_lang::Key::key", "<anchor_lang::accounts::prog\
            ram::Program<'info, T> as anchor_lang::Key>::key"), ("anchor_lang::Key::key",
              "<anchor_lang::accounts::interface::Interface<'info, T> as \
                anchor_lang::Key>::key"),
              ("anchor_lang::Key::key",
              "<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Key>::key"),
              ("anchor_lang::Key::key",
              "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
                anchor_lang::Key>::key"), ("anchor_lang::Key::key", "<anchor_lang::accounts\
                ::unchecked_account::UncheckedAccount<'info> as anchor_lang::Key>::key"), (
                "anchor_lang::Key::key", "<anchor_lang::accounts::sysvar::Sysvar<'info, T> \
                as anchor_lang::Key>::key")])]

theorem exact_reference_identities :
    referenceRows.length = 6 ∧ referenceRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem compatible_actual_version_identities :
    compatibleRows.length = 6 ∧ compatibleRows.all (fun row => decide
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
  [(.accounts_account_Account_into_inner, {
    package := "anchor-lang", version := "0.29.0", source
    := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.Pubkey_key, {
      package := "anchor-lang", version := "0.29.0", source := registry },
      ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_account_Account_clone_borrowed_info, {
      package := "anchor-lang", version :=
      "0.29.0", source := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_account_Account_deref_mut, {
      package := "anchor-lang", version := "0.29.0", source
      := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_borrowed_info_ref, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_wrapper_key, {
      package := "anchor-lang", version := "0.29.0", source := registry },
      ["0.28.999", "0.30.0", "0.29.0-rc.1"])]

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

end SolanalibTest.Specs.AnchorLang.LegacyViewCompatibility

/- Per-operation compatibility selection. Synthetic versions carry no native or ABI credit. -/
namespace SolanalibTest.Specs.AnchorLang.Views.LegacyCompatibility

@[expose] public section

set_option autoImplicit false

namespace OwnedFields

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
    (.accounts_account_Account_set_inner, [⟨"anchor-lang", version,
      "anchor_lang::accounts::account::Account::<'a, T>::set_inner",
      "anchor_lang::accounts::account::Account::<'a, T>::set_inner"⟩]),
    (.accounts_owned_info_ref, [⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
      "<anchor_lang::accounts::account::Account<'info, T> as \
        core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref"⟩,
          ⟨"anchor-lang", version, "core::ops::deref::Deref::deref",
          "<anchor_lang::accounts::program::Program<'info, T> as \
            core::ops::deref::Deref>::deref"⟩,
          ⟨"anchor-lang", version, "core::convert::AsRef::as_ref",
          "<anchor_lang::accounts::signer::Signer<'info> as \
            core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref"⟩, ⟨
            "anchor-lang", version, "core::ops::deref::Deref::deref", "<anchor_lang::accoun\
            ts::signer::Signer<'info> as core::ops::deref::Deref>::deref"⟩, ⟨"anchor-lang",
              version,
            "core::ops::deref::Deref::deref", "<anchor_lang::accounts::system_account::Syst\
            emAccount<'info> as core::ops::deref::Deref>::deref"⟩, ⟨"anchor-lang", version,
            "core::convert::AsRef::as_ref", "<anchor_lang::accounts::unchecked_account::Unc\
            heckedAccount<'info> as \
            core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref"⟩, ⟨
            "anchor-lang", version, "core::ops::deref::Deref::deref", "<anchor_lang::accoun\
            ts::unchecked_account::UncheckedAccount<'info> as \
            core::ops::deref::Deref>::deref"⟩]),
    (.accounts_sysvar_Sysvar_deref, [⟨"anchor-lang", version, "core::ops::deref::Deref::der\
      ef",
      "<anchor_lang::accounts::sysvar::Sysvar<'a, T> as core::ops::deref::Deref>::deref"⟩]),
    (.Pubkey_key, [⟨"anchor-lang", version, "anchor_lang::Key::key",
      "<solana_program::pubkey::Pubkey as anchor_lang::Key>::key"⟩]),
    (.accounts_account_Account_deref_mut, [⟨"anchor-lang", version,
      "core::ops::deref::DerefMut::deref_mut",
      "<anchor_lang::accounts::account::Account<'a, T> as \
        core::ops::deref::DerefMut>::deref_mut"⟩]),
    (.accounts_wrapper_key, [⟨"anchor-lang", version, "anchor_lang::Key::key",
      "<anchor_lang::accounts::account::Account<'info, T> as anchor_lang::Key>::key"⟩,
      ⟨"anchor-lang", version, "anchor_lang::Key::key",
      "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
        anchor_lang::Key>::key"⟩,
      ⟨"anchor-lang", version, "anchor_lang::Key::key",
      "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
        anchor_lang::Key>::key"⟩])
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

end OwnedFields

end

end SolanalibTest.Specs.AnchorLang.Views.LegacyCompatibility
