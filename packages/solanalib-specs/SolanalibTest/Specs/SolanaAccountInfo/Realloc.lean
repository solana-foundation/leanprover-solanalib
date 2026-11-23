/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaAccountInfo.Realloc
public import Solanalib.Specs.SolanaAccountInfo.Capabilities
public import SolanalibTest.Specs.Core.AccountInfoSdk

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaAccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core SolanalibTest.Specs.Core.AccountInfoSdk

theorem realloc_reuses_backing_model :
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.realloc_run shrunk regrowArgs
      (.returned (.ok ()) regrown) :=
  (AccountInfoSdk.resize_returned_iff _ _ _ _).mpr rfl

namespace SdkProfiles

open Solanalib.Contracts.Model.Versioning
open Solanalib.Contracts.Model.Capabilities (RustIdentity)
open Solanalib.Specs.SolanaAccountInfo.Capabilities (catalog)

/-- Both size-changing methods use the selected Solana memory branch. The other
three methods do not require these extra build facts. -/
def sdkBuild : Build where
  package := "solana-account-info"
  version := "2.3.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩]
  dependencies :=
    [⟨"solana-program-memory", "2.3.1",
      ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]

/-- Independent source fixtures retain both lifetime spellings. -/
def localCases (version : String) :
    List (Solanalib.Specs.SolanaAccountInfo.Capabilities.Key × List RustIdentity) :=
  [(.AccountInfo_assign,
      [⟨"solana-account-info", version, "solana_account_info::AccountInfo::<'a>::assign",
        "solana_account_info::AccountInfo::<'a>::assign"⟩,
       ⟨"solana-account-info", version, "solana_account_info::AccountInfo::<'_>::assign",
        "solana_account_info::AccountInfo::<'_>::assign"⟩]),
   (.AccountInfo_try_borrow_lamports,
      [⟨"solana-account-info", version,
        "solana_account_info::AccountInfo::<'a>::try_borrow_lamports",
        "solana_account_info::AccountInfo::<'a>::try_borrow_lamports"⟩,
       ⟨"solana-account-info", version,
         "solana_account_info::AccountInfo::<'_>::try_borrow_lamports",
        "solana_account_info::AccountInfo::<'_>::try_borrow_lamports"⟩]),
   (.AccountInfo_try_data_len,
      [⟨"solana-account-info", version, "solana_account_info::AccountInfo::<'a>::try_data_l\
        en",
        "solana_account_info::AccountInfo::<'a>::try_data_len"⟩,
       ⟨"solana-account-info", version, "solana_account_info::AccountInfo::<'_>::try_data_l\
         en",
        "solana_account_info::AccountInfo::<'_>::try_data_len"⟩])]

def sizingCases (version : String) :
    List (Solanalib.Specs.SolanaAccountInfo.Capabilities.Key × List RustIdentity) :=
  [(.AccountInfo_realloc,
      [⟨"solana-account-info", version, "solana_account_info::AccountInfo::<'a>::realloc",
        "solana_account_info::AccountInfo::<'a>::realloc"⟩,
       ⟨"solana-account-info", version, "solana_account_info::AccountInfo::<'_>::realloc",
        "solana_account_info::AccountInfo::<'_>::realloc"⟩]),
   (.AccountInfo_resize,
      [⟨"solana-account-info", version, "solana_account_info::AccountInfo::<'a>::resize",
        "solana_account_info::AccountInfo::<'a>::resize"⟩,
       ⟨"solana-account-info", version, "solana_account_info::AccountInfo::<'_>::resize",
        "solana_account_info::AccountInfo::<'_>::resize"⟩])]

/-- The five SDK profiles retain ten complete source names at the reference,
a synthetic patch and a synthetic later minor of the declared SDK line. -/
theorem sdk_actual_identities :
    ["2.3.0", "2.3.1", "2.9.0"].all (fun version =>
      (localCases version ++ sizingCases version).all (fun entry => decide
        ((catalog.forBuild { sdkBuild with version := version }).identities entry.1 = entry.2))) =
      true := by
  decide +kernel

theorem sdk_boundaries_and_prerelease_rejected :
    ["2.2.9", "3.0.0", "2.3.1-rc.1"].all (fun version =>
      (localCases version ++ sizingCases version).all (fun entry =>
        ((catalog.forBuild { sdkBuild with version := version }).identities entry.1).isEmpty)) =
      true := by
  decide +kernel

theorem sdk_reference_and_compatible_forks_rejected :
    ["2.3.0", "2.3.1"].all (fun version =>
      (localCases version ++ sizingCases version).all (fun entry =>
        ((catalog.forBuild { sdkBuild with version := version, source := ⟨"git", "https://example.org/account-info-fork",
            "0123456789012345678901234567890123456789"⟩ }).identities entry.1).isEmpty)) =
      true := by
  decide +kernel

/-- Owner assignment, lamports borrowing and checked length acquire no unrelated
memory-provider, target or feature requirement from the sizing methods. -/
theorem local_methods_need_no_memory_or_target_selection :
    ["2.3.0", "2.3.1"].all (fun version =>
      ([[], [⟨"os", "linux"⟩]] : List (List TargetFact)).all (fun target =>
        (localCases version).all (fun entry => decide
          ((catalog.forBuild { sdkBuild with version := version, target := target, dependencies :=
            [] }).identities entry.1 = entry.2)))) =
      true := by
  decide +kernel

/-- Both inspected memory references and an assumed compatible provider retain
the actual SDK version of the caller, with realloc and resize kept separate. -/
theorem sizing_memory_provider_identities :
    ["2.3.0", "2.3.1"].all (fun version =>
      ["2.2.1", "2.3.1", "2.9.0"].all (fun provider =>
        (sizingCases version).all (fun entry => decide
          ((catalog.forBuild { sdkBuild with version := version, dependencies :=
            (sdkBuild.dependencies.map
              (fun dependency => { dependency with version := provider })) }).identities entry.1 =
            entry.2)))) = true := by
  decide +kernel

/-- Unknown, host and duplicated OS facts cannot select the Solana memset branch. -/
theorem sizing_requires_unique_solana_target :
    ["2.3.0", "2.3.1"].all (fun version =>
      ([[], [⟨"os", "linux"⟩], [⟨"os", "solana"⟩, ⟨"os", "solana"⟩]] :
        List (List TargetFact)).all (fun target =>
        (sizingCases version).all (fun entry =>
          ((catalog.forBuild { sdkBuild with version := version, target := target }).identities
            entry.1).isEmpty))) = true := by
  decide +kernel

theorem sizing_memory_provider_boundaries_rejected :
    ["2.3.0", "2.3.1"].all (fun version =>
      ["2.2.0", "3.0.0", "2.9.0-rc.1"].all (fun provider =>
        (sizingCases version).all (fun entry =>
          ((catalog.forBuild { sdkBuild with version := version, dependencies :=
            (sdkBuild.dependencies.map
              (fun dependency => { dependency with version := provider })) }).identities
              entry.1).isEmpty))) = true := by
  decide +kernel

theorem sizing_memory_provider_required_unique_and_registry :
    ["2.3.0", "2.3.1"].all (fun version =>
      [[], sdkBuild.dependencies ++ sdkBuild.dependencies,
        sdkBuild.dependencies.map (fun dependency => { dependency with source :=
          ⟨"git", "https://example.org/memory-fork",
            "0123456789012345678901234567890123456789"⟩ })].all (fun dependencies =>
        (sizingCases version).all (fun entry =>
          ((catalog.forBuild { sdkBuild with version := version, dependencies := dependencies
            }).identities entry.1).isEmpty))) = true := by
  decide +kernel

end SdkProfiles

end SolanalibTest.Specs.SolanaAccountInfo
