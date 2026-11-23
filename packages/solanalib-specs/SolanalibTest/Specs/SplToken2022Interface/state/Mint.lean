/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplToken2022Interface.state.Mint
public import Solanalib.Specs.SplToken2022Interface.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SplToken2022Interface.state.Mint

open Solanalib.Specs.Core.Token
open Solanalib.Specs.SplToken2022Interface.state.Mint

/-- This catalog entry denotes precisely the concrete source Clone instance. -/
theorem registered_identity :
    Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.identities .state_Mint_clone =
      [⟨"spl-token-2022-interface", "3.1.1", "core::clone::Clone::clone",
        "<spl_token_2022_interface::state::Mint as core::clone::Clone>::clone"⟩] := rfl

/-- The model admits a source Mint independently of its initialization flag. -/
theorem uninitialized_is_admitted :
    clone_contract.requires ⟨some .zero, 2^64 - 1, 255, false, none⟩ () := trivial

/-- The reference copies both authorities and every scalar at the source
boundaries, preserving None separately from a present all-zero authority. -/
theorem copied_fields :
    cloneReference ⟨some .zero, 2^64 - 1, 255, false, none⟩ () =
      (⟨some .zero, 2^64 - 1, 255, false, none⟩,
       ⟨some .zero, 2^64 - 1, 255, false, none⟩) := rfl

/-- Clients can use the exact full-value equality from any supplied model
interpretation, without expanding or proving an SDK Clone implementation. -/
theorem complete_copy_from_contract (run : Mint → Unit → Mint × Mint)
    (implements : clone_contract.RealizedBy run) (value : Mint) :
    (run value ()).1 = value ∧ (run value ()).2 = value :=
  implements value () trivial

open Solanalib.Contracts.Model.Versioning

def registrySource : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def mintBuild : Build where
  package := "spl-token-2022-interface"
  version := "3.1.1"
  source := registrySource
  dependencies := [
    ⟨"solana-program-option", "3.1.0", registrySource⟩,
    ⟨"solana-address", "2.6.1", registrySource⟩]

/-- Source-call admission retains both concrete field providers. -/
theorem reviewed_build_admitted :
    ((Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.forBuild mintBuild).identities
      .state_Mint_clone) =
      [⟨"spl-token-2022-interface", "3.1.1", "core::clone::Clone::clone",
        "<spl_token_2022_interface::state::Mint as core::clone::Clone>::clone"⟩] := by
  decide +kernel

/-- Compatible releases keep the full Clone identity and may resolve compatible
field providers independently of the exact native-test lockfile. -/
theorem compatible_builds_admitted :
    ["3.1.2", "3.2.0"].all (fun version => decide
      ((Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.forBuild
        { mintBuild with
          version := version
          dependencies := [
            ⟨"solana-program-option", "3.1.1", registrySource⟩,
            ⟨"solana-address", "2.9.0", registrySource⟩] }).identities .state_Mint_clone =
        [⟨"spl-token-2022-interface", version, "core::clone::Clone::clone",
          "<spl_token_2022_interface::state::Mint as core::clone::Clone>::clone"⟩])) = true := by
  decide +kernel

theorem outside_clone_range_rejected :
    ["3.1.0", "4.0.0", "3.2.0-rc.1"].all (fun version => decide
      ((Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.forBuild
        { mintBuild with version := version }).identities .state_Mint_clone = [])) = true := by
  decide +kernel

theorem missing_field_providers_rejected :
    ((Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.forBuild
      { mintBuild with dependencies := [] }).identities .state_Mint_clone) = [] := by
  decide +kernel

theorem below_reference_field_provider_rejected :
    ((Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.forBuild
      { mintBuild with dependencies := [
        ⟨"solana-program-option", "3.1.0", mintBuild.source⟩,
        ⟨"solana-address", "2.6.0", mintBuild.source⟩] }).identities .state_Mint_clone) = [] := by
  decide +kernel

end SolanalibTest.Specs.SplToken2022Interface.state.Mint
