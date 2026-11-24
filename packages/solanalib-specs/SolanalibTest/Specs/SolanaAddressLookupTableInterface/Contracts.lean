/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

import Solanalib.Specs.SolanaAddressLookupTableInterface.LookupTable
public import Solanalib.Specs.SolanaAddressLookupTableInterface.Capabilities
public import SolanalibTest.Specs.Core.AddressLookupTableOwned

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaAddressLookupTableInterface.Contracts

open Solanalib.Contracts.Model.Versioning
open Solanalib.Specs.SolanaAddressLookupTableInterface.Capabilities

def cratesIo : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def selectedBuild : Build where
  package := "solana-address-lookup-table-interface"
  version := "2.2.2"
  source := cratesIo
  features := some ["bincode", "bytemuck"]
  dependencies := [⟨"bincode", "1.3.3", cratesIo⟩, ⟨"bytemuck", "1.24.0", cratesIo⟩,
    ⟨"solana-pubkey", "2.4.0", cratesIo⟩]

theorem compatible_lookup_identities :
    ["2.2.2", "2.2.3", "2.9.0"].all (fun version => decide
      ((catalog.forBuild { selectedBuild with version := version }).identities
        .state_AddressLookupTable_deserialize =
        [⟨"solana-address-lookup-table-interface", version,
          "solana_address_lookup_table_interface::state::AddressLookupTable::<'_>::deserial\
            ize",
          "solana_address_lookup_table_interface::state::AddressLookupTable::<'_>::deserial\
            ize"⟩,
         ⟨"solana-address-lookup-table-interface", version,
          "solana_address_lookup_table_interface::state::AddressLookupTable::<'a>::deserial\
            ize",
          "solana_address_lookup_table_interface::state::AddressLookupTable::<'a>::deserial\
            ize"⟩]))
            = true := by
  decide +kernel

theorem compatible_lookup_providers_admitted :
    [("bincode", "1.3.4"), ("bytemuck", "1.25.0"), ("solana-pubkey", "2.4.1")].all
      (fun (package, version) => decide ((catalog.forBuild { selectedBuild with
        version := "2.2.3"
        dependencies := selectedBuild.dependencies.map fun dependency =>
          if dependency.package = package then { dependency with version := version } else
            dependency
        }).identities .state_AddressLookupTable_deserialize ≠ [])) = true := by decide +kernel

theorem outside_lookup_range_rejected :
    ["2.2.1", "3.0.0", "2.2.3-rc.1"].all (fun version => decide
      ((catalog.forBuild { selectedBuild with version := version }).identities
        .state_AddressLookupTable_deserialize = [])) = true := by decide +kernel

theorem lookup_features_remain_required :
    [none, some ["bincode"], some ["bytemuck"]].all (fun features => decide
      ((catalog.forBuild { selectedBuild with version := "2.2.3", features := features }).identities
        .state_AddressLookupTable_deserialize = [])) = true := by decide +kernel

theorem outside_lookup_provider_ranges_rejected :
    [("bincode", "1.3.2"), ("bincode", "2.0.0"),
      ("bytemuck", "1.23.0"), ("bytemuck", "2.0.0"),
      ("solana-pubkey", "2.3.3"), ("solana-pubkey", "3.0.0")].all
      (fun (package, version) => decide ((catalog.forBuild { selectedBuild with
        version := "2.2.3"
        dependencies := selectedBuild.dependencies.map fun dependency =>
          if dependency.package = package then { dependency with version := version } else
            dependency
        }).identities .state_AddressLookupTable_deserialize = [])) = true := by decide +kernel

theorem missing_lookup_providers_rejected :
    ["bincode", "bytemuck", "solana-pubkey"].all (fun package => decide
      ((catalog.forBuild { selectedBuild with
        version := "2.2.3"
        dependencies := selectedBuild.dependencies.filter fun dependency => dependency.package !=
          package
        }).identities .state_AddressLookupTable_deserialize = [])) = true := by decide +kernel

theorem ambiguous_or_forked_lookup_provider_rejected :
    let duplicate := { selectedBuild with
      version := "2.2.3"
      dependencies := selectedBuild.dependencies ++ [⟨"solana-pubkey", "2.4.1", cratesIo⟩] }
    let forked := { selectedBuild with
      version := "2.2.3"
      dependencies := selectedBuild.dependencies.map fun dependency =>
        if dependency.package = "bytemuck" then
          { dependency with source := ⟨"git", "https://example.invalid/bytemuck", "fork"⟩ } else dependency }
    (catalog.forBuild duplicate).identities .state_AddressLookupTable_deserialize = [] ∧
    (catalog.forBuild forked).identities .state_AddressLookupTable_deserialize = [] := by
      decide +kernel

end SolanalibTest.Specs.SolanaAddressLookupTableInterface.Contracts
