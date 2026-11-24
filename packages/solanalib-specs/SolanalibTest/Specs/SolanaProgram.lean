/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.SolanaProgram.Log
public import SolanalibTest.Specs.SolanaProgram.ReturnData

public import SolanalibTest.Specs.SolanaProgram.Cpi

public import Solanalib.Specs.SolanaProgram
public import SolanalibTest.Specs.SolanaProgram.Address
public import SolanalibTest.Specs.Core.SdkValues
public import SolanalibTest.Specs.Core.AccountInfoSdk
public import Solanalib.Specs.SolanaProgram.Capabilities
public import SolanalibTest.Specs.SolanaProgram.InstructionClone

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaProgram.LegacyValueCompatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (Key catalog)

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal Rust identities are independent of generated profile selection. -/
def referenceRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.account_info_AccountInfo_assign, {
    package := "solana-program", version := "1.18.26", source
    := registry },
      [("solana_program::account_info::AccountInfo::<'a>::assign",
        "solana_program::account_info::AccountInfo::<'a>::assign"),
        ("solana_program::account_info::AccountInfo::<'_>::assign",
        "solana_program::account_info::AccountInfo::<'_>::assign")]),
    (.account_info_AccountInfo_clone, {
      package := "solana-program", version := "1.18.26", source
      := registry },
      [("core::clone::Clone::clone",
        "<solana_program::account_info::AccountInfo<'a> as core::clone::Clone>::clone"),
        ("core::clone::Clone::clone",
        "<solana_program::account_info::AccountInfo<'_> as core::clone::Clone>::clone")]),
    (.account_info_AccountInfo_data_is_empty, {
      package := "solana-program", version := "1.\
      18.26",
      source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::data_is_empty",
        "solana_program::account_info::AccountInfo::<'a>::data_is_empty"),
        ("solana_program::account_info::AccountInfo::<'_>::data_is_empty",
        "solana_program::account_info::AccountInfo::<'_>::data_is_empty")]),
    (.account_info_AccountInfo_data_len, {
      package := "solana-program", version := "1.18.26",
      source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::data_len",
        "solana_program::account_info::AccountInfo::<'a>::data_len"),
        ("solana_program::account_info::AccountInfo::<'_>::data_len",
        "solana_program::account_info::AccountInfo::<'_>::data_len")]),
    (.account_info_AccountInfo_lamports, {
      package := "solana-program", version := "1.18.26",
      source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::lamports",
        "solana_program::account_info::AccountInfo::<'a>::lamports"),
        ("solana_program::account_info::AccountInfo::<'_>::lamports",
        "solana_program::account_info::AccountInfo::<'_>::lamports")]),
    (.account_info_AccountInfo_realloc, {
      package := "solana-program", version := "1.18.26", source
      := registry, target := [⟨"os", "solana"⟩] },
      [("solana_program::account_info::AccountInfo::<'a>::realloc",
        "solana_program::account_info::AccountInfo::<'a>::realloc"),
        ("solana_program::account_info::AccountInfo::<'_>::realloc",
        "solana_program::account_info::AccountInfo::<'_>::realloc")]),
    (.account_info_AccountInfo_try_borrow_data, {
      package := "solana-program", version :=
      "1.18.26", source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::try_borrow_data",
        "solana_program::account_info::AccountInfo::<'a>::try_borrow_data"),
        ("solana_program::account_info::AccountInfo::<'_>::try_borrow_data",
        "solana_program::account_info::AccountInfo::<'_>::try_borrow_data")]),
    (.account_info_AccountInfo_try_borrow_lamports, {
      package := "solana-program", version :=
      "1.18.26", source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::try_borrow_lamports",
        "solana_program::account_info::AccountInfo::<'a>::try_borrow_lamports"),
        ("solana_program::account_info::AccountInfo::<'_>::try_borrow_lamports",
        "solana_program::account_info::AccountInfo::<'_>::try_borrow_lamports")]),
    (.account_info_AccountInfo_try_borrow_mut_data, {
      package := "solana-program", version :=
      "1.18.26", source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::try_borrow_mut_data",
        "solana_program::account_info::AccountInfo::<'a>::try_borrow_mut_data"),
        ("solana_program::account_info::AccountInfo::<'_>::try_borrow_mut_data",
        "solana_program::account_info::AccountInfo::<'_>::try_borrow_mut_data")]),
    (.account_info_AccountInfo_try_data_len, {
      package := "solana-program", version := "1.1\
      8.26",
      source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::try_data_len",
        "solana_program::account_info::AccountInfo::<'a>::try_data_len"),
        ("solana_program::account_info::AccountInfo::<'_>::try_data_len",
        "solana_program::account_info::AccountInfo::<'_>::try_data_len")]),
    (.address_lookup_table_state_AddressLookupTable_deserialize, {
      package := "solana-progr\
      am",
      version := "1.18.26", source := registry, dependencies := [⟨"bincode", "1.3.3", registry⟩,
      ⟨"bytemuck", "1.21.0", registry⟩] },
      [("solana_program::address_lookup_table::state::AddressLookupTable::<'_>::deserialize",
        "solana_program::address_lookup_table::state::AddressLookupTable::<'_>::deserialize"),
        ("solana_program::address_lookup_table::state::AddressLookupTable::<'a>::deserializ\
          e",
        "solana_program::address_lookup_table::state::AddressLookupTable::<'a>::deserialize")]),
    (.borsh0_10_get_instance_packed_len, {
      package := "solana-program", version := "1.18.26",
      source := registry, dependencies := [⟨"borsh", "0.10.4", registry⟩] },
      [("solana_program::borsh0_10::get_instance_packed_len",
        "solana_program::borsh0_10::get_instance_packed_len")]),
    (.hash_Hash_to_bytes, {
      package := "solana-program", version := "1.18.26", source := registry },
      [("solana_program::hash::Hash::to_bytes", "solana_program::hash::Hash::to_bytes")]),
    (.hash_hash, {
      package := "solana-program", version := "1.18.26", source := registry, target :=
      [⟨"os", "solana"⟩] },
      [("solana_program::hash::hash", "solana_program::hash::hash")]),
    (.instruction_AccountMeta_clone, {
      package := "solana-program", version := "1.18.26", source :=
      registry },
      [("core::clone::Clone::clone",
        "<solana_program::instruction::AccountMeta as core::clone::Clone>::clone")]),
    (.instruction_AccountMeta_new, {
      package := "solana-program", version := "1.18.26", source :=
      registry },
      [("solana_program::instruction::AccountMeta::new",
        "solana_program::instruction::AccountMeta::new")]),
    (.instruction_AccountMeta_new_readonly, {
      package := "solana-program", version := "1.18\
      .26",
      source := registry },
      [("solana_program::instruction::AccountMeta::new_readonly",
        "solana_program::instruction::AccountMeta::new_readonly")]),
    (.program_option_COption_into_option, {
      package := "solana-program", version := "1.18.2\
      6",
      source := registry },
      [("core::convert::From::from",
        "solana_program::program_option::<impl \
          core::convert::From<solana_program::program_option::COption<T>> for \
          core::option::Option<T>>::from"), ("core::convert::From::from", "solana_program::\
            program_option::<impl \
            core::convert::From<solana_program::program_option::COption<T>> for \
            core::option::Option<T>>::from")]),
    (.rent_Rent_is_exempt, {
      package := "solana-program", version := "1.15.2", source := registry,
      target := [⟨"pointer_width", "64"⟩] },
      [("solana_program::rent::Rent::is_exempt", "solana_program::rent::Rent::is_exempt")]),
    (.rent_Rent_is_exempt, {
      package := "solana-program", version := "1.18.26", source := registry,
      target := [⟨"pointer_width", "64"⟩] },
      [("solana_program::rent::Rent::is_exempt", "solana_program::rent::Rent::is_exempt")]),
    (.rent_Rent_minimum_balance, {
      package := "solana-program", version := "1.15.2", source :=
      registry, target := [⟨"pointer_width", "64"⟩] },
      [("solana_program::rent::Rent::minimum_balance",
        "solana_program::rent::Rent::minimum_balance")]),
    (.rent_Rent_minimum_balance, {
      package := "solana-program", version := "1.18.26", source :=
      registry, target := [⟨"pointer_width", "64"⟩] },
      [("solana_program::rent::Rent::minimum_balance",
        "solana_program::rent::Rent::minimum_balance")]),
    (.sysvar_clock_Clock_get, {
      package := "solana-program", version := "1.18.26", source :=
      registry },
      [("solana_program::sysvar::Sysvar::get",
        "solana_program::sysvar::clock::<impl solana_program::sysvar::Sysvar for \
          solana_program::clock::Clock>::get")]),
    (.sysvar_rent_Rent_get, {
      package := "solana-program", version := "1.18.26", source := registry
      },
      [("solana_program::sysvar::Sysvar::get",
        "solana_program::sysvar::rent::<impl solana_program::sysvar::Sysvar for \
          solana_program::rent::Rent>::get")])]

/-- These uninspected patch versions exercise compatibility assumptions only. -/
def compatibleRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.account_info_AccountInfo_assign, {
    package := "solana-program", version := "1.18.27", source
    := registry },
      [("solana_program::account_info::AccountInfo::<'a>::assign",
        "solana_program::account_info::AccountInfo::<'a>::assign"),
        ("solana_program::account_info::AccountInfo::<'_>::assign",
        "solana_program::account_info::AccountInfo::<'_>::assign")]),
    (.account_info_AccountInfo_clone, {
      package := "solana-program", version := "1.18.27", source
      := registry },
      [("core::clone::Clone::clone",
        "<solana_program::account_info::AccountInfo<'a> as core::clone::Clone>::clone"),
        ("core::clone::Clone::clone",
        "<solana_program::account_info::AccountInfo<'_> as core::clone::Clone>::clone")]),
    (.account_info_AccountInfo_data_is_empty, {
      package := "solana-program", version := "1.\
      18.27",
      source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::data_is_empty",
        "solana_program::account_info::AccountInfo::<'a>::data_is_empty"),
        ("solana_program::account_info::AccountInfo::<'_>::data_is_empty",
        "solana_program::account_info::AccountInfo::<'_>::data_is_empty")]),
    (.account_info_AccountInfo_data_len, {
      package := "solana-program", version := "1.18.27",
      source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::data_len",
        "solana_program::account_info::AccountInfo::<'a>::data_len"),
        ("solana_program::account_info::AccountInfo::<'_>::data_len",
        "solana_program::account_info::AccountInfo::<'_>::data_len")]),
    (.account_info_AccountInfo_lamports, {
      package := "solana-program", version := "1.18.27",
      source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::lamports",
        "solana_program::account_info::AccountInfo::<'a>::lamports"),
        ("solana_program::account_info::AccountInfo::<'_>::lamports",
        "solana_program::account_info::AccountInfo::<'_>::lamports")]),
    (.account_info_AccountInfo_realloc, {
      package := "solana-program", version := "1.18.27", source
      := registry, target := [⟨"os", "solana"⟩] },
      [("solana_program::account_info::AccountInfo::<'a>::realloc",
        "solana_program::account_info::AccountInfo::<'a>::realloc"),
        ("solana_program::account_info::AccountInfo::<'_>::realloc",
        "solana_program::account_info::AccountInfo::<'_>::realloc")]),
    (.account_info_AccountInfo_try_borrow_data, {
      package := "solana-program", version :=
      "1.18.27", source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::try_borrow_data",
        "solana_program::account_info::AccountInfo::<'a>::try_borrow_data"),
        ("solana_program::account_info::AccountInfo::<'_>::try_borrow_data",
        "solana_program::account_info::AccountInfo::<'_>::try_borrow_data")]),
    (.account_info_AccountInfo_try_borrow_lamports, {
      package := "solana-program", version :=
      "1.18.27", source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::try_borrow_lamports",
        "solana_program::account_info::AccountInfo::<'a>::try_borrow_lamports"),
        ("solana_program::account_info::AccountInfo::<'_>::try_borrow_lamports",
        "solana_program::account_info::AccountInfo::<'_>::try_borrow_lamports")]),
    (.account_info_AccountInfo_try_borrow_mut_data, {
      package := "solana-program", version :=
      "1.18.27", source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::try_borrow_mut_data",
        "solana_program::account_info::AccountInfo::<'a>::try_borrow_mut_data"),
        ("solana_program::account_info::AccountInfo::<'_>::try_borrow_mut_data",
        "solana_program::account_info::AccountInfo::<'_>::try_borrow_mut_data")]),
    (.account_info_AccountInfo_try_data_len, {
      package := "solana-program", version := "1.1\
      8.27",
      source := registry },
      [("solana_program::account_info::AccountInfo::<'a>::try_data_len",
        "solana_program::account_info::AccountInfo::<'a>::try_data_len"),
        ("solana_program::account_info::AccountInfo::<'_>::try_data_len",
        "solana_program::account_info::AccountInfo::<'_>::try_data_len")]),
    (.address_lookup_table_state_AddressLookupTable_deserialize, {
      package := "solana-progr\
      am",
      version := "1.18.27", source := registry, dependencies := [⟨"bincode", "1.3.3", registry⟩,
      ⟨"bytemuck", "1.21.0", registry⟩] },
      [("solana_program::address_lookup_table::state::AddressLookupTable::<'_>::deserialize",
        "solana_program::address_lookup_table::state::AddressLookupTable::<'_>::deserialize"),
        ("solana_program::address_lookup_table::state::AddressLookupTable::<'a>::deserializ\
          e",
        "solana_program::address_lookup_table::state::AddressLookupTable::<'a>::deserialize")]),
    (.borsh0_10_get_instance_packed_len, {
      package := "solana-program", version := "1.18.27",
      source := registry, dependencies := [⟨"borsh", "0.10.4", registry⟩] },
      [("solana_program::borsh0_10::get_instance_packed_len",
        "solana_program::borsh0_10::get_instance_packed_len")]),
    (.hash_Hash_to_bytes, {
      package := "solana-program", version := "1.18.27", source := registry },
      [("solana_program::hash::Hash::to_bytes", "solana_program::hash::Hash::to_bytes")]),
    (.hash_hash, {
      package := "solana-program", version := "1.18.27", source := registry, target :=
      [⟨"os", "solana"⟩] },
      [("solana_program::hash::hash", "solana_program::hash::hash")]),
    (.instruction_AccountMeta_clone, {
      package := "solana-program", version := "1.18.27", source :=
      registry },
      [("core::clone::Clone::clone",
        "<solana_program::instruction::AccountMeta as core::clone::Clone>::clone")]),
    (.instruction_AccountMeta_new, {
      package := "solana-program", version := "1.18.27", source :=
      registry },
      [("solana_program::instruction::AccountMeta::new",
        "solana_program::instruction::AccountMeta::new")]),
    (.instruction_AccountMeta_new_readonly, {
      package := "solana-program", version := "1.18\
      .27",
      source := registry },
      [("solana_program::instruction::AccountMeta::new_readonly",
        "solana_program::instruction::AccountMeta::new_readonly")]),
    (.program_option_COption_into_option, {
      package := "solana-program", version := "1.18.2\
      7",
      source := registry },
      [("core::convert::From::from",
        "solana_program::program_option::<impl \
          core::convert::From<solana_program::program_option::COption<T>> for \
          core::option::Option<T>>::from"), ("core::convert::From::from", "solana_program::\
            program_option::<impl \
            core::convert::From<solana_program::program_option::COption<T>> for \
            core::option::Option<T>>::from")]),
    (.rent_Rent_is_exempt, {
      package := "solana-program", version := "1.15.3", source := registry,
      target := [⟨"pointer_width", "64"⟩] },
      [("solana_program::rent::Rent::is_exempt", "solana_program::rent::Rent::is_exempt")]),
    (.rent_Rent_is_exempt, {
      package := "solana-program", version := "1.18.27", source := registry,
      target := [⟨"pointer_width", "64"⟩] },
      [("solana_program::rent::Rent::is_exempt", "solana_program::rent::Rent::is_exempt")]),
    (.rent_Rent_minimum_balance, {
      package := "solana-program", version := "1.15.3", source :=
      registry, target := [⟨"pointer_width", "64"⟩] },
      [("solana_program::rent::Rent::minimum_balance",
        "solana_program::rent::Rent::minimum_balance")]),
    (.rent_Rent_minimum_balance, {
      package := "solana-program", version := "1.18.27", source :=
      registry, target := [⟨"pointer_width", "64"⟩] },
      [("solana_program::rent::Rent::minimum_balance",
        "solana_program::rent::Rent::minimum_balance")]),
    (.sysvar_clock_Clock_get, {
      package := "solana-program", version := "1.18.27", source :=
      registry },
      [("solana_program::sysvar::Sysvar::get",
        "solana_program::sysvar::clock::<impl solana_program::sysvar::Sysvar for \
          solana_program::clock::Clock>::get")]),
    (.sysvar_rent_Rent_get, {
      package := "solana-program", version := "1.18.27", source := registry
      },
      [("solana_program::sysvar::Sysvar::get",
        "solana_program::sysvar::rent::<impl solana_program::sysvar::Sysvar for \
          solana_program::rent::Rent>::get")])]

theorem exact_reference_identities :
    referenceRows.length = 24 ∧ referenceRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem compatible_actual_version_identities :
    compatibleRows.length = 24 ∧ compatibleRows.all (fun row => decide
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
  [(.account_info_AccountInfo_assign, {
    package := "solana-program", version := "1.18.26", source
    := registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.account_info_AccountInfo_clone, {
      package := "solana-program", version := "1.18.26", source
      := registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.account_info_AccountInfo_data_is_empty, {
      package := "solana-program", version := "1.\
      18.26",
      source := registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.account_info_AccountInfo_data_len, {
      package := "solana-program", version := "1.18.26",
      source := registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.account_info_AccountInfo_lamports, {
      package := "solana-program", version := "1.18.26",
      source := registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.account_info_AccountInfo_realloc, {
      package := "solana-program", version := "1.18.26", source
      := registry, target := [⟨"os", "solana"⟩] }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.account_info_AccountInfo_try_borrow_data, {
      package := "solana-program", version :=
      "1.18.26", source := registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.account_info_AccountInfo_try_borrow_lamports, {
      package := "solana-program", version :=
      "1.18.26", source := registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.account_info_AccountInfo_try_borrow_mut_data, {
      package := "solana-program", version :=
      "1.18.26", source := registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.account_info_AccountInfo_try_data_len, {
      package := "solana-program", version := "1.1\
      8.26",
      source := registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.address_lookup_table_state_AddressLookupTable_deserialize, {
      package := "solana-progr\
      am",
      version := "1.18.26", source := registry, dependencies := [⟨"bincode", "1.3.3", registry⟩,
      ⟨"bytemuck", "1.21.0", registry⟩] }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.borsh0_10_get_instance_packed_len, {
      package := "solana-program", version := "1.18.26",
      source := registry, dependencies := [⟨"borsh", "0.10.4", registry⟩] }, ["1.18.25", "2\
        .0.0",
      "1.18.26-rc.1"]),
    (.hash_Hash_to_bytes, {
      package := "solana-program", version := "1.18.26", source := registry
      }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.hash_hash, {
      package := "solana-program", version := "1.18.26", source := registry, target :=
      [⟨"os", "solana"⟩] }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.instruction_AccountMeta_clone, {
      package := "solana-program", version := "1.18.26", source :=
      registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.instruction_AccountMeta_new, {
      package := "solana-program", version := "1.18.26", source :=
      registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.instruction_AccountMeta_new_readonly, {
      package := "solana-program", version := "1.18\
      .26",
      source := registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.program_option_COption_into_option, {
      package := "solana-program", version := "1.18.2\
      6",
      source := registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.rent_Rent_is_exempt, {
      package := "solana-program", version := "1.15.2", source := registry,
      target := [⟨"pointer_width", "64"⟩] }, ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.rent_Rent_is_exempt, {
      package := "solana-program", version := "1.18.26", source := registry,
      target := [⟨"pointer_width", "64"⟩] }, ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.rent_Rent_minimum_balance, {
      package := "solana-program", version := "1.15.2", source :=
      registry, target := [⟨"pointer_width", "64"⟩] }, ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.rent_Rent_minimum_balance, {
      package := "solana-program", version := "1.18.26", source :=
      registry, target := [⟨"pointer_width", "64"⟩] }, ["1.15.1", "2.0.0", "1.15.2-rc.1"]),
    (.sysvar_clock_Clock_get, {
      package := "solana-program", version := "1.18.26", source :=
      registry }, ["1.18.25", "2.0.0", "1.18.26-rc.1"]),
    (.sysvar_rent_Rent_get, {
      package := "solana-program", version := "1.18.26", source := registry
      }, ["1.18.25", "2.0.0", "1.18.26-rc.1"])]

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
  [("bincode", "1.3.4", ["1.3.2", "2.0.0", "1.3.4-rc.1"]),
    ("borsh", "0.10.5", ["0.10.3", "0.11.0", "0.10.5-rc.1"]),
    ("bytemuck", "1.21.1", ["1.20.999", "2.0.0", "1.21.1-rc.1"])]

theorem compatible_dependencies_keep_literal_identities :
    dependencyVersions.length = 3 ∧
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

end SolanalibTest.Specs.SolanaProgram.LegacyValueCompatibility

/- Per-operation compatibility selection. Synthetic versions carry no native or ABI credit. -/
namespace SolanalibTest.Specs.SolanaProgram.LegacyCompatibility

@[expose] public section

set_option autoImplicit false

namespace AccountsAndValues

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "solana-program"
  version := "1.15.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "1.15.3" }

def identityCases (version : String) : List (Solanalib.Specs.SolanaProgram.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.account_info_AccountInfo_try_borrow_mut_lamports, [⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'a>::try_borrow_mut_lamports",
      "solana_program::account_info::AccountInfo::<'a>::try_borrow_mut_lamports"⟩,
      ⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'_>::try_borrow_mut_lamports",
      "solana_program::account_info::AccountInfo::<'_>::try_borrow_mut_lamports"⟩]),
    (.epoch_schedule_EpochSchedule_get_last_slot_in_epoch, [⟨"solana-program", version,
      "solana_program::epoch_schedule::EpochSchedule::get_last_slot_in_epoch",
      "solana_program::epoch_schedule::EpochSchedule::get_last_slot_in_epoch"⟩]),
    (.program_option_COption_contains, (if version = "1.15.2" then [⟨"solana-program", version,
      "solana_program::program_option::COption::<T>::contains",
      "solana_program::program_option::COption::<T>::contains"⟩, ⟨"solana-program", version,
      "solana_program::program_option::COption::<T>::contains",
      "solana_program::program_option::COption::<T>::contains"⟩] else [⟨"solana-program", version,
      "solana_program::program_option::COption::<T>::contains",
      "solana_program::program_option::COption::<T>::contains"⟩])),
    (.program_option_COption_is_none, (if version = "1.15.2" then [⟨"solana-program", version,
      "solana_program::program_option::COption::<T>::is_none",
      "solana_program::program_option::COption::<T>::is_none"⟩, ⟨"solana-program", version,
      "solana_program::program_option::COption::<T>::is_none",
      "solana_program::program_option::COption::<T>::is_none"⟩] else [⟨"solana-program", version,
      "solana_program::program_option::COption::<T>::is_none",
      "solana_program::program_option::COption::<T>::is_none"⟩])),
    (.program_option_COption_unwrap_or_default, (if version = "1.15.2" then [⟨"solana-progr\
      am",
      version, "solana_program::program_option::COption::<T>::unwrap_or_default",
      "solana_program::program_option::COption::<T>::unwrap_or_default"⟩, ⟨"solana-program",
      version, "solana_program::program_option::COption::<T>::unwrap_or_default",
      "solana_program::program_option::COption::<T>::unwrap_or_default"⟩] else [⟨"solana-pr\
        ogram",
      version, "solana_program::program_option::COption::<T>::unwrap_or_default",
      "solana_program::program_option::COption::<T>::unwrap_or_default"⟩])),
    (.program_pack_Pack_unpack, [⟨"solana-program", version,
      "solana_program::program_pack::Pack::unpack", "solana_program::program_pack::Pack::un\
        pack"⟩]),
    (.stake_state_Lockup_default, [⟨"solana-program", version, "core::default::Default::def\
      ault",
      "<solana_program::stake::state::Lockup as core::default::Default>::default"⟩]),
    (.stake_state_Lockup_is_in_force, [⟨"solana-program", version,
      "solana_program::stake::state::Lockup::is_in_force",
      "solana_program::stake::state::Lockup::is_in_force"⟩]),
    (.stake_state_StakeState_delegation, [⟨"solana-program", version,
      "solana_program::stake::state::StakeState::delegation",
      "solana_program::stake::state::StakeState::delegation"⟩]),
    (.stake_state_StakeState_lockup, [⟨"solana-program", version,
      "solana_program::stake::state::StakeState::lockup",
      "solana_program::stake::state::StakeState::lockup"⟩]),
    (.stake_state_StakeState_meta, [⟨"solana-program", version,
      "solana_program::stake::state::StakeState::meta",
      "solana_program::stake::state::StakeState::meta"⟩]),
    (.sysvar_rent_Rent_get_legacy_error_table, [⟨"solana-program", version,
      "solana_program::sysvar::Sysvar::get",
      "solana_program::sysvar::rent::<impl solana_program::sysvar::Sysvar for \
        solana_program::rent::Rent>::get"⟩]),
    (.account_info_AccountInfo_assign, [⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'a>::assign",
      "solana_program::account_info::AccountInfo::<'a>::assign"⟩, ⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'_>::assign",
      "solana_program::account_info::AccountInfo::<'_>::assign"⟩]),
    (.account_info_AccountInfo_clone, [⟨"solana-program", version, "core::clone::Clone::clo\
      ne",
      "<solana_program::account_info::AccountInfo<'a> as core::clone::Clone>::clone"⟩,
      ⟨"solana-program", version, "core::clone::Clone::clone",
      "<solana_program::account_info::AccountInfo<'_> as core::clone::Clone>::clone"⟩]),
    (.account_info_AccountInfo_data_len, [⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'a>::data_len",
      "solana_program::account_info::AccountInfo::<'a>::data_len"⟩, ⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'_>::data_len",
      "solana_program::account_info::AccountInfo::<'_>::data_len"⟩]),
    (.account_info_AccountInfo_lamports, [⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'a>::lamports",
      "solana_program::account_info::AccountInfo::<'a>::lamports"⟩, ⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'_>::lamports",
      "solana_program::account_info::AccountInfo::<'_>::lamports"⟩]),
    (.account_info_AccountInfo_try_borrow_data, [⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'a>::try_borrow_data",
      "solana_program::account_info::AccountInfo::<'a>::try_borrow_data"⟩, ⟨"solana-program",
      version, "solana_program::account_info::AccountInfo::<'_>::try_borrow_data",
      "solana_program::account_info::AccountInfo::<'_>::try_borrow_data"⟩]),
    (.account_info_AccountInfo_try_borrow_mut_data, [⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'a>::try_borrow_mut_data",
      "solana_program::account_info::AccountInfo::<'a>::try_borrow_mut_data"⟩, ⟨"solana-pro\
        gram",
      version, "solana_program::account_info::AccountInfo::<'_>::try_borrow_mut_data",
      "solana_program::account_info::AccountInfo::<'_>::try_borrow_mut_data"⟩]),
    (.account_info_AccountInfo_try_data_len, [⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'a>::try_data_len",
      "solana_program::account_info::AccountInfo::<'a>::try_data_len"⟩, ⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'_>::try_data_len",
      "solana_program::account_info::AccountInfo::<'_>::try_data_len"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["1.15.1", "1.16.0", "1.15.3-rc.1"].all (fun version =>
      (identityCases version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with version := version }).identities
          entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_origin_rejected :
    (identityCases compatibleBuild.version).all (fun entry =>
      ((catalog.forBuild { compatibleBuild with source :=
        ⟨"git", "https://example.org/source-fork", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
          a"⟩ }).identities entry.1).isEmpty) = true := by decide +kernel

/-- Generic range admission does not widen the fixed nominal ProgramOptionEntry profile. -/
theorem concrete_key_profile_remains_exact :
    ([.program_option_COption_contains, .program_option_COption_is_none,
      .program_option_COption_unwrap_or_default] : List
      Solanalib.Specs.SolanaProgram.Capabilities.Key).all (fun key =>
      let concrete := (catalog.applicability key).filter (fun profile => profile.id ==
        "reviewed-key")
      !concrete.isEmpty && concrete.all (fun profile =>
        profile.compatibleRanges.isEmpty && profile.matches referenceBuild &&
        !profile.matches compatibleBuild)) = true := by decide +kernel

end AccountsAndValues

namespace StakeInstructions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "solana-program"
  version := "1.15.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  dependencies := [⟨"bincode", "1.3.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "1.15.3" }

def identityCases (version : String) : List (Solanalib.Specs.SolanaProgram.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.stake_instruction_authorize, [⟨"solana-program", version,
      "solana_program::stake::instruction::authorize",
      "solana_program::stake::instruction::authorize"⟩]),
    (.stake_instruction_delegate_stake, [⟨"solana-program", version,
      "solana_program::stake::instruction::delegate_stake",
      "solana_program::stake::instruction::delegate_stake"⟩]),
    (.stake_instruction_initialize, [⟨"solana-program", version,
      "solana_program::stake::instruction::initialize",
      "solana_program::stake::instruction::initialize"⟩]),
    (.stake_instruction_merge, [⟨"solana-program", version,
      "solana_program::stake::instruction::merge", "solana_program::stake::instruction::mer\
        ge"⟩]),
    (.stake_instruction_set_lockup, [⟨"solana-program", version,
      "solana_program::stake::instruction::set_lockup",
      "solana_program::stake::instruction::set_lockup"⟩]),
    (.stake_instruction_split, [⟨"solana-program", version,
      "solana_program::stake::instruction::split", "solana_program::stake::instruction::spl\
        it"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["1.15.1", "1.16.0", "1.15.3-rc.1"].all (fun version =>
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
    ([("bincode", "1.3.4")] : List (String × String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1).isEmpty)) = true := by decide +kernel

end StakeInstructions

namespace AccountRealloc

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "solana-program"
  version := "1.15.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "1.15.3" }

def identityCases (version : String) : List (Solanalib.Specs.SolanaProgram.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.account_info_AccountInfo_realloc, [⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'a>::realloc",
      "solana_program::account_info::AccountInfo::<'a>::realloc"⟩, ⟨"solana-program", version,
      "solana_program::account_info::AccountInfo::<'_>::realloc",
      "solana_program::account_info::AccountInfo::<'_>::realloc"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["1.15.1", "1.16.0", "1.15.3-rc.1"].all (fun version =>
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
    ([⟨"os", "linux"⟩] : List Versioning.TargetFact).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with target := compatibleBuild.target.map (fun fact =>
          if fact.field = change.field then change else fact) }).identities entry.1).isEmpty)) =
            true := by decide +kernel

end AccountRealloc

namespace DynamicSyscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgram.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "solana-program"
  version := "1.15.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩]
  targetFeatures := some []

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "1.15.3" }

def identityCases (version : String) : List (Solanalib.Specs.SolanaProgram.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.syscalls_definitions_sol_create_program_address, [⟨"solana-program", version,
      "solana_program::syscalls::definitions::sol_create_program_address",
      "solana_program::syscalls::definitions::sol_create_program_address"⟩]),
    (.syscalls_definitions_sol_get_rent_sysvar, [⟨"solana-program", version,
      "solana_program::syscalls::definitions::sol_get_rent_sysvar",
      "solana_program::syscalls::definitions::sol_get_rent_sysvar"⟩]),
    (.syscalls_definitions_sol_memcpy_, [⟨"solana-program", version,
      "solana_program::syscalls::definitions::sol_memcpy_",
      "solana_program::syscalls::definitions::sol_memcpy_"⟩]),
    (.syscalls_definitions_sol_memset_, [⟨"solana-program", version,
      "solana_program::syscalls::definitions::sol_memset_",
      "solana_program::syscalls::definitions::sol_memset_"⟩]),
    (.syscalls_definitions_sol_sha256, [⟨"solana-program", version,
      "solana_program::syscalls::definitions::sol_sha256",
      "solana_program::syscalls::definitions::sol_sha256"⟩]),
    (.syscalls_definitions_sol_try_find_program_address, [⟨"solana-program", version,
      "solana_program::syscalls::definitions::sol_try_find_program_address",
      "solana_program::syscalls::definitions::sol_try_find_program_address"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["1.15.1", "1.16.0", "1.15.3-rc.1"].all (fun version =>
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
    ([⟨"pointer_width", "32"⟩, ⟨"os", "linux"⟩] : List Versioning.TargetFact).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with target := compatibleBuild.target.map (fun fact =>
          if fact.field = change.field then change else fact) }).identities entry.1).isEmpty)) =
            true := by decide +kernel

theorem target_features_unknown_or_wrong_rejected :
    [none, some ["static-syscalls"]].all (fun value =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with targetFeatures := value }).identities
          entry.1).isEmpty)) = true := by decide +kernel

end DynamicSyscalls

end

end SolanalibTest.Specs.SolanaProgram.LegacyCompatibility
