/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaAddress
public import Solanalib.Specs.SolanaAddress.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaAddress

open Solanalib.Specs.Core.Address
open Solanalib.Specs.SolanaAddress.Address

def marked : Array32 := ⟨List.replicate 31 0 ++ [9], by simp⟩

/-- Constructor/getter composition follows from the contracts for arbitrary
interpretations, without unfolding the reference implementations. -/
theorem bytes_roundtrip_of_contracts
    (build : Unit → Array32 → Value × Unit)
    (read : Unit → Value → _root_.Solanalib.Runtime.Bytes × Unit)
    (buildSpec : new_from_array_contract.RealizedBy build)
    (readSpec : as_ref_contract.RealizedBy read) (array : Array32) :
    (read (build () array).2 (build () array).1).1 = array.val := by
  have built := buildSpec () array trivial
  have observed := readSpec (build () array).2 (build () array).1 trivial
  calc
    (read (build () array).2 (build () array).1).1 = (build () array).1.bytes := observed.2
    _ = (newFromArray array).bytes := congrArg _root_.Solanalib.Runtime.Pubkey.bytes built.2
    _ = array.val := rfl

theorem all_32_bytes_preserved :
    (new_from_array_model () marked).1.bytes = List.replicate 31 0 ++ [9] ∧
    (as_array_model () (newFromArray marked)).1.val = marked.val ∧
    (to_bytes_model () (newFromArray marked)).1.val = marked.val :=
  ⟨rfl, rfl, rfl⟩

theorem default_is_32_zero_bytes :
    (default_model () ()).1.bytes = List.replicate 32 0 := rfl

/-- Equality sees the final byte, rather than only a prefix or an address label. -/
theorem equality_checks_last_byte :
    (eq_model () (newFromArray marked, .zero)).1 = false ∧
    (eq_model () (newFromArray marked, newFromArray marked)).1 = true := by decide

theorem search_starts_at_255 : tryFind witnessSearch = some (.zero, 255) := by decide

/-- This test oracle admits only a hash made with bump 0. It is a deliberately
chosen mathematical oracle, not a claim about SHA-256 or curve membership. -/
def zeroOnlyCrypto : Crypto where
  primitives := {
    sha256 := fun bytes => List.replicate 31 0 ++ [bytes.headD 0]
    onCurve := fun bytes => decide (bytes.getD 31 0 ≠ 0) }

def zeroOnlySearch : SearchArgs := ⟨zeroOnlyCrypto, [], .zero⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem bump_zero_is_not_tried : tryFind zeroOnlySearch = none := by decide

theorem bump_zero_would_be_admissible :
    _root_.Solanalib.Runtime.createProgramAddressBytes zeroOnlyCrypto.primitives [[0]]
      _root_.Solanalib.Runtime.Pubkey.zero.bytes = .ok (List.replicate 32 0) := rfl

theorem failed_search_cannot_return_key (key : Value) (bump : UInt8) :
    ¬ find_program_address_contract.post () zeroOnlySearch (.returned (key, bump) ()) := by
  change ¬ tryFind zeroOnlySearch = some (key, bump)
  rw [bump_zero_is_not_tried]
  simp

theorem failed_search_can_terminate :
    find_program_address_contract.post () zeroOnlySearch
      (.terminated .noViableProgramAddress) := bump_zero_is_not_tried

theorem failed_search_can_unwind :
    find_program_address_contract.post () zeroOnlySearch
      (.unwound .noViableProgramAddress ()) := bump_zero_is_not_tried

def alwaysOnCurve : Crypto where
  primitives := { witnessCrypto.primitives with onCurve := fun _ => true }

theorem curve_result_is_supplied_by_crypto :
    (is_on_curve_model () (witnessCrypto, newFromArray marked)).1 = false ∧
    (is_on_curve_model () (alwaysOnCurve, newFromArray marked)).1 = true := ⟨rfl, rfl⟩

open Solanalib.Contracts.Model.Versioning

def comparisonBuild : Build where
  package := "solana-address"
  version := "2.6.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Reviewed and unlisted compatible releases keep the actual defining release
and the exact Ord implementation in their selected source identity. -/
theorem comparison_compatible_identities :
    ["2.6.0", "2.6.1", "2.6.2", "2.7.0", "2.8.0", "2.9.0", "2.9.1"].all
      (fun version => decide
        ((Solanalib.Specs.SolanaAddress.Capabilities.catalog.forBuild
          { comparisonBuild with version := version }).identities .Address_cmp =
          [⟨"solana-address", version, "core::cmp::Ord::cmp",
            "<solana_address::Address as core::cmp::Ord>::cmp"⟩])) = true := by
  decide +kernel

/-- Earlier releases, a new major line and prereleases remain outside this profile. -/
theorem comparison_outside_range_rejected :
    ["2.5.0", "3.0.0", "2.9.1-rc.1"].all (fun version => decide
      ((Solanalib.Specs.SolanaAddress.Capabilities.catalog.forBuild
        { comparisonBuild with version := version }).identities .Address_cmp = [])) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaAddress

namespace SolanalibTest.Specs.SolanaAddress.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SolanaAddress.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SolanaAddress.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

abbrev Row := Solanalib.Specs.SolanaAddress.Capabilities.Key × String × String × String

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
  package := "solana-address"
  version := "2.6.1"
  source := registry
  features := some ["borsh"]
  dependencies := [
    ⟨"borsh", "1.6.0", registry⟩,
    ⟨"borsh-derive", "1.6.0", registry⟩]

def rows0 : List Row := [
    (.Address_serialize, "solana-address-2.6.1-serialize",
      "borsh::ser::BorshSerialize::serialize",
        "<solana_address::Address as borsh::ser::BorshSerialize>::serialize"),
    (.Address_deserialize_reader_read_exact, "solana-address-2.6.1-deserialize_reader",
      "borsh::de::BorshDeserialize::deserialize_reader",
        "<solana_address::Address as borsh::de::BorshDeserialize>::deserialize_reader")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 2 ∧
    ["2.6.1", "2.6.2"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def accepted0 : List Build := [
  dependencyVersion build0 "borsh" "1.6.1",
  dependencyVersion build0 "borsh-derive" "1.6.1"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_0 :
    accepted0.length = 2 ∧
    accepted0.all (fun build => rows0.all (identifies build)) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "2.6.0" },
  { build0 with version := "3.0.0" },
  { build0 with version := "2.6.2-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build0 "borsh" "2.0.0",
  dependencyVersion build0 "borsh-derive" "2.0.0",
  { build0 with dependencies := (build0.dependencies.filter (fun dep => dep.package != "bor\
    sh")) },
  { build0 with dependencies := (build0.dependencies ++ [⟨"borsh", "1.6.0", registry⟩]) },
  { build0 with dependencies := (build0.dependencies.map (fun dep =>
        if dep.package == "borsh" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build0 with features := none },
  { build0 with features := some [] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 12 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

def build1 : Build where
  package := "solana-address"
  version := "2.6.0"
  source := registry
  target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩]
  features := some ["syscalls"]

def rows1 : List Row := [
    (.Address_create_program_address_solana,
      "solana-address-2.6.0-2.6.1-create_program_address_solana",
      "solana_address::syscalls::<impl solana_address::Address>::create_program_address",
        "solana_address::syscalls::<impl solana_address::Address>::create_program_address")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_1 :
    rows1.length = 1 ∧
    ["2.6.0", "2.6.1"].all (fun version =>
      rows1.all (identifies { build1 with version := version })) = true := by
  decide +kernel

def rejected1 : List Build := [
  { build1 with version := "2.5.999" },
  { build1 with version := "3.0.0" },
  { build1 with version := "2.6.1-rc.1" },
  { build1 with package := "unrelated-library" },
  { build1 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  { build1 with target := (build1.target.filter (fun fact => fact.field != "pointer_width")) },
  { build1 with target := (build1.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build1 with target := (build1.target ++ [⟨"pointer_width", "32"⟩]) },
  { build1 with target := (build1.target.filter (fun fact => fact.field != "os")) },
  { build1 with target := (build1.target.map (fun fact =>
        if fact.field == "os" then { fact with value := "linux" } else fact)) },
  { build1 with target := (build1.target ++ [⟨"os", "linux"⟩]) },
  { build1 with features := none },
  { build1 with features := some [] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_1 :
    rejected1.length = 13 ∧
    rejected1.all (fun build => rows1.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaAddress.UpdatedProfiles
