/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplAssociatedTokenAccountInterface
public import SolanalibTest.Specs.Core.AddressOperations
public import Solanalib.Specs.SplAssociatedTokenAccountInterface.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SplAssociatedTokenAccountInterface.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SplAssociatedTokenAccountInterface.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SplAssociatedTokenAccountInterface.Capabilities.catalog.applicability
        key).filter (fun profile => profile.id == id) }

abbrev Row := Solanalib.Specs.SplAssociatedTokenAccountInterface.Capabilities.Key × String × String
  × String

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
  package := "spl-associated-token-account-interface"
  version := "2.0.0"
  source := registry
  target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩]
  dependencies := [
    ⟨"solana-pubkey", "3.0.0", registry⟩,
    ⟨"solana-address", "2.6.0", registry⟩]

def rows0 : List Row := [
    (.address_get_associated_token_address_with_program_id,
      "spl-associated-token-account-interface-2.0.0-get_associated_token_address_with_progr\
        am_id",
      "spl_associated_token_account_interface::address::get_associated_token_address_with_p\
        rogram_id", "spl_associated_token_account_interface::address::get_associated_token_\
          address_with_program_id")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 1 ∧
    ["2.0.0", "2.0.1"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def accepted0 : List Build := [
  dependencyVersion build0 "solana-pubkey" "3.0.1",
  dependencyVersion build0 "solana-address" "2.6.1"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_0 :
    accepted0.length = 2 ∧
    accepted0.all (fun build => rows0.all (identifies build)) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "1.999.999" },
  { build0 with version := "3.0.0" },
  { build0 with version := "2.0.1-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build0 "solana-pubkey" "4.0.0",
  dependencyVersion build0 "solana-address" "3.0.0",
  { build0 with dependencies := (build0.dependencies.filter (fun dep => dep.package !=
    "solana-pubkey")) },
  { build0 with dependencies := (build0.dependencies ++ [⟨"solana-pubkey", "3.0.0", registry⟩]) },
  { build0 with dependencies := (build0.dependencies.map (fun dep =>
        if dep.package == "solana-pubkey" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build0 with target := (build0.target.filter (fun fact => fact.field != "pointer_width")) },
  { build0 with target := (build0.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build0 with target := (build0.target ++ [⟨"pointer_width", "32"⟩]) },
  { build0 with target := (build0.target.filter (fun fact => fact.field != "os")) },
  { build0 with target := (build0.target.map (fun fact =>
        if fact.field == "os" then { fact with value := "linux" } else fact)) },
  { build0 with target := (build0.target ++ [⟨"os", "linux"⟩]) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 16 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SplAssociatedTokenAccountInterface.UpdatedProfiles
