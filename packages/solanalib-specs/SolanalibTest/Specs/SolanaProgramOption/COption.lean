/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaProgramOption
public import Solanalib.Specs.SolanaProgramOption.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaProgramOption

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaProgramOption.COption

theorem arbitrary_payload {T : Type} (value : T) :
    is_some_run T () (.some value) (.returned true ()) := rfl

theorem empty_payload_type_still_admits_none :
    is_some_run Empty () .none (.returned false ()) := rfl

theorem none_cannot_report_some :
    ¬ is_some_run Empty () .none (.returned true ()) := by
  intro impossible
  cases impossible

end SolanalibTest.Specs.SolanaProgramOption

namespace SolanalibTest.Specs.SolanaProgramOption.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SolanaProgramOption.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SolanaProgramOption.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

abbrev Row := Solanalib.Specs.SolanaProgramOption.Capabilities.Key × String × String × String

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
  package := "solana-program-option"
  version := "3.1.0"
  source := registry

def rows0 : List Row := [
    (.COption_eq, "reviewed-3-1-0",
      "core::cmp::PartialEq::eq",
        "<solana_program_option::COption<T> as core::cmp::PartialEq>::eq"),
    (.COption_unwrap, "reviewed-3-1-0",
      "solana_program_option::COption::<T>::unwrap", "solana_program_option::COption::<T>::\
        unwrap")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 2 ∧
    ["3.1.0", "3.1.1"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "3.0.999" },
  { build0 with version := "4.0.0" },
  { build0 with version := "3.1.1-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 5 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

def build1 : Build where
  package := "solana-program-option"
  version := "3.1.0"
  source := registry
  dependencies := [
    ⟨"solana-address", "2.6.0", registry⟩]

def rows1 : List Row := [
    (.COption_eq, "reviewed-key",
      "core::cmp::PartialEq::eq",
        "<solana_program_option::COption<T> as core::cmp::PartialEq>::eq")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_1 :
    rows1.length = 1 ∧
    ["3.1.0", "3.1.1"].all (fun version =>
      rows1.all (identifies { build1 with version := version })) = true := by
  decide +kernel

def accepted1 : List Build := [
  dependencyVersion build1 "solana-address" "2.6.1"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_1 :
    accepted1.length = 1 ∧
    accepted1.all (fun build => rows1.all (identifies build)) = true := by
  decide +kernel

def rejected1 : List Build := [
  { build1 with version := "3.0.999" },
  { build1 with version := "4.0.0" },
  { build1 with version := "3.1.1-rc.1" },
  { build1 with package := "unrelated-library" },
  { build1 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build1 "solana-address" "2.6.2",
  { build1 with dependencies := (build1.dependencies.filter (fun dep => dep.package !=
    "solana-address")) },
  { build1 with dependencies := (build1.dependencies ++ [⟨"solana-address", "2.6.0", registry⟩]) },
  { build1 with dependencies := (build1.dependencies.map (fun dep =>
        if dep.package == "solana-address" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_1 :
    rejected1.length = 9 ∧
    rejected1.all (fun build => rows1.all (rejects build)) = true := by
  decide +kernel

def build2 : Build where
  package := "solana-program-option"
  version := "3.1.0"
  source := registry
  target := [⟨"panic", "abort"⟩]
  dependencies := [
    ⟨"solana-address", "2.6.0", registry⟩]

def rows2 : List Row := [
    (.COption_unwrap, "reviewed-key",
      "solana_program_option::COption::<T>::unwrap", "solana_program_option::COption::<T>::\
        unwrap")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_2 :
    rows2.length = 1 ∧
    ["3.1.0", "3.1.1"].all (fun version =>
      rows2.all (identifies { build2 with version := version })) = true := by
  decide +kernel

def accepted2 : List Build := [
  dependencyVersion build2 "solana-address" "2.6.1"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_2 :
    accepted2.length = 1 ∧
    accepted2.all (fun build => rows2.all (identifies build)) = true := by
  decide +kernel

def rejected2 : List Build := [
  { build2 with version := "3.0.999" },
  { build2 with version := "4.0.0" },
  { build2 with version := "3.1.1-rc.1" },
  { build2 with package := "unrelated-library" },
  { build2 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build2 "solana-address" "2.6.2",
  { build2 with dependencies := (build2.dependencies.filter (fun dep => dep.package !=
    "solana-address")) },
  { build2 with dependencies := (build2.dependencies ++ [⟨"solana-address", "2.6.0", registry⟩]) },
  { build2 with dependencies := (build2.dependencies.map (fun dep =>
        if dep.package == "solana-address" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build2 with target := (build2.target.filter (fun fact => fact.field != "panic")) },
  { build2 with target := (build2.target.map (fun fact =>
        if fact.field == "panic" then { fact with value := "unwind" } else fact)) },
  { build2 with target := (build2.target ++ [⟨"panic", "unwind"⟩]) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_2 :
    rejected2.length = 12 ∧
    rejected2.all (fun build => rows2.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaProgramOption.UpdatedProfiles
