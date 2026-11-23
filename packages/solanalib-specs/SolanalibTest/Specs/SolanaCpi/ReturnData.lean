/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaCpi.ReturnData
public import Solanalib.Specs.SolanaCpi.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SolanaCpi.ReturnData

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime
open Solanalib.Specs.SolanaCpi

theorem empty_clears (index : Index) (before : Solanalib.Runtime.InvState) :
    set_return_data_run index before [] (.returned .ok0 { before with ts := { before.ts with
      returnData := (before.ts.key index.context.frame.programIdx, []) } }) := rfl

end SolanalibTest.Specs.SolanaCpi.ReturnData

namespace SolanalibTest.Specs.SolanaCpi.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SolanaCpi.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SolanaCpi.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

abbrev Row := Solanalib.Specs.SolanaCpi.Capabilities.Key × String × String × String

def identifies (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 =
    [⟨build.package, build.version, row.2.2.1, row.2.2.2⟩])

def rejects (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 = [])

def registry : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def build0 : Build where
  package := "solana-cpi"
  version := "3.1.0"
  source := registry
  target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩]

def rows0 : List Row := [
    (.set_return_data, "raw-runtime-solana-cpi-3.1.0",
      "solana_cpi::set_return_data", "solana_cpi::set_return_data")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 1 ∧
    ["3.1.0", "3.1.1"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "3.0.999" },
  { build0 with version := "4.0.0" },
  { build0 with version := "3.1.1-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
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
    rejected0.length = 11 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaCpi.UpdatedProfiles
