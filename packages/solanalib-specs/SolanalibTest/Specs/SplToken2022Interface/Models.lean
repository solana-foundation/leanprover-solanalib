/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplToken2022Interface
public import SolanalibTest.Specs.Core.TokenExtensionLegacy
public import Solanalib.Specs.SplToken2022Interface.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false
set_option maxRecDepth 10000

namespace SolanalibTest.Specs.SplToken2022Interface.Models

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Specs.Core.TokenExtensionLegacy
open Solanalib.Specs.SplToken2022Interface.extension

theorem unpack_owned_base_marker_only_2_1_0 :
    StateWithExtensions.unpack_owned_base_run Legacy.mintUnpacker [] atMarker
      (.returned (.ok ⟨Legacy.mintSampleBase, .borrowed ⟨atMarker, 166, 0⟩⟩) [none]) :=
  marker_only_accepted

end SolanalibTest.Specs.SplToken2022Interface.Models

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

namespace SolanalibTest.Specs.SplToken2022Interface.Models

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Specs.Core.TokenExtensionLegacy

/-- The same complete family serves the reviewed 3.0.1 profile, retaining the
exact borrowed tail after the padding allocation is retired. -/
theorem unpack_owned_base_marker_only_3_0_1 :
    Solanalib.Specs.SplToken2022Interface.extension.StateWithExtensions.unpack_owned_base_run
      Legacy.mintUnpacker [] atMarker
      (.returned (.ok ⟨Legacy.mintSampleBase, .borrowed ⟨atMarker, 166, 0⟩⟩) [none]) :=
  marker_only_accepted

end SolanalibTest.Specs.SplToken2022Interface.Models

namespace SolanalibTest.Specs.SplToken2022Interface.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SplToken2022Interface.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

abbrev Row := Solanalib.Specs.SplToken2022Interface.Capabilities.Key × String × String × String

def identifies (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 =
    [⟨build.package, build.version, row.2.2.1, row.2.2.2⟩])

def rejects (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 = [])

def registry : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def build0 : Build where
  package := "spl-token-2022-interface"
  version := "3.0.1"
  source := registry
  target := [⟨"pointer_width", "64"⟩]

def rows0 : List Row := [
    (.extension_StateWithExtensions_unpack_owned_base,
      "spl-token-2022-interface-3.0.1-extension-StateWithExtensions-unpack",
      "spl_token_2022_interface::extension::StateWithExtensions::<'data, S>::unpack",
        "spl_token_2022_interface::extension::StateWithExtensions::<'data, S>::unpack")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 1 ∧
    ["3.0.1", "3.0.2"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "3.0.0" },
  { build0 with version := "3.1.0" },
  { build0 with version := "3.0.2-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  { build0 with target := (build0.target.filter (fun fact => fact.field != "pointer_width")) },
  { build0 with target := (build0.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build0 with target := (build0.target ++ [⟨"pointer_width", "32"⟩]) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 8 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

def build1 : Build where
  package := "spl-token-2022-interface"
  version := "2.1.0"
  source := registry
  target := [⟨"pointer_width", "64"⟩]

def rows1 : List Row := [
    (.extension_StateWithExtensions_unpack_owned_base,
      "spl-token-2022-interface-2.1.0-extension-StateWithExtensions-unpack",
      "spl_token_2022_interface::extension::StateWithExtensions::<'data, S>::unpack",
        "spl_token_2022_interface::extension::StateWithExtensions::<'data, S>::unpack")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_1 :
    rows1.length = 1 ∧
    ["2.1.0", "2.1.1"].all (fun version =>
      rows1.all (identifies { build1 with version := version })) = true := by
  decide +kernel

def rejected1 : List Build := [
  { build1 with version := "2.0.999" },
  { build1 with version := "3.0.0" },
  { build1 with version := "2.1.1-rc.1" },
  { build1 with package := "unrelated-library" },
  { build1 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  { build1 with target := (build1.target.filter (fun fact => fact.field != "pointer_width")) },
  { build1 with target := (build1.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build1 with target := (build1.target ++ [⟨"pointer_width", "32"⟩]) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_1 :
    rejected1.length = 8 ∧
    rejected1.all (fun build => rows1.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SplToken2022Interface.UpdatedProfiles
