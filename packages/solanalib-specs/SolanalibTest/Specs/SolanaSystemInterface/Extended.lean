/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaSystemInterface.Extended
public import Solanalib.Specs.SolanaSystemInterface.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaSystemInterface.Extended

open Solanalib.Contracts.Model Solanalib.Specs.Core InstructionSystemExtended
open InstructionSystemExtended.Sample

theorem explicit_zero_payer_keeps_duplicate_signer :
    prefundSource.metas =
      [Instruction.accountMeta .zero true true, Instruction.accountMeta .zero true true] ∧
    prefundSource.data.lamports = 0 ∧ prefundSource.value.data.take 4 = [13, 0, 0, 0] :=
  ⟨rfl, rfl, by decide⟩

theorem absent_payer_has_one_account :
    ({ prefundSource with payer := none } : PrefundSource).metas =
      [Instruction.accountMeta .zero true true] ∧
    ({ prefundSource with payer := none } : PrefundSource).lamports = 0 := ⟨rfl, rfl⟩

theorem returned_prefund_observes_exact_value :
    InstructionBuilder.observe (types.builder PrefundData) prefundArgs.providers prefundAfter
      ⟨.zero, (0 : Nat), (0 : Nat)⟩ = some prefundSource.value := rfl

def pushFailure : PrefundArgs types :=
  { prefundArgs with providers := { prefundArgs.providers with
    metaVec := { prefundArgs.providers.metaVec with
      push := Callback.ofFunction fun (state : InstructionBuilder.Sample.State) _ =>
        .unwound (41 : Nat) { state with events := state.events ++ [12] } }
    serialize := fun _ _ _ => False } }

def pushFailureState : InstructionBuilder.Sample.State :=
  { prefundAllocated with events := [10, 12] }

def pushFailureAfter : InstructionBuilder.Sample.State :=
  InstructionBuilder.Sample.retireMetas pushFailureState 0

theorem payer_push_unwind_cleans_before_serializer :
    prefundRun types {} pushFailure (.unwound (41 : Nat) pushFailureAfter) ∧
    pushFailureAfter.events = [10, 12, 40] ∧ pushFailureAfter.metas = [none] := by
  refine ⟨?_, rfl, rfl⟩
  refine ⟨.returned (0 : Nat) prefundAllocated, rfl, ?_⟩
  refine ⟨.unwound (41 : Nat) pushFailureAfter, ?_, rfl⟩
  exact ⟨.unwound (41 : Nat) pushFailureState, rfl,
    .returned () pushFailureAfter, rfl, rfl⟩

def allocationTerminal : PrefundArgs types :=
  { prefundArgs with providers := { prefundArgs.providers with
    metaVec := { prefundArgs.providers.metaVec with
      fromList := Callback.ofFunction fun _ _ => .terminated (19 : Nat)
      push := fun _ _ _ => False
      drop := fun _ _ _ => False }
    serialize := fun _ _ _ => False } }

theorem allocation_terminal_has_no_later_operation :
    prefundRun types {} allocationTerminal (.terminated (19 : Nat)) :=
  ⟨.terminated (19 : Nat), rfl, rfl⟩

end SolanalibTest.Specs.SolanaSystemInterface.Extended

namespace SolanalibTest.Specs.SolanaSystemInterface.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SolanaSystemInterface.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SolanaSystemInterface.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

abbrev Row := Solanalib.Specs.SolanaSystemInterface.Capabilities.Key × String × String × String

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
  package := "solana-system-interface"
  version := "3.2.0"
  source := registry
  features := some ["bincode"]
  dependencies := [
    ⟨"solana-instruction", "3.4.0", registry⟩,
    ⟨"bincode", "1.3.3", registry⟩]

def rows0 : List Row := [
    (.instruction_create_account_allow_prefund, "solana-system-interface-3.2.0-bincode",
      "solana_system_interface::instruction::create_account_allow_prefund",
        "solana_system_interface::instruction::create_account_allow_prefund")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 1 ∧
    ["3.2.0", "3.2.1"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def accepted0 : List Build := [
  dependencyVersion build0 "solana-instruction" "3.4.1",
  dependencyVersion build0 "bincode" "1.3.4"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_0 :
    accepted0.length = 2 ∧
    accepted0.all (fun build => rows0.all (identifies build)) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "3.1.999" },
  { build0 with version := "4.0.0" },
  { build0 with version := "3.2.1-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build0 "solana-instruction" "4.0.0",
  dependencyVersion build0 "bincode" "2.0.0",
  { build0 with dependencies := (build0.dependencies.filter (fun dep => dep.package !=
    "solana-instruction")) },
  { build0 with dependencies := (build0.dependencies ++ [⟨"solana-instruction", "3.4.0",
    registry⟩]) },
  { build0 with dependencies := (build0.dependencies.map (fun dep =>
        if dep.package == "solana-instruction" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build0 with features := none },
  { build0 with features := some [] },
  { build0 with features := some ["bincode", "wincode"] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 13 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

def build1 : Build where
  package := "solana-system-interface"
  version := "3.2.0"
  source := registry
  features := some ["wincode"]
  dependencies := [
    ⟨"solana-instruction", "3.4.0", registry⟩,
    ⟨"wincode", "0.5.5", registry⟩]

def rows1 : List Row := [
    (.instruction_create_account_allow_prefund, "solana-system-interface-3.2.0-wincode",
      "solana_system_interface::instruction::create_account_allow_prefund",
        "solana_system_interface::instruction::create_account_allow_prefund")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_1 :
    rows1.length = 1 ∧
    ["3.2.0", "3.2.1"].all (fun version =>
      rows1.all (identifies { build1 with version := version })) = true := by
  decide +kernel

def accepted1 : List Build := [
  dependencyVersion build1 "solana-instruction" "3.4.1",
  dependencyVersion build1 "wincode" "0.5.6",
  { build1 with features := some ["bincode", "wincode"] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_1 :
    accepted1.length = 3 ∧
    accepted1.all (fun build => rows1.all (identifies build)) = true := by
  decide +kernel

def rejected1 : List Build := [
  { build1 with version := "3.1.999" },
  { build1 with version := "4.0.0" },
  { build1 with version := "3.2.1-rc.1" },
  { build1 with package := "unrelated-library" },
  { build1 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build1 "solana-instruction" "4.0.0",
  dependencyVersion build1 "wincode" "0.6.0",
  { build1 with dependencies := (build1.dependencies.filter (fun dep => dep.package !=
    "solana-instruction")) },
  { build1 with dependencies := (build1.dependencies ++ [⟨"solana-instruction", "3.4.0",
    registry⟩]) },
  { build1 with dependencies := (build1.dependencies.map (fun dep =>
        if dep.package == "solana-instruction" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build1 with features := none },
  { build1 with features := some [] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_1 :
    rejected1.length = 12 ∧
    rejected1.all (fun build => rows1.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaSystemInterface.UpdatedProfiles
