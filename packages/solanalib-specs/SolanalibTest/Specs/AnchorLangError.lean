/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLangError
public import SolanalibTest.Specs.Core.AnchorOperations
public import Solanalib.Specs.AnchorLangError.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.AnchorLangError.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.AnchorLangError.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.AnchorLangError.Capabilities.catalog.applicability key).filter (fun profile
        => profile.id == id) }

abbrev Row := Solanalib.Specs.AnchorLangError.Capabilities.Key × String × String × String

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
  package := "anchor-lang-error"
  version := "1.1.2"
  source := registry
  dependencies := [
    ⟨"anchor-syn", "1.1.2", registry⟩]

def rows0 : List Row := [
    (.Error_from_error_code, "anchor-lang-error-1.1.2-code",
      "core::convert::From::from",
        "<anchor_lang_error::Error as \
          core::convert::From<anchor_lang_error::ErrorCode>>::from"),
    (.ErrorCode_name, "anchor-lang-error-1.1.2-code-name",
      "anchor_lang_error::ErrorCode::name", "anchor_lang_error::ErrorCode::name")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 2 ∧
    ["1.1.2", "1.1.3"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def accepted0 : List Build := [
  dependencyVersion build0 "anchor-syn" "1.1.3"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_0 :
    accepted0.length = 1 ∧
    accepted0.all (fun build => rows0.all (identifies build)) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "1.1.1" },
  { build0 with version := "1.2.0" },
  { build0 with version := "1.1.3-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build0 "anchor-syn" "2.0.0",
  { build0 with dependencies := (build0.dependencies.filter (fun dep => dep.package !=
    "anchor-syn")) },
  { build0 with dependencies := (build0.dependencies ++ [⟨"anchor-syn", "1.1.2", registry⟩]) },
  { build0 with dependencies := (build0.dependencies.map (fun dep =>
        if dep.package == "anchor-syn" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 9 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

def build1 : Build where
  package := "anchor-lang-error"
  version := "1.1.2"
  source := registry
  dependencies := [
    ⟨"solana-program-error", "3.0.1", registry⟩]

def rows1 : List Row := [
    (.Error_log, "anchor-lang-error-1.1.2-log",
      "anchor_lang_error::Error::log", "anchor_lang_error::Error::log")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_1 :
    rows1.length = 1 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows1.all (identifies { build1 with version := version })) = true := by
  decide +kernel

def accepted1 : List Build := [
  dependencyVersion build1 "solana-program-error" "3.0.2"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_1 :
    accepted1.length = 1 ∧
    accepted1.all (fun build => rows1.all (identifies build)) = true := by
  decide +kernel

def rejected1 : List Build := [
  { build1 with version := "1.1.1" },
  { build1 with version := "1.2.1" },
  { build1 with version := "1.1.3-rc.1" },
  { build1 with package := "unrelated-library" },
  { build1 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build1 "solana-program-error" "4.0.0",
  { build1 with dependencies := (build1.dependencies.filter (fun dep => dep.package !=
    "solana-program-error")) },
  { build1 with dependencies := (build1.dependencies ++ [⟨"solana-program-error", "3.0.1",
    registry⟩]) },
  { build1 with dependencies := (build1.dependencies.map (fun dep =>
        if dep.package == "solana-program-error" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_1 :
    rejected1.length = 9 ∧
    rejected1.all (fun build => rows1.all (rejects build)) = true := by
  decide +kernel

def build2 : Build where
  package := "anchor-lang-error"
  version := "1.1.2"
  source := registry

def rows2 : List Row := [
    (.Error_with_account_name, "anchor-lang-error-1.1.2-name",
      "anchor_lang_error::Error::with_account_name", "anchor_lang_error::Error::with_accoun\
        t_name")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_2 :
    rows2.length = 1 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows2.all (identifies { build2 with version := version })) = true := by
  decide +kernel

def rejected2 : List Build := [
  { build2 with version := "1.1.1" },
  { build2 with version := "1.2.1" },
  { build2 with version := "1.1.3-rc.1" },
  { build2 with package := "unrelated-library" },
  { build2 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_2 :
    rejected2.length = 5 ∧
    rejected2.all (fun build => rows2.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLangError.UpdatedProfiles

namespace SolanalibTest.Specs.AnchorLangError.Operations

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AnchorErrorOperations

set_option autoImplicit false

abbrev Heap := AnchorErrorOwned.Reference.State
abbrev StringId := AnchorErrorOwned.Reference.StringId

/-- This selected enum arm distinguishes the migration-aware table from older
tables. The expected strings, number and allocation order are literal results,
not a second implementation of the ErrorCode operation. -/
def migrationCode : Fin CodeTables.v1_1_2.size := ⟨50, by decide⟩

def nameState : Heap where
  strings := [some "AccountNotMigrated"]
  boxes := []
  remaining := 2
  events := [.name ⟨0⟩ "AccountNotMigrated"]

private def messageState : Heap where
  strings := [some "AccountNotMigrated", some "Account must be migrated before exiting"]
  boxes := []
  remaining := 1
  events := [.name ⟨0⟩ "AccountNotMigrated",
    .message ⟨1⟩ "Account must be migrated before exiting"]

def migrationPayload : AnchorErrorOwned.Payload StringId :=
  .anchor ⟨⟨0⟩, 2042, ⟨1⟩, none, none⟩

def boxedState : Heap where
  strings := [some "AccountNotMigrated", some "Account must be migrated before exiting"]
  boxes := [some migrationPayload]
  remaining := 0
  events := [.name ⟨0⟩ "AccountNotMigrated",
    .message ⟨1⟩ "Account must be migrated before exiting", .box ⟨0⟩ migrationPayload]

theorem migration_error_allocates_name_message_then_box :
    Solanalib.Specs.AnchorLangError.Error.from_error_code_run
      Solanalib.Specs.AnchorLangError.Error.from_error_code_sample
      (AnchorErrorOwned.Reference.initial 3) migrationCode
      (.returned ⟨⟨0⟩⟩ boxedState) := by
  exact ⟨.returned ⟨0⟩ nameState, rfl, .returned ⟨1⟩ messageState, rfl,
    .returned ⟨0⟩ boxedState, rfl, rfl⟩

theorem migration_name_copies_only_the_selected_variant_name :
    Solanalib.Specs.AnchorLangError.ErrorCode.name_run
      Solanalib.Specs.AnchorLangError.ErrorCode.name_sample
      (AnchorErrorOwned.Reference.initial 1) migrationCode
      (.returned ⟨0⟩ { nameState with remaining := 0 }) := rfl

def logPayload : Payload ProgramError.Value Nat :=
  .program ⟨.borshIoError, some (.accountName 7), none⟩

def request : FormatRequest Nat ProgramError.Value :=
  ⟨"ProgramError caused by account: {}. Error Code: {:?}. Error Number: {}. Error Message: \
    {}.",
    [.string 7, .debugProgram .borshIoError, .number 64424509440,
      .displayProgram .borshIoError]⟩

def logEvents : List LogEvent :=
  [.format request 0, .logged 0, .dropped 0]

/-- The ordinary formatter/drop providers use the existing trace vocabulary;
only the finite result of the user logger varies. The unit Borsh error has no String
clone dependency. These are model scenarios, not Rust library-body proofs. -/
abbrev logger (unwinds : Bool) : LogTypes .modern where
  State := List LogEvent
  StringResource := Nat
  BoxResource := Nat
  Unwind := Nat
  Terminal := Empty
  storage := .boxed
  currentBox := fun _ resource => if resource = 0 then some logPayload else none
  cloneString := ()
  format := logSample.format
  logString := fun before resource outcome =>
    outcome = if unwinds then .unwound 17 (before ++ [.logged resource])
      else .returned () (before ++ [.logged resource])
  logLiteral := fun before text outcome => outcome = .returned () (before ++ [.literal text])
  logPubkey := fun before key outcome => outcome = .returned () (before ++ [.pubkey key])
  dropString := logSample.dropString
  double := fun _ _ _ _ => False

theorem modern_borsh_log_uses_exact_status_and_one_temporary :
    Solanalib.Specs.AnchorLangError.Error.log_run ⟨logger false, rfl⟩ [] ⟨0⟩
      (.returned () logEvents) := by
  refine ⟨logPayload, rfl, .returned () logEvents, ?_, rfl⟩
  refine ⟨.returned (64424509440 : UInt64) [], ⟨_, rfl, rfl⟩, ?_⟩
  exact ⟨.returned 0 [.format request 0], ⟨_, rfl, rfl⟩,
    .returned () [.format request 0, .logged 0], rfl,
    .returned () logEvents, ⟨_, rfl, rfl⟩, rfl⟩

theorem logger_unwind_drops_temporary_and_retains_error_box :
    Solanalib.Specs.AnchorLangError.Error.log_run ⟨logger true, rfl⟩ [] ⟨0⟩
      (.unwound (17 : Nat) logEvents) ∧
    (logger true).currentBox logEvents 0 = some logPayload := by
  refine ⟨?_, rfl⟩
  refine ⟨logPayload, rfl, .unwound (17 : Nat) logEvents, ?_, rfl⟩
  refine ⟨.returned (64424509440 : UInt64) [], ⟨_, rfl, rfl⟩, ?_⟩
  exact formatLog_unwind (logger true) [] [.format request 0]
    [.format request 0, .logged 0] logEvents request 0 17 rfl rfl rfl

def oldPayload : AnchorErrorOwned.Payload StringId :=
  .anchor ⟨⟨0⟩, 2042, ⟨1⟩, some (.accountName ⟨2⟩), none⟩

def newPayload : AnchorErrorOwned.Payload StringId :=
  .anchor ⟨⟨0⟩, 2042, ⟨1⟩, some (.accountName ⟨4⟩), none⟩

def beforeName : Heap where
  strings := [some "error", some "message", some "old-account", some "input"]
  boxes := [some oldPayload]
  remaining := 1
  events := []

private def copiedName : Heap where
  strings := [some "error", some "message", some "old-account", some "input",
    some "new-account"]
  boxes := [some oldPayload]
  remaining := 0
  events := [.name ⟨4⟩ "new-account"]

private def droppedOrigin : Heap where
  strings := [some "error", some "message", none, some "input", some "new-account"]
  boxes := [some oldPayload]
  remaining := 0
  events := [.name ⟨4⟩ "new-account", .dropString ⟨2⟩ "old-account"]

private def storedName : Heap where
  strings := [some "error", some "message", none, some "input", some "new-account"]
  boxes := [some newPayload]
  remaining := 0
  events := [.name ⟨4⟩ "new-account", .dropString ⟨2⟩ "old-account", .write ⟨0⟩]

def afterName : Heap where
  strings := [some "error", some "message", none, none, some "new-account"]
  boxes := [some newPayload]
  remaining := 0
  events := [.name ⟨4⟩ "new-account", .dropString ⟨2⟩ "old-account", .write ⟨0⟩,
    .dropString ⟨3⟩ "input"]

abbrev nameCallbacks : NameTypes where
  toTypes := sampleAt .boxed
  Name := StringId
  Unwind := Empty
  toString := fun before _ => AnchorErrorOwned.Reference.ops.copyLiteral before "new-accoun\
    t"
  dropName := AnchorErrorOwned.Reference.ops.dropString
  double := AnchorErrorOwned.noDouble

theorem account_name_replacement_retains_box_and_cleans_old_origin_and_argument :
    Solanalib.Specs.AnchorLangError.Error.with_account_name_run ⟨nameCallbacks, rfl⟩
      beforeName (⟨⟨0⟩⟩, ⟨3⟩) (.returned ⟨⟨0⟩⟩ afterName) := by
  refine ⟨.returned ⟨⟨0⟩⟩ storedName, ?_, ?_⟩
  · refine ⟨.returned ⟨4⟩ copiedName, rfl, ?_⟩
    refine ⟨.returned ⟨⟨0⟩⟩ storedName, ?_, rfl⟩
    refine ⟨Payload.ofOwned oldPayload, rfl, .returned () droppedOrigin, ?_,
      Payload.ofOwned oldPayload, storedName, rfl, rfl, rfl⟩
    exact ⟨.returned () droppedOrigin, ⟨"old-account", rfl, rfl⟩, rfl⟩
  · refine ⟨.returned ⟨⟨0⟩⟩ afterName, ?_, Or.inl rfl⟩
    exact ⟨.returned () afterName, ⟨"input", rfl, rfl⟩, rfl⟩

end SolanalibTest.Specs.AnchorLangError.Operations
