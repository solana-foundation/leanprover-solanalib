/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.PinocchioLog.Logger
public import Solanalib.Specs.Core.FixedLoggerReference
public import Solanalib.Specs.PinocchioLog.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.PinocchioLog

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.FixedLogger

theorem default_initializes_only_length :
    Solanalib.Specs.PinocchioLog.logger.Logger.default_run ⟨3⟩ () ()
      (.returned ⟨[none, none, none], 0⟩ ()) := rfl

def partialWrite (before : List (Option UInt8) × List String) (_ : Unit) :
    Outcome (List (Option UInt8) × List String) Nat String (List String) :=
  .unwound "format" (before.1.set 0 (some 42), before.2 ++ ["write"])

def valueDrop (panics : Bool) (before : List String) (_ : Unit) :
    Outcome (List String) Unit String (List String) :=
  if panics then .unwound "drop" (before ++ ["drop"]) else .returned () (before ++ ["drop"])

def scriptIndex (capacity : Nat) (dropPanics : Bool) : AppendIndex where
  capacity := capacity
  Ref := Nat
  Value := Unit
  Aux := List String
  Unwind := String
  Terminal := List String
  write := Callback.ofFunction partialWrite
  writerSafe := by intro before value produced called; cases called; simp [partialWrite]
  drop := Callback.ofFunction (valueDrop dropPanics)
  double := fun before first later terminal => terminal = before ++ [first, later]

def scriptComputed (capacity : Nat) (panics : Bool) (before : Buffer × List String) (receiver :
  Nat) :=
  appendComputed (scriptIndex capacity panics) partialWrite (valueDrop panics)
    (fun (before : List String) (first later : String) => before ++ [first, later]) before
      (receiver, ())

theorem script_graph (capacity : Nat) (panics : Bool) (before : Buffer × List String) (receiver :
  Nat)
    (outcome : Outcome (Buffer × List String) Nat String (List String)) :
    Solanalib.Specs.PinocchioLog.logger.Logger.append_run (scriptIndex capacity panics) before
      (receiver, ()) outcome ↔
      outcome = scriptComputed capacity panics before receiver :=
  append_graph (scriptIndex capacity panics) partialWrite (valueDrop panics)
    (fun (before : List String) (first later : String) => before ++ [first, later]) rfl rfl
    (by intros; rfl) before (receiver, ()) outcome

theorem formatter_unwind_retains_partial_tail_and_drops_value :
    Solanalib.Specs.PinocchioLog.logger.Logger.append_run (scriptIndex 3 false) (Buffer.empty 3,
      []) ((7 : Nat), ())
      (.unwound "format" (⟨[some 42, none, none], 0⟩, ["write", "drop"])) :=
  (script_graph 3 false _ _ _).mpr rfl

def stoppedLog : LogIndex where
  capacity := 2
  Aux := Unit
  Unwind := Empty
  Terminal := Nat
  sink := Callback.ofFunction (fun _ bytes => .terminated bytes.length)

theorem log_terminal_preserves_sink_outcome :
    Solanalib.Specs.PinocchioLog.logger.Logger.log_run stoppedLog (⟨[some 226, some 64], 2⟩, ()) ()
      (.terminated (2 : Nat)) := ⟨.terminated (2 : Nat), rfl, rfl⟩

/-- Full buffers skip the formatter, preserve the prefix and consume the operand. -/
theorem full_buffer_still_drops_operand :
    Solanalib.Specs.PinocchioLog.logger.Logger.append_run (scriptIndex 3 false)
      (⟨[some 97, some 98, some 99], 3⟩, []) ((7 : Nat), ())
      (.returned (7 : Nat) (⟨[some 97, some 98, some 64], 3⟩, ["drop"])) :=
  (script_graph 3 false _ _ _).mpr rfl

/-- Capacity zero performs no storage write and still consumes the operand. -/
theorem zero_capacity_still_drops_operand :
    Solanalib.Specs.PinocchioLog.logger.Logger.append_run (scriptIndex 0 false)
      (Buffer.empty 0, []) ((7 : Nat), ())
      (.returned (7 : Nat) (Buffer.empty 0, ["drop"])) :=
  (script_graph 0 false _ _ _).mpr rfl

/-- Destructor unwind on a full buffer preserves the already marked bytes. -/
theorem full_buffer_drop_unwind_preserves_marker :
    Solanalib.Specs.PinocchioLog.logger.Logger.append_run (scriptIndex 3 true)
      (⟨[some 97, some 98, some 99], 3⟩, []) ((7 : Nat), ())
      (.unwound "drop" (⟨[some 97, some 98, some 64], 3⟩, ["drop"])) :=
  (script_graph 3 true _ _ _).mpr rfl

/-- A second unwind passes both reasons and the actual cleanup state to termination. -/
theorem formatter_and_drop_unwind_terminate :
    Solanalib.Specs.PinocchioLog.logger.Logger.append_run (scriptIndex 3 true)
      (Buffer.empty 3, []) ((7 : Nat), ())
      (.terminated ["write", "drop", "format", "drop"]) :=
  (script_graph 3 true _ _ _).mpr rfl

def terminalWrite (_ : List (Option UInt8) × List String) (_ : Unit) :
    Outcome (List (Option UInt8) × List String) Nat String (List String) :=
  .terminated ["formatter stopped"]

def terminalIndex : AppendIndex :=
  { scriptIndex 3 true with
    write := Callback.ofFunction terminalWrite
    writerSafe := by intro before value produced called; cases called; trivial }

/-- A terminal formatter bypasses the destructor, even when it would unwind. -/
theorem terminal_formatter_skips_operand_drop :
    Solanalib.Specs.PinocchioLog.logger.Logger.append_run terminalIndex
      (Buffer.empty 3, []) ((7 : Nat), ())
      (.terminated ["formatter stopped"]) :=
  (append_graph terminalIndex terminalWrite (valueDrop true)
    (fun (before : List String) (first later : String) => before ++ [first, later]) rfl rfl
    (by intros; rfl) _ _ _).mpr rfl

end SolanalibTest.Specs.PinocchioLog

namespace SolanalibTest.Specs.PinocchioLog.Logger.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def logger_Logger_appendBuild : Versioning.Build where
  package := "pinocchio-log"
  version := "0.5.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def logger_Logger_appendCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.5.1; eligible
  (logger_Logger_appendBuild, true),
  -- lower; eligible
  (logger_Logger_appendBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ logger_Logger_appendBuild with version := "0.5.98" }, true),
  -- exclusive-upper; unsupported
  ({ logger_Logger_appendBuild with version := "0.6.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ logger_Logger_appendBuild with version := "0.5.1-rc.1" }, false),
  -- wrong-package; unsupported
  ({ logger_Logger_appendBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ logger_Logger_appendBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.5.0; unsupported
  ({ logger_Logger_appendBuild with version := "0.5.0" }, false)
]

set_option maxRecDepth 8192 in
theorem logger_Logger_append_profile_controls :
    logger_Logger_appendCases.all (fun test =>
      (((Solanalib.Specs.PinocchioLog.Capabilities.catalog.applicability .logger_Logger_append).any
        (fun profile => ["pinocchio-log-0.5.1-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem logger_Logger_append_callable_identities :
    ["0.5.1", "0.5.98"].all (fun version =>
      (((Solanalib.Specs.PinocchioLog.Capabilities.catalog.forBuild
        { logger_Logger_appendBuild with version := version }).identities
          .logger_Logger_append).eraseDups ==
        [⟨"pinocchio-log", version, "pinocchio_log::logger::Logger::<BUFFER>::append",
          "pinocchio_log::logger::Logger::<BUFFER>::append"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def logger_Logger_defaultBuild : Versioning.Build where
  package := "pinocchio-log"
  version := "0.5.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := []

def logger_Logger_defaultCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.5.1; eligible
  (logger_Logger_defaultBuild, true),
  -- lower; eligible
  (logger_Logger_defaultBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ logger_Logger_defaultBuild with version := "0.5.98" }, true),
  -- exclusive-upper; unsupported
  ({ logger_Logger_defaultBuild with version := "0.6.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ logger_Logger_defaultBuild with version := "0.5.1-rc.1" }, false),
  -- wrong-package; unsupported
  ({ logger_Logger_defaultBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ logger_Logger_defaultBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- below-lower-bound-fixture-0.5.0; unsupported
  ({ logger_Logger_defaultBuild with version := "0.5.0" }, false)
]

set_option maxRecDepth 8192 in
theorem logger_Logger_default_profile_controls :
    logger_Logger_defaultCases.all (fun test =>
      (((Solanalib.Specs.PinocchioLog.Capabilities.catalog.applicability .logger_Logger_default).any
        (fun profile => ["pinocchio-log-0.5.1-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem logger_Logger_default_callable_identities :
    ["0.5.1", "0.5.98"].all (fun version =>
      (((Solanalib.Specs.PinocchioLog.Capabilities.catalog.forBuild
        { logger_Logger_defaultBuild with version := version }).identities
          .logger_Logger_default).eraseDups ==
        [⟨"pinocchio-log", version, "core::default::Default::default",
          "<pinocchio_log::logger::Logger<BUFFER> as core::default::Default>::default"⟩])) = true
          := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def logger_Logger_logBuild : Versioning.Build where
  package := "pinocchio-log"
  version := "0.5.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩]
  features := some []
  targetFeatures := some []
  dependencies := []

def logger_Logger_logCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.5.1; eligible
  (logger_Logger_logBuild, true),
  -- lower; eligible
  (logger_Logger_logBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ logger_Logger_logBuild with version := "0.5.98" }, true),
  -- exclusive-upper; unsupported
  ({ logger_Logger_logBuild with version := "0.6.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ logger_Logger_logBuild with version := "0.5.1-rc.1" }, false),
  -- wrong-package; unsupported
  ({ logger_Logger_logBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ logger_Logger_logBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ logger_Logger_logBuild with target := [] }, false),
  -- wrong-target-os; unsupported
  ({ logger_Logger_logBuild with target := [⟨"os", "linux"⟩] }, false),
  -- missing-target_features; unresolved
  ({ logger_Logger_logBuild with targetFeatures := none }, false),
  -- wrong-target_features; unsupported
  ({ logger_Logger_logBuild with targetFeatures := some ["static-syscalls"] }, false),
  -- below-lower-bound-fixture-0.5.0; unsupported
  ({ logger_Logger_logBuild with version := "0.5.0" }, false)
]

set_option maxRecDepth 8192 in
theorem logger_Logger_log_profile_controls :
    logger_Logger_logCases.all (fun test =>
      (((Solanalib.Specs.PinocchioLog.Capabilities.catalog.applicability .logger_Logger_log).any
        (fun profile => ["pinocchio-log-0.5.1-reviewed"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem logger_Logger_log_callable_identities :
    ["0.5.1", "0.5.98"].all (fun version =>
      (((Solanalib.Specs.PinocchioLog.Capabilities.catalog.forBuild
        { logger_Logger_logBuild with version := version }).identities
          .logger_Logger_log).eraseDups ==
        [⟨"pinocchio-log", version, "pinocchio_log::logger::Logger::<BUFFER>::log",
          "pinocchio_log::logger::Logger::<BUFFER>::log"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def logger_syscalls_sol_memcpy_Build : Versioning.Build where
  package := "pinocchio-log"
  version := "0.5.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩]
  features := some []
  targetFeatures := some []
  dependencies := []

def logger_syscalls_sol_memcpy_Cases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.5.1; eligible
  (logger_syscalls_sol_memcpy_Build, true),
  -- lower; eligible
  (logger_syscalls_sol_memcpy_Build, true),
  -- hypothetical-declaration-probe; eligible
  ({ logger_syscalls_sol_memcpy_Build with version := "0.5.98" }, true),
  -- exclusive-upper; unsupported
  ({ logger_syscalls_sol_memcpy_Build with version := "0.6.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ logger_syscalls_sol_memcpy_Build with version := "0.5.1-rc.1" }, false),
  -- wrong-package; unsupported
  ({ logger_syscalls_sol_memcpy_Build with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ logger_syscalls_sol_memcpy_Build with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-pointer_width; unresolved
  ({ logger_syscalls_sol_memcpy_Build with target := [⟨"os", "solana"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ logger_syscalls_sol_memcpy_Build with target := [⟨"pointer_width", "linux"⟩, ⟨"os", "s\
    olana"⟩]
    }, false),
  -- missing-target-os; unresolved
  ({ logger_syscalls_sol_memcpy_Build with target := [⟨"pointer_width", "64"⟩] }, false),
  -- wrong-target-os; unsupported
  ({ logger_syscalls_sol_memcpy_Build with target := [⟨"pointer_width", "64"⟩, ⟨"os", "linu\
    x"⟩] },
    false),
  -- missing-target_features; unresolved
  ({ logger_syscalls_sol_memcpy_Build with targetFeatures := none }, false),
  -- wrong-target_features; unsupported
  ({ logger_syscalls_sol_memcpy_Build with targetFeatures := some ["static-syscalls"] }, false),
  -- below-lower-bound-fixture-0.5.0; unsupported
  ({ logger_syscalls_sol_memcpy_Build with version := "0.5.0" }, false)
]

set_option maxRecDepth 8192 in
theorem logger_syscalls_sol_memcpy__profile_controls :
    logger_syscalls_sol_memcpy_Cases.all (fun test =>
      (((Solanalib.Specs.PinocchioLog.Capabilities.catalog.applicability
        .logger_syscalls_sol_memcpy_).any
        (fun profile => ["raw-runtime-pinocchio-log-0.5.1"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem logger_syscalls_sol_memcpy__callable_identities :
    ["0.5.1", "0.5.98"].all (fun version =>
      (((Solanalib.Specs.PinocchioLog.Capabilities.catalog.forBuild
        { logger_syscalls_sol_memcpy_Build with version := version }).identities
          .logger_syscalls_sol_memcpy_).eraseDups ==
        [⟨"pinocchio-log", version, "pinocchio_log::logger::syscalls::sol_memcpy_",
          "pinocchio_log::logger::syscalls::sol_memcpy_"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def logger_syscalls_sol_memset_Build : Versioning.Build where
  package := "pinocchio-log"
  version := "0.5.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩]
  features := some []
  targetFeatures := some []
  dependencies := []

def logger_syscalls_sol_memset_Cases : List (Versioning.Build × Bool) := [
  -- inspected-reference-0.5.1; eligible
  (logger_syscalls_sol_memset_Build, true),
  -- lower; eligible
  (logger_syscalls_sol_memset_Build, true),
  -- hypothetical-declaration-probe; eligible
  ({ logger_syscalls_sol_memset_Build with version := "0.5.98" }, true),
  -- exclusive-upper; unsupported
  ({ logger_syscalls_sol_memset_Build with version := "0.6.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ logger_syscalls_sol_memset_Build with version := "0.5.1-rc.1" }, false),
  -- wrong-package; unsupported
  ({ logger_syscalls_sol_memset_Build with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ logger_syscalls_sol_memset_Build with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-pointer_width; unresolved
  ({ logger_syscalls_sol_memset_Build with target := [⟨"os", "solana"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ logger_syscalls_sol_memset_Build with target := [⟨"pointer_width", "linux"⟩, ⟨"os", "s\
    olana"⟩]
    }, false),
  -- missing-target-os; unresolved
  ({ logger_syscalls_sol_memset_Build with target := [⟨"pointer_width", "64"⟩] }, false),
  -- wrong-target-os; unsupported
  ({ logger_syscalls_sol_memset_Build with target := [⟨"pointer_width", "64"⟩, ⟨"os", "linu\
    x"⟩] },
    false),
  -- missing-target_features; unresolved
  ({ logger_syscalls_sol_memset_Build with targetFeatures := none }, false),
  -- wrong-target_features; unsupported
  ({ logger_syscalls_sol_memset_Build with targetFeatures := some ["static-syscalls"] }, false),
  -- below-lower-bound-fixture-0.5.0; unsupported
  ({ logger_syscalls_sol_memset_Build with version := "0.5.0" }, false)
]

set_option maxRecDepth 8192 in
theorem logger_syscalls_sol_memset__profile_controls :
    logger_syscalls_sol_memset_Cases.all (fun test =>
      (((Solanalib.Specs.PinocchioLog.Capabilities.catalog.applicability
        .logger_syscalls_sol_memset_).any
        (fun profile => ["raw-runtime-pinocchio-log-0.5.1"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem logger_syscalls_sol_memset__callable_identities :
    ["0.5.1", "0.5.98"].all (fun version =>
      (((Solanalib.Specs.PinocchioLog.Capabilities.catalog.forBuild
        { logger_syscalls_sol_memset_Build with version := version }).identities
          .logger_syscalls_sol_memset_).eraseDups ==
        [⟨"pinocchio-log", version, "pinocchio_log::logger::syscalls::sol_memset_",
          "pinocchio_log::logger::syscalls::sol_memset_"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.PinocchioLog.Logger.Pr575Compatibility
