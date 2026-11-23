/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaMsg.LogHostStdout
public import Solanalib.Specs.SolanaMsg.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SolanaMsg.HostStdout

open Solanalib.Contracts.Model Solanalib.Specs.Core

def host : Solanalib.Specs.SolanaMsg.host_stdout.Index :=
  { Solanalib.Specs.SolanaMsg.host_stdout.sol_log_sample with target := .host }

theorem host_prints_line :
    Solanalib.Specs.SolanaMsg.host_stdout.sol_log_run host [] "host" (.returned () [.stdoutLine
      "host"]) := rfl

theorem host_is_not_noop :
    ¬ Solanalib.Specs.SolanaMsg.host_stdout.sol_log_run host [] "host" (.returned () []) := by
  intro impossible
  cases impossible

def unwindingHost : Solanalib.Specs.SolanaMsg.host_stdout.Index where
  State := List Log.Event
  Unwind := Nat
  Terminal := Nat
  target := .host
  sink := Callback.ofFunction fun before event => .unwound (5 : Nat) (before ++ [event])

theorem host_unwind_retains_emitted_event :
    Solanalib.Specs.SolanaMsg.host_stdout.sol_log_run unwindingHost [] "λ\n"
      (.unwound (5 : Nat) [.stdoutLine "λ\n"]) := rfl

def terminatingSolana : Solanalib.Specs.SolanaMsg.host_stdout.Index :=
  { unwindingHost with
    target := .solana
    sink := Callback.ofFunction fun (_ : List Log.Event) _ => .terminated (9 : Nat) }

theorem solana_terminal_sink_is_retained :
    Solanalib.Specs.SolanaMsg.host_stdout.sol_log_run terminatingSolana [] "message" (.terminated
      (9 : Nat)) := rfl

def selectedBuild : Versioning.Build where
  package := "solana-msg"
  version := "2.2.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

theorem compatible_stdout_identities :
    ["2.2.1", "2.2.2", "2.9.0"].all (fun version => decide
      ((Solanalib.Specs.SolanaMsg.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities .host_stdout_sol_log =
        [⟨"solana-msg", version, "solana_msg::sol_log", "solana_msg::sol_log"⟩])) = true := by
  decide +kernel

theorem outside_stdout_range_rejected :
    ["2.2.0", "3.0.0", "2.2.2-rc.1"].all (fun version => decide
      ((Solanalib.Specs.SolanaMsg.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities .host_stdout_sol_log = [])) = true :=
          by
  decide +kernel

end SolanalibTest.Specs.SolanaMsg.HostStdout
