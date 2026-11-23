/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaMsg.Log

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaMsg

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem appends_exact_utf8 :
    Solanalib.Specs.SolanaMsg.sol_log_run Solanalib.Specs.SolanaMsg.sol_log_sample [] "a"
      (.returned () [.text [97]]) := by
  simp only [Solanalib.Specs.SolanaMsg.sol_log_run, Solanalib.Specs.SolanaMsg.sol_log_sample,
    Log.textCall, Callback.ofFunction, Log.appendEvent, Log.utf8Bytes,
    String.toUTF8_eq_toByteArray] <;> rfl

theorem host_stdout_is_distinct :
    Log.textCall .hostStd (Callback.ofFunction Log.appendEvent) [] "a"
      (.returned () [.stdoutLine "a"]) := rfl

theorem host_without_std_calls_no_sink :
    Log.textCall .hostNoStd
      (fun (_ : Nat) (_ : Log.Event) (_ : Outcome Nat Unit String String) => False)
      3 "a" (.returned () 3) := rfl

def failedSink (state : Nat) (_ : Log.Event) : Outcome Nat Unit String String :=
  .unwound "stdout-write" (state + 1)

theorem log_failure_preserves_callback_state :
    Log.textCall .hostStd (Callback.ofFunction failedSink) 3 "a"
      (.unwound "stdout-write" 4) := rfl

theorem data_fields_are_retained :
    Log.dataCall .solana (Callback.ofFunction Log.appendEvent) [] [[1, 2], [], [3]]
      (.returned () [.data [[1, 2], [], [3]]]) := rfl

theorem runtime_projection_is_only_flattening :
    Log.Event.runtimeBytes (.data [[1, 2], [], [3]]) = some [1, 2, 3] := rfl

theorem distinct_events_can_have_same_runtime_projection :
    Log.Event.data [[1], [2]] ≠ .data [[1, 2]] ∧
      Log.Event.runtimeBytes (.data [[1], [2]]) =
        Log.Event.runtimeBytes (.data [[1, 2]]) := by
  constructor
  · decide
  · rfl

end SolanalibTest.Specs.SolanaMsg
