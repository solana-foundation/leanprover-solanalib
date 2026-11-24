/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Log
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaMsg

open Solanalib.Contracts.Model Solanalib.Specs.Core

structure LogIndex where
  State : Type
  Unwind : Type
  Terminal : Type
  target : Log.TextTarget
  sink : Callback.Run State Log.Event Unit Unwind Terminal

def sol_log_contract : Family where
  Index := LogIndex
  State := LogIndex.State
  Args := fun _ => String
  Value := fun _ => Unit
  Unwind := LogIndex.Unwind
  Terminal := LogIndex.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before message outcome => match index.target with
      | .solana => index.sink before (.text (Log.utf8Bytes message)) outcome
      | .hostStd => index.sink before (.stdoutLine message) outcome
      | .hostNoStd => outcome = .returned () before
  }

def sol_log_run : FamilyRun sol_log_contract :=
  fun index => Log.textCall index.target index.sink

theorem sol_log_reference : FamilyReference sol_log_contract sol_log_run := by
  intro index before message outcome _ step
  exact step

def sol_log_sample : LogIndex where
  State := List Log.Event
  Unwind := String
  Terminal := String
  target := .solana
  sink := Callback.ofFunction Log.appendEvent

theorem sol_log_hasExecution :
    FamilyHasExecution sol_log_contract sol_log_run sol_log_sample :=
  ⟨[], "hello", .returned () [.text (Log.utf8Bytes "hello")], True.intro, rfl⟩

theorem sol_log_satisfiable : FamilySatisfiable sol_log_contract sol_log_sample :=
  sol_log_hasExecution.satisfiable

end Solanalib.Specs.SolanaMsg
