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

namespace Solanalib.Specs.SolanaMsg.host_stdout

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- This release always uses std on the host and has no host-no-std branch. -/
inductive Target where
  | solana
  | host
  deriving DecidableEq, Repr

structure Index where
  State : Type
  Unwind : Type
  Terminal : Type
  target : Target
  sink : Callback.Run State Log.Event Unit Unwind Terminal

def sol_log_contract : Family where
  Index := Index
  State := Index.State
  Args := fun _ => String
  Value := fun _ => Unit
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before message =>
      index.sink before (match index.target with
        | .solana => .text (Log.utf8Bytes message)
        | .host => .stdoutLine message)
  }

def sol_log_run : FamilyRun sol_log_contract :=
  fun index before message => index.sink before (match index.target with
    | .solana => .text (Log.utf8Bytes message)
    | .host => .stdoutLine message)

theorem sol_log_reference : FamilyReference sol_log_contract sol_log_run := by
  intro _ _ _ _ _ called
  exact called

def sol_log_sample : Index where
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

end Solanalib.Specs.SolanaMsg.host_stdout
