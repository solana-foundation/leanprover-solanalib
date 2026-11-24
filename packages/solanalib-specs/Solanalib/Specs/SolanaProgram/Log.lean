/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Log
public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.SdkLog

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.log

open Solanalib.Contracts.Model Solanalib.Specs.Core

structure DataIndex where
  State : Type
  Unwind : Type
  Terminal : Type
  target : Log.DataTarget
  sink : Callback.Run State Log.Event Unit Unwind Terminal

def sol_log_data_contract : Family where
  Index := DataIndex
  State := DataIndex.State
  Args := fun _ => List Solanalib.Runtime.Bytes
  Value := fun _ => Unit
  Unwind := DataIndex.Unwind
  Terminal := DataIndex.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before fields outcome => match index.target with
      | .solana => index.sink before (.data fields) outcome
      | .hostStub => index.sink before (.stubData fields) outcome
  }

def sol_log_data_run : FamilyRun sol_log_data_contract :=
  fun index => Log.dataCall index.target index.sink

theorem sol_log_data_reference : FamilyReference sol_log_data_contract sol_log_data_run := by
  intro index before fields outcome _ step
  exact step

def sol_log_data_sample : DataIndex where
  State := List Log.Event
  Unwind := String
  Terminal := String
  target := .solana
  sink := Callback.ofFunction Log.appendEvent

theorem sol_log_data_hasExecution :
    FamilyHasExecution sol_log_data_contract sol_log_data_run sol_log_data_sample :=
  ⟨[], [[1, 2], [], [3]], .returned () [.data [[1, 2], [], [3]]], True.intro, rfl⟩

theorem sol_log_data_satisfiable :
    FamilySatisfiable sol_log_data_contract sol_log_data_sample :=
  sol_log_data_hasExecution.satisfiable

end Solanalib.Specs.SolanaProgram.log

@[expose] public section

set_option autoImplicit false

/-! These Program models retain their exact source profiles. The current
catalog selection admits solana-program 1.18.26; releases and build conditions
are checked per member. The namespace alone grants no release admission. -/

namespace Solanalib.Specs.SolanaProgram.log

open Solanalib.Contracts.Model Solanalib.Specs.Core

def sol_log_contract : Family := SdkLog.textFamily
def sol_log_run : FamilyRun sol_log_contract := SdkLog.textReference
def sol_log_sample : sol_log_contract.Index := SdkLog.sample

theorem sol_log_reference : FamilyReference sol_log_contract sol_log_run :=
  SdkLog.text_reference

theorem sol_log_hasExecution :
    FamilyHasExecution sol_log_contract sol_log_run sol_log_sample :=
  SdkLog.text_hasExecution

theorem sol_log_satisfiable : FamilySatisfiable sol_log_contract sol_log_sample :=
  sol_log_hasExecution.satisfiable

end Solanalib.Specs.SolanaProgram.log

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.log

open Solanalib.Contracts.Model Solanalib.Specs.Core

def sol_log_compute_units_contract : Family := SdkLog.computeFamily
def sol_log_compute_units_run : FamilyRun sol_log_compute_units_contract := SdkLog.computeReference
def sol_log_compute_units_sample : sol_log_compute_units_contract.Index := SdkLog.sample

theorem sol_log_compute_units_reference : FamilyReference sol_log_compute_units_contract
  sol_log_compute_units_run :=
  SdkLog.compute_reference

theorem sol_log_compute_units_hasExecution :
    FamilyHasExecution sol_log_compute_units_contract sol_log_compute_units_run
      sol_log_compute_units_sample :=
  SdkLog.compute_hasExecution

theorem sol_log_compute_units_satisfiable : FamilySatisfiable sol_log_compute_units_contract
  sol_log_compute_units_sample :=
  sol_log_compute_units_hasExecution.satisfiable

end Solanalib.Specs.SolanaProgram.log
