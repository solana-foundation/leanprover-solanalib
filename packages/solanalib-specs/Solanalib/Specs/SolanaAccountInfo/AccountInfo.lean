/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoFacts
public import Solanalib.Specs.Core.AccountInfoRc

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaAccountInfo.AccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core

abbrev State := Solanalib.Specs.Core.AccountInfo.State
abbrev Args := Solanalib.Specs.Core.AccountInfo.Args
abbrev Value := Solanalib.Specs.Core.AccountInfo.Value

/-- `AccountInfo::lamports` uses a temporary shared lamports borrow. -/
def lamports_contract := Solanalib.Specs.Core.AccountInfo.observationContract .lamports

/-- `AccountInfo::data_len` uses a temporary shared data borrow. -/
def data_len_contract := Solanalib.Specs.Core.AccountInfo.observationContract .dataLen

/-- `AccountInfo::try_borrow_data` preserves protocol validity and returns a
readable shared data guard or the AccountBorrowFailed error of the SDK. -/
def try_borrow_data_contract := Solanalib.Specs.Core.AccountInfo.dataBorrowContract .shared

/-- `AccountInfo::try_borrow_mut_data` does not require `is_writable`. -/
def try_borrow_mut_data_contract := Solanalib.Specs.Core.AccountInfo.dataBorrowContract .exclusive

/-- Value observation of an already completed clone, separate from its Rc calls. -/
def clone_observation_contract := Solanalib.Specs.Core.AccountInfo.cloneContract

/-- Derived `Clone` sequences both Rc dependencies and their terminal exits. -/
def clone_contract := AccountInfoRc.cloneFamily

def lamports_reference := Solanalib.Specs.Core.AccountInfo.observeReference .lamports
def data_len_reference := Solanalib.Specs.Core.AccountInfo.observeReference .dataLen
def try_borrow_data_reference :=
  returnsOf (Unwind := Empty) (Terminal := Empty) Solanalib.Specs.Core.AccountInfo.tryBorrowData
def try_borrow_mut_data_reference :=
  returnsOf (Unwind := Empty) (Terminal := Empty) Solanalib.Specs.Core.AccountInfo.tryBorrowMutData
def clone_observation_reference :=
  returnsOf (Unwind := Empty) (Terminal := Empty) Solanalib.Specs.Core.AccountInfo.cloneReference
def clone_reference := AccountInfoRc.cloneRun
def clone_sample := AccountInfoRc.cloneSample

theorem lamports_reference_holds : lamports_contract.Holds lamports_reference :=
  Solanalib.Specs.Core.AccountInfo.observationReference_holds .lamports

theorem data_len_reference_holds : data_len_contract.Holds data_len_reference :=
  Solanalib.Specs.Core.AccountInfo.observationReference_holds .dataLen

theorem try_borrow_data_reference_holds :
    try_borrow_data_contract.Holds try_borrow_data_reference :=
  (realized_iff_holds _ _).mp
    (Solanalib.Specs.Core.AccountInfo.dataBorrowReference_realizes .shared)

theorem try_borrow_mut_data_reference_holds :
    try_borrow_mut_data_contract.Holds try_borrow_mut_data_reference :=
  (realized_iff_holds _ _).mp
    (Solanalib.Specs.Core.AccountInfo.dataBorrowReference_realizes .exclusive)

theorem clone_observation_reference_holds :
    clone_observation_contract.Holds clone_observation_reference :=
  (realized_iff_holds _ _).mp Solanalib.Specs.Core.AccountInfo.cloneReference_realizes

theorem clone_reference_holds : FamilyReference clone_contract clone_reference :=
  AccountInfoRc.clone_reference

theorem lamports_reference_executes : lamports_contract.HasExecution lamports_reference := by
  refine ⟨Solanalib.Specs.Core.AccountInfo.sampleState,
    Solanalib.Specs.Core.AccountInfo.sampleArgs,
    .returned 40 (Solanalib.Specs.Core.AccountInfo.observe .lamports
      Solanalib.Specs.Core.AccountInfo.sampleState Solanalib.Specs.Core.AccountInfo.sampleInfo).2,
    Solanalib.Specs.Core.AccountInfo.sample_valid.observationReady .lamports, ?_⟩
  exact rfl

theorem data_len_reference_executes : data_len_contract.HasExecution data_len_reference := by
  refine ⟨Solanalib.Specs.Core.AccountInfo.sampleState,
    Solanalib.Specs.Core.AccountInfo.sampleArgs,
    .returned 3 (Solanalib.Specs.Core.AccountInfo.observe .dataLen
      Solanalib.Specs.Core.AccountInfo.sampleState Solanalib.Specs.Core.AccountInfo.sampleInfo).2,
    Solanalib.Specs.Core.AccountInfo.sample_valid.observationReady .dataLen, ?_⟩
  exact rfl

theorem try_borrow_data_reference_executes :
    try_borrow_data_contract.HasExecution try_borrow_data_reference := by
  refine ⟨Solanalib.Specs.Core.AccountInfo.sampleState,
    Solanalib.Specs.Core.AccountInfo.sampleArgs,
    .returned (.ok ⟨0, 0⟩) (Solanalib.Specs.Core.AccountInfo.tryBorrowData
      Solanalib.Specs.Core.AccountInfo.sampleState Solanalib.Specs.Core.AccountInfo.sampleArgs).2,
    Solanalib.Specs.Core.AccountInfo.sample_valid.dataBorrowReady, ?_⟩
  exact rfl

theorem try_borrow_mut_data_reference_executes :
    try_borrow_mut_data_contract.HasExecution try_borrow_mut_data_reference := by
  refine ⟨Solanalib.Specs.Core.AccountInfo.sampleState,
    Solanalib.Specs.Core.AccountInfo.sampleArgs,
    .returned (.ok ⟨0, 0⟩) (Solanalib.Specs.Core.AccountInfo.tryBorrowMutData
      Solanalib.Specs.Core.AccountInfo.sampleState Solanalib.Specs.Core.AccountInfo.sampleArgs).2,
    Solanalib.Specs.Core.AccountInfo.sample_valid.dataBorrowReady, ?_⟩
  exact rfl

theorem clone_observation_reference_executes :
    clone_observation_contract.HasExecution clone_observation_reference := by
  exact ⟨Solanalib.Specs.Core.AccountInfo.sampleState,
    Solanalib.Specs.Core.AccountInfo.sampleArgs,
    .returned Solanalib.Specs.Core.AccountInfo.sampleInfo
      Solanalib.Specs.Core.AccountInfo.sampleState,
    True.intro, rfl⟩

theorem clone_reference_executes :
    FamilyHasExecution clone_contract clone_reference clone_sample := AccountInfoRc.clone_execution

theorem lamports_satisfiable : lamports_contract.Satisfiable :=
  lamports_reference_executes.satisfiable
theorem data_len_satisfiable : data_len_contract.Satisfiable :=
  data_len_reference_executes.satisfiable
theorem try_borrow_data_satisfiable : try_borrow_data_contract.Satisfiable :=
  try_borrow_data_reference_executes.satisfiable
theorem try_borrow_mut_data_satisfiable : try_borrow_mut_data_contract.Satisfiable :=
  try_borrow_mut_data_reference_executes.satisfiable
theorem clone_observation_satisfiable : clone_observation_contract.Satisfiable :=
  clone_observation_reference_executes.satisfiable
theorem clone_satisfiable : FamilySatisfiable clone_contract clone_sample :=
  clone_reference_executes.satisfiable

end Solanalib.Specs.SolanaAccountInfo.AccountInfo
