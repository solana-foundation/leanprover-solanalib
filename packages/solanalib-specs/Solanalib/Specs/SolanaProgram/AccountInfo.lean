/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoResize
public import Solanalib.Specs.Core.AccountInfoRc

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.account_info.AccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core


/-- Exact solana-program 1.18.26 binding to the shared AccountInfo semantics. -/

def assign_contract := AccountInfoSdk.assignContract
def assign_run := AccountInfoSdk.assign
theorem assign_reference : assign_contract.RealizedBy assign_run := AccountInfoSdk.assign_realizes
theorem assign_satisfiable : assign_contract.Satisfiable :=
  ⟨AccountInfoSdk.sample, (AccountInfo.sampleInfo, AccountInfo.sampleInfo.owner), by
    change 0 < 1; decide⟩

/-- Exact solana-program 1.18.26 binding to the shared AccountInfo semantics. -/

def clone_contract := AccountInfoRc.cloneFamily
def clone_run := AccountInfoRc.cloneRun
def clone_sample := AccountInfoRc.cloneSample
theorem clone_reference : FamilyReference clone_contract clone_run := AccountInfoRc.clone_reference
theorem clone_has_execution : FamilyHasExecution clone_contract clone_run clone_sample :=
  AccountInfoRc.clone_execution
theorem clone_satisfiable : FamilySatisfiable clone_contract clone_sample :=
  clone_has_execution.satisfiable

/-- Exact solana-program 1.18.26 binding to the shared AccountInfo semantics. -/

def data_is_empty_contract := AccountInfoSdk.dataIsEmptyContract
def data_is_empty_run := AccountInfoSdk.dataIsEmptyReference
theorem data_is_empty_reference : data_is_empty_contract.Holds data_is_empty_run :=
  AccountInfoSdk.dataIsEmpty_holds
theorem data_is_empty_has_execution : data_is_empty_contract.HasExecution data_is_empty_run := by
  obtain ⟨outcome, step⟩ := AccountInfoSdk.dataIsEmpty_exists AccountInfo.sampleState
    AccountInfo.sampleArgs (AccountInfo.sample_valid.observationReady .dataLen)
  exact ⟨AccountInfo.sampleState, AccountInfo.sampleArgs, outcome,
    AccountInfo.sample_valid.observationReady .dataLen, step⟩
theorem data_is_empty_satisfiable : data_is_empty_contract.Satisfiable :=
  data_is_empty_has_execution.satisfiable

/-- Exact solana-program 1.18.26 binding to the shared AccountInfo semantics. -/

def data_len_contract := AccountInfo.observationContract .dataLen
def data_len_run := AccountInfo.observeReference .dataLen
theorem data_len_reference : data_len_contract.Holds data_len_run :=
  AccountInfo.observationReference_holds .dataLen
theorem data_len_has_execution : data_len_contract.HasExecution data_len_run := by
  exact ⟨AccountInfo.sampleState, AccountInfo.sampleArgs,
    .returned 3 (AccountInfo.observe .dataLen AccountInfo.sampleState AccountInfo.sampleInfo).2,
    AccountInfo.sample_valid.observationReady .dataLen, rfl⟩
theorem data_len_satisfiable : data_len_contract.Satisfiable := data_len_has_execution.satisfiable

/-- Exact solana-program 1.18.26 binding to the shared AccountInfo semantics. -/

def lamports_contract := AccountInfo.observationContract .lamports
def lamports_run := AccountInfo.observeReference .lamports
theorem lamports_reference : lamports_contract.Holds lamports_run :=
  AccountInfo.observationReference_holds .lamports
theorem lamports_has_execution : lamports_contract.HasExecution lamports_run := by
  exact ⟨AccountInfo.sampleState, AccountInfo.sampleArgs,
    .returned 40 (AccountInfo.observe .lamports AccountInfo.sampleState AccountInfo.sampleInfo).2,
    AccountInfo.sample_valid.observationReady .lamports, rfl⟩
theorem lamports_satisfiable : lamports_contract.Satisfiable := lamports_has_execution.satisfiable

/-- Exact solana-program 1.18.26 binding to the shared AccountInfo semantics. -/

def realloc_contract := AccountInfoSdk.resizeContract
def realloc_run := AccountInfoSdk.resizeReference
theorem realloc_reference : realloc_contract.Holds realloc_run := AccountInfoSdk.resize_holds
theorem realloc_has_execution : realloc_contract.HasExecution realloc_run := by
  obtain ⟨outcome, step⟩ := AccountInfoSdk.resize_exists _ _ AccountInfoSdk.sample_resizeReady
  exact ⟨AccountInfoSdk.sample, AccountInfoSdk.sampleResizeArgs, outcome,
    AccountInfoSdk.sample_resizeReady, step⟩
theorem realloc_satisfiable : realloc_contract.Satisfiable := realloc_has_execution.satisfiable

/-- Exact solana-program 1.18.26 binding to the shared AccountInfo semantics. -/

def try_borrow_data_contract := AccountInfo.dataBorrowContract .shared
def try_borrow_data_run := returnsOf (Unwind := Empty) (Terminal := Empty) AccountInfo.tryBorrowData
theorem try_borrow_data_reference : try_borrow_data_contract.Holds try_borrow_data_run :=
  (realized_iff_holds _ _).mp (AccountInfo.dataBorrowReference_realizes .shared)
theorem try_borrow_data_has_execution : try_borrow_data_contract.HasExecution try_borrow_data_run
  := by
  exact ⟨AccountInfo.sampleState, AccountInfo.sampleArgs,
    .returned (.ok ⟨0, 0⟩) (AccountInfo.tryBorrowData AccountInfo.sampleState
      AccountInfo.sampleArgs).2,
    AccountInfo.sample_valid.dataBorrowReady, rfl⟩
theorem try_borrow_data_satisfiable : try_borrow_data_contract.Satisfiable :=
  try_borrow_data_has_execution.satisfiable

/-- Exact solana-program 1.18.26 binding to the shared AccountInfo semantics. -/

def try_borrow_lamports_contract := AccountInfoSdk.lamportsBorrowContract .shared
def try_borrow_lamports_run := AccountInfoSdk.borrowLamports .shared
theorem try_borrow_lamports_reference : try_borrow_lamports_contract.RealizedBy
  try_borrow_lamports_run :=
  AccountInfoSdk.lamportsBorrow_realizes .shared
theorem try_borrow_lamports_satisfiable : try_borrow_lamports_contract.Satisfiable :=
  ⟨AccountInfo.sampleState, AccountInfo.sampleArgs, AccountInfoSdk.sample_lamportsReady⟩

/-- Exact solana-program 1.18.26 binding to the shared AccountInfo semantics. -/

def try_borrow_mut_data_contract := AccountInfo.dataBorrowContract .exclusive
def try_borrow_mut_data_run := returnsOf (Unwind := Empty) (Terminal := Empty)
  AccountInfo.tryBorrowMutData
theorem try_borrow_mut_data_reference : try_borrow_mut_data_contract.Holds try_borrow_mut_data_run
  :=
  (realized_iff_holds _ _).mp (AccountInfo.dataBorrowReference_realizes .exclusive)
theorem try_borrow_mut_data_has_execution : try_borrow_mut_data_contract.HasExecution
  try_borrow_mut_data_run := by
  exact ⟨AccountInfo.sampleState, AccountInfo.sampleArgs,
    .returned (.ok ⟨0, 0⟩) (AccountInfo.tryBorrowMutData AccountInfo.sampleState
      AccountInfo.sampleArgs).2,
    AccountInfo.sample_valid.dataBorrowReady, rfl⟩
theorem try_borrow_mut_data_satisfiable : try_borrow_mut_data_contract.Satisfiable :=
  try_borrow_mut_data_has_execution.satisfiable

/-- Exact solana-program 1.18.26 binding to the shared AccountInfo semantics. -/

def try_data_len_contract := AccountInfoSdk.tryDataLenContract
def try_data_len_run := AccountInfoSdk.tryDataLenReference
theorem try_data_len_reference : try_data_len_contract.Holds try_data_len_run :=
  AccountInfoSdk.tryDataLen_holds
theorem try_data_len_has_execution : try_data_len_contract.HasExecution try_data_len_run := by
  obtain ⟨value, after, step⟩ := AccountInfoSdk.tryDataLen_exists AccountInfo.sampleState
    AccountInfo.sampleArgs (AccountInfo.sample_valid.observationReady .dataLen)
  exact ⟨AccountInfo.sampleState, AccountInfo.sampleArgs, .returned value after,
    AccountInfo.sample_valid.observationReady .dataLen, step⟩
theorem try_data_len_satisfiable : try_data_len_contract.Satisfiable :=
  try_data_len_has_execution.satisfiable

end Solanalib.Specs.SolanaProgram.account_info.AccountInfo

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.account_info.AccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Exact solana-program 1.15.2 binding to the shared AccountInfo semantics. -/

def try_borrow_mut_lamports_contract := AccountInfoSdk.lamportsBorrowContract .exclusive
def try_borrow_mut_lamports_run := AccountInfoSdk.borrowLamports .exclusive
theorem try_borrow_mut_lamports_reference : try_borrow_mut_lamports_contract.RealizedBy
  try_borrow_mut_lamports_run :=
  AccountInfoSdk.lamportsBorrow_realizes .exclusive
theorem try_borrow_mut_lamports_satisfiable : try_borrow_mut_lamports_contract.Satisfiable :=
  ⟨AccountInfo.sampleState, AccountInfo.sampleArgs, AccountInfoSdk.sample_lamportsReady⟩

end Solanalib.Specs.SolanaProgram.account_info.AccountInfo
