/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoResize

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaAccountInfo.AccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The volatile owner write targets shared owner storage directly. -/
def assign_contract := AccountInfoSdk.assignContract
def assign_run := AccountInfoSdk.assign
theorem assign_reference : assign_contract.RealizedBy assign_run := AccountInfoSdk.assign_realizes
theorem assign_satisfiable : assign_contract.Satisfiable :=
  ⟨AccountInfoSdk.sample, (AccountInfo.sampleInfo, .zero), by change 0 < 1; decide⟩

/-- Checked shared lamports borrowing returns a current live guard. -/
def try_borrow_lamports_contract := AccountInfoSdk.lamportsBorrowContract .shared
def try_borrow_lamports_run := AccountInfoSdk.borrowLamports .shared
theorem try_borrow_lamports_reference :
    try_borrow_lamports_contract.RealizedBy try_borrow_lamports_run :=
  AccountInfoSdk.lamportsBorrow_realizes .shared
theorem try_borrow_lamports_satisfiable : try_borrow_lamports_contract.Satisfiable :=
  ⟨AccountInfo.sampleState, AccountInfo.sampleArgs, AccountInfoSdk.sample_lamportsReady⟩

/-- Checked length reading releases its temporary guard before either return. -/
def try_data_len_contract := AccountInfoSdk.tryDataLenContract
def try_data_len_run := AccountInfoSdk.tryDataLenReference
theorem try_data_len_reference : try_data_len_contract.Holds try_data_len_run :=
  AccountInfoSdk.tryDataLen_holds
theorem try_data_len_has_execution : try_data_len_contract.HasExecution try_data_len_run :=
  ⟨AccountInfo.sampleState, AccountInfo.sampleArgs,
    .returned (.ok 3) (AccountInfo.observe .dataLen AccountInfo.sampleState
      AccountInfo.sampleInfo).2,
    AccountInfo.sample_valid.observationReady .dataLen, rfl⟩
theorem try_data_len_satisfiable : try_data_len_contract.Satisfiable :=
  try_data_len_has_execution.satisfiable

/-- Resize fixes zero initialization to true while preserving the source
borrow, equality and growth checks, metadata updates and guard cleanup. -/
def resize_contract : Solanalib.Contracts.Model AccountInfoSdk.State (AccountInfo.Value × Nat)
    (Except ProgramError.Value Unit) Empty AccountInfoSdk.ResizeTerminal where
  requires := fun state args => AccountInfoSdk.ResizeReady state ⟨args.1, args.2, true⟩
  post := fun state args => AccountInfoSdk.resizeContract.post state ⟨args.1, args.2, true⟩

def resize_run (state : AccountInfoSdk.State) (args : AccountInfo.Value × Nat) :=
  AccountInfoSdk.resizeReference state ⟨args.1, args.2, true⟩

theorem resize_reference : resize_contract.Holds resize_run := by
  intro state args outcome ready step
  exact AccountInfoSdk.resize_holds state ⟨args.1, args.2, true⟩ outcome ready step

theorem resize_has_execution : resize_contract.HasExecution resize_run := by
  obtain ⟨outcome, step⟩ := AccountInfoSdk.resize_exists _ _ AccountInfoSdk.sample_resizeReady
  exact ⟨AccountInfoSdk.sample, (AccountInfo.sampleInfo, 5), outcome,
    AccountInfoSdk.sample_resizeReady, step⟩

theorem resize_satisfiable : resize_contract.Satisfiable := resize_has_execution.satisfiable

end Solanalib.Specs.SolanaAccountInfo.AccountInfo

namespace Solanalib.Specs.SolanaAccountInfo.AccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Reflexive AsRef returns the same existing reference without Rc cloning. -/
def as_ref_contract := AccountInfoSdk.asRefContract
def as_ref_run := AccountInfoSdk.asRef
theorem as_ref_reference : as_ref_contract.RealizedBy as_ref_run := AccountInfoSdk.asRef_realizes
theorem as_ref_satisfiable : as_ref_contract.Satisfiable := ⟨AccountInfo.sampleState, ⟨0⟩, trivial⟩

end Solanalib.Specs.SolanaAccountInfo.AccountInfo

namespace Solanalib.Specs.SolanaAccountInfo.AccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The unchecked empty getter propagates the configured RefCell panic. -/
def data_is_empty_contract := AccountInfoSdk.dataIsEmptyContract
def data_is_empty_run := AccountInfoSdk.dataIsEmptyReference
theorem data_is_empty_reference : data_is_empty_contract.Holds data_is_empty_run :=
  AccountInfoSdk.dataIsEmpty_holds
theorem data_is_empty_has_execution : data_is_empty_contract.HasExecution data_is_empty_run :=
  ⟨AccountInfo.sampleState, AccountInfo.sampleArgs,
    .returned false (AccountInfo.observe .dataLen AccountInfo.sampleState AccountInfo.sampleInfo).2,
    AccountInfo.sample_valid.observationReady .dataLen, rfl⟩
theorem data_is_empty_satisfiable : data_is_empty_contract.Satisfiable :=
  data_is_empty_has_execution.satisfiable

end Solanalib.Specs.SolanaAccountInfo.AccountInfo

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaAccountInfo.AccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Checked mutable lamports borrowing returns a current live guard. -/
def try_borrow_mut_lamports_contract := AccountInfoSdk.lamportsBorrowContract .exclusive
def try_borrow_mut_lamports_run := AccountInfoSdk.borrowLamports .exclusive
theorem try_borrow_mut_lamports_reference :
    try_borrow_mut_lamports_contract.RealizedBy try_borrow_mut_lamports_run :=
  AccountInfoSdk.lamportsBorrow_realizes .exclusive
theorem try_borrow_mut_lamports_satisfiable : try_borrow_mut_lamports_contract.Satisfiable :=
  ⟨AccountInfo.sampleState, AccountInfo.sampleArgs, AccountInfoSdk.sample_lamportsReady⟩

end Solanalib.Specs.SolanaAccountInfo.AccountInfo
