/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.PinocchioResizeCall

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Pinocchio.account_info.AccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.PinocchioAccount

def is_signer_contract := headerContract (fun header => header.isSigner != 0)
def is_signer_run := headerRun (fun header => header.isSigner != 0)
theorem is_signer_reference : is_signer_contract.RealizedBy is_signer_run := header_reference _
theorem is_signer_satisfiable : is_signer_contract.Satisfiable := header_satisfiable _

def is_writable_contract := headerContract (fun header => header.isWritable != 0)
def is_writable_run := headerRun (fun header => header.isWritable != 0)
theorem is_writable_reference : is_writable_contract.RealizedBy is_writable_run := header_reference
  _
theorem is_writable_satisfiable : is_writable_contract.Satisfiable := header_satisfiable _

def key_contract : Solanalib.Contracts.Model State Handle PubkeyRef :=
  .returning (fun _ _ => True)
    (fun before handle value after => after = before ∧ value = keyRef handle)
def key_run (state : State) (handle : Handle) : PubkeyRef × State := (keyRef handle, state)
theorem key_reference : key_contract.RealizedBy key_run := by intro _ _ _; exact ⟨rfl, rfl⟩
theorem key_satisfiable : key_contract.Satisfiable := ⟨sampleState, sampleHandle, trivial⟩

def owner_contract : Solanalib.Contracts.Model State Handle PubkeyRef :=
  .returning (fun _ _ => True)
    (fun before handle value after => after = before ∧ value = ownerRef handle)
def owner_run (state : State) (handle : Handle) : PubkeyRef × State := (ownerRef handle, state)
theorem owner_reference : owner_contract.RealizedBy owner_run := by intro _ _ _; exact ⟨rfl, rfl⟩
theorem owner_satisfiable : owner_contract.Satisfiable := ⟨sampleState, sampleHandle, trivial⟩

def is_owned_by_contract : Solanalib.Contracts.Model State (Handle × Solanalib.Runtime.Pubkey) Bool
  :=
  .returning (fun before args => ∃ header, before.lookup args.1 = some header)
    (fun before args value after => after = before ∧
      ∃ header, before.lookup args.1 = some header ∧ value = decide (header.owner = args.2))
def is_owned_by_run (state : State) (args : Handle × Solanalib.Runtime.Pubkey) : Bool × State :=
  (decide ((state.header args.1).owner = args.2), state)
theorem is_owned_by_reference : is_owned_by_contract.RealizedBy is_owned_by_run := by
  rintro before args ⟨header, found⟩
  exact ⟨rfl, header, found, by simp [is_owned_by_run, State.header, found]⟩
theorem is_owned_by_satisfiable : is_owned_by_contract.Satisfiable :=
  ⟨sampleState, (sampleHandle, .zero), _, rfl⟩

def lamports_contract : Solanalib.Contracts.Model State Handle UInt64 :=
  .returning (fun before handle => ∃ value, before.content handle .lamports = some (.lamports
    value))
    (fun before handle value after => after = before ∧
      before.content handle .lamports = some (.lamports value))
def lamports_run (state : State) (handle : Handle) : UInt64 × State := (state.lamports handle,
  state)
theorem lamports_reference : lamports_contract.RealizedBy lamports_run := by
  rintro before handle ⟨value, found⟩
  exact ⟨rfl, by simp [lamports_run, State.lamports, found]⟩
theorem lamports_satisfiable : lamports_contract.Satisfiable :=
  ⟨sampleState, sampleHandle, 40, rfl⟩

def data_len_contract : Solanalib.Contracts.Model State Handle Nat :=
  .returning DataPresent (fun before handle value after => after = before ∧
    ∃ data, before.content handle .data = some (.data data) ∧ value = data.dataLen)
def data_len_run (state : State) (handle : Handle) : Nat × State := ((state.data handle).dataLen,
  state)
theorem data_len_reference : data_len_contract.RealizedBy data_len_run := by
  rintro before handle ⟨data, found⟩
  exact ⟨rfl, data, found, by simp [data_len_run, State.data, found]⟩
theorem data_len_satisfiable : data_len_contract.Satisfiable :=
  ⟨sampleState, sampleHandle, sampleInput.data, rfl⟩

def try_borrow_data_contract := borrowContract .data .shared
def try_borrow_data_run := acquire .data .shared
theorem try_borrow_data_reference : try_borrow_data_contract.RealizedBy try_borrow_data_run :=
  borrow_reference .data .shared
theorem try_borrow_data_satisfiable : try_borrow_data_contract.Satisfiable := borrow_satisfiable _ _

def try_borrow_mut_data_contract := borrowContract .data .exclusive
def try_borrow_mut_data_run := acquire .data .exclusive
theorem try_borrow_mut_data_reference : try_borrow_mut_data_contract.RealizedBy
  try_borrow_mut_data_run :=
  borrow_reference .data .exclusive
theorem try_borrow_mut_data_satisfiable : try_borrow_mut_data_contract.Satisfiable :=
  borrow_satisfiable _ _

def try_borrow_mut_lamports_contract := borrowContract .lamports .exclusive
def try_borrow_mut_lamports_run := acquire .lamports .exclusive
theorem try_borrow_mut_lamports_reference :
    try_borrow_mut_lamports_contract.RealizedBy try_borrow_mut_lamports_run :=
  borrow_reference .lamports .exclusive
theorem try_borrow_mut_lamports_satisfiable : try_borrow_mut_lamports_contract.Satisfiable :=
  borrow_satisfiable _ _

def resize_contract := resizeFamily
def resize_run := resizeCallRun
def resize_sample := resizeCallSample
theorem resize_reference : FamilyReference resize_contract resize_run := resizeCall_reference
theorem resize_hasExecution : FamilyHasExecution resize_contract resize_run resize_sample :=
  resizeCall_hasExecution
theorem resize_satisfiable : FamilySatisfiable resize_contract resize_sample :=
  resize_hasExecution.satisfiable

end Solanalib.Specs.Pinocchio.account_info.AccountInfo
