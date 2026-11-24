/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.AccountInfo
import SolanalibTest.Conformance.Library.Families.SdkAccounts.Checks
import Solanalib.Specs.SolanaAccountInfo.Realloc

/-! Exact-version native AccountInfo records. Each checker decides its registered
reference and (when nontrivial) the registered precondition. The native provider
implements only the reached memory syscall boundary; no SDK body is replaced. -/

set_option autoImplicit false

open Solanalib.Specs.SolanaProgram

namespace SolanalibTest.Conformance.Library.Families.SdkAccounts

open Solanalib.Contracts.Model Solanalib.Specs.Core


def solana_account_info_2_3_0_as_ref : SolanalibTest.Conformance.Library.Checker where
  function :=
    "<solana_account_info::AccountInfo<'a> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'a>>>::as_ref"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.as_ref_run"
  check := asRefCheck Solanalib.Specs.SolanaAccountInfo.AccountInfo.as_ref_contract (fun _ _ =>
    rfl) Solanalib.Specs.SolanaAccountInfo.AccountInfo.as_ref_run
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.as_ref_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.as_ref_run"]

def solana_account_info_2_3_0_assign : SolanalibTest.Conformance.Library.Checker where
  function := "solana_account_info::AccountInfo::<'a>::assign"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.assign_run"
  check := assignCheck Solanalib.Specs.SolanaAccountInfo.AccountInfo.assign_contract (fun _ _ =>
    rfl) Solanalib.Specs.SolanaAccountInfo.AccountInfo.assign_run
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.assign_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.assign_run"]

def solana_account_info_2_3_0_data_is_empty : SolanalibTest.Conformance.Library.Checker where
  function := "solana_account_info::AccountInfo::<'a>::data_is_empty"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_is_empty_run"
  check := emptyCheck Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_is_empty_contract (fun _ _
    => rfl) Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_is_empty_run rfl
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_is_empty_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_is_empty_run"]

def solana_account_info_2_3_0_realloc : SolanalibTest.Conformance.Library.Checker where
  function := "solana_account_info::AccountInfo::<'a>::realloc"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.realloc_run"
  check := resizeCheck reallocArgsOf id
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.realloc_contract (fun _ _ => rfl)
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.realloc_run (fun _ _ => rfl)
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.realloc_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.realloc_run"]

def solana_account_info_2_3_0_resize : SolanalibTest.Conformance.Library.Checker where
  function := "solana_account_info::AccountInfo::<'a>::resize"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.resize_run"
  check := resizeCheck resizeArgsOf (fun a => ⟨a.1, a.2, true⟩)
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.resize_contract (fun _ _ => rfl)
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.resize_run (fun _ _ => rfl)
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.resize_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.resize_run"]

def solana_account_info_2_3_0_try_borrow_lamports : SolanalibTest.Conformance.Library.Checker where
  function := "solana_account_info::AccountInfo::<'a>::try_borrow_lamports"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_lamports_run"
  check := borrowCheck true
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_lamports_contract (fun _ _ => rfl)
    (returnsOf Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_lamports_run)
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_lamports_run rfl
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_lamports_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_lamports_ru\
    n"]

def solana_account_info_2_3_0_try_data_len : SolanalibTest.Conformance.Library.Checker where
  function := "solana_account_info::AccountInfo::<'a>::try_data_len"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_data_len_run"
  check := tryLenCheck Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_data_len_contract (fun _ _
    => rfl) Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_data_len_run rfl
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_data_len_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_data_len_run"]

def solana_account_info_2_3_0_checkers : List SolanalibTest.Conformance.Library.Checker := [
  solana_account_info_2_3_0_as_ref,
  solana_account_info_2_3_0_assign,
  solana_account_info_2_3_0_data_is_empty,
  solana_account_info_2_3_0_realloc,
  solana_account_info_2_3_0_resize,
  solana_account_info_2_3_0_try_borrow_lamports,
  solana_account_info_2_3_0_try_data_len]

end SolanalibTest.Conformance.Library.Families.SdkAccounts

namespace SolanalibTest.Conformance.Library.Families.SdkAccounts

open Solanalib.Contracts.Model Solanalib.Specs.Core


def solana_account_info_3_1_1_as_ref : SolanalibTest.Conformance.Library.Checker where
  function :=
    "<solana_account_info::AccountInfo<'a> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'a>>>::as_ref"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.as_ref_run"
  check := asRefCheck Solanalib.Specs.SolanaAccountInfo.AccountInfo.as_ref_contract (fun _ _ =>
    rfl) Solanalib.Specs.SolanaAccountInfo.AccountInfo.as_ref_run
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.as_ref_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.as_ref_run"]

def solana_account_info_3_1_1_assign : SolanalibTest.Conformance.Library.Checker where
  function := "solana_account_info::AccountInfo::<'a>::assign"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.assign_run"
  check := assignCheck Solanalib.Specs.SolanaAccountInfo.AccountInfo.assign_contract (fun _ _ =>
    rfl) Solanalib.Specs.SolanaAccountInfo.AccountInfo.assign_run
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.assign_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.assign_run"]

def solana_account_info_3_1_1_data_is_empty : SolanalibTest.Conformance.Library.Checker where
  function := "solana_account_info::AccountInfo::<'a>::data_is_empty"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_is_empty_run"
  check := emptyCheck Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_is_empty_contract (fun _ _
    => rfl) Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_is_empty_run rfl
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_is_empty_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_is_empty_run"]

def solana_account_info_3_1_1_resize : SolanalibTest.Conformance.Library.Checker where
  function := "solana_account_info::AccountInfo::<'a>::resize"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.resize_run"
  check := resizeCheck resizeArgsOf (fun a => ⟨a.1, a.2, true⟩)
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.resize_contract (fun _ _ => rfl)
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.resize_run (fun _ _ => rfl)
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.resize_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.resize_run"]

def solana_account_info_3_1_1_try_borrow_mut_lamports : SolanalibTest.Conformance.Library.Checker
  where
  function := "solana_account_info::AccountInfo::<'a>::try_borrow_mut_lamports"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_mut_lamports_run"
  check := borrowCheck true
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_mut_lamports_contract (fun _ _ => rfl)
    (returnsOf Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_mut_lamports_run)
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_mut_lamports_run rfl
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_mut_lamports_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_mut_lamport\
    s_run"]

def solana_account_info_3_1_1_try_data_len : SolanalibTest.Conformance.Library.Checker where
  function := "solana_account_info::AccountInfo::<'a>::try_data_len"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_data_len_run"
  check := tryLenCheck Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_data_len_contract (fun _ _
    => rfl) Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_data_len_run rfl
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_data_len_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_data_len_run"]

def solana_account_info_3_1_1_checkers : List SolanalibTest.Conformance.Library.Checker := [
  solana_account_info_3_1_1_as_ref,
  solana_account_info_3_1_1_assign,
  solana_account_info_3_1_1_data_is_empty,
  solana_account_info_3_1_1_resize,
  solana_account_info_3_1_1_try_borrow_mut_lamports,
  solana_account_info_3_1_1_try_data_len]

end SolanalibTest.Conformance.Library.Families.SdkAccounts

namespace SolanalibTest.Conformance.Library.Families.SdkAccounts

end SolanalibTest.Conformance.Library.Families.SdkAccounts

namespace SolanalibTest.Conformance.Library.Families.SdkAccounts

open Solanalib.Contracts.Model Solanalib.Specs.Core


def solana_program_1_18_26_assign : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::assign"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.assign_run"
  check := assignCheck account_info.AccountInfo.assign_contract (fun
    _ _ => rfl) account_info.AccountInfo.assign_run
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.assign_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.assign_run"]

def solana_program_1_18_26_clone : SolanalibTest.Conformance.Library.Checker where
  function := "<solana_program::account_info::AccountInfo<'a> as core::clone::Clone>::clone"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.clone_run"
  check := cloneCheck (account_info.AccountInfo.clone_run
    SolanalibTest.Conformance.Library.Families.AccountsV1.Info.cloneIndex) rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.clone_run"]

def solana_program_1_18_26_data_is_empty : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::data_is_empty"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.data_is_empty_run"
  check := emptyCheck account_info.AccountInfo.data_is_empty_contract
    (fun _ _ => rfl) account_info.AccountInfo.data_is_empty_run rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.data_is_empty_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.data_is_empty\
    _run"]

def solana_program_1_18_26_data_len : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::data_len"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.data_len_run"
  check := getterCheck .dataLen
    account_info.AccountInfo.data_len_contract (fun _ _ => rfl)
    account_info.AccountInfo.data_len_run rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.data_len_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.data_len_run"]

def solana_program_1_18_26_lamports : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::lamports"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.lamports_run"
  check := getterCheck .lamports
    account_info.AccountInfo.lamports_contract (fun _ _ => rfl)
    account_info.AccountInfo.lamports_run rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.lamports_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.lamports_run"]

def solana_program_1_18_26_realloc : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::realloc"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.realloc_run"
  check := resizeCheck reallocArgsOf id
    account_info.AccountInfo.realloc_contract (fun _ _ => rfl)
    account_info.AccountInfo.realloc_run (fun _ _ => rfl)
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.realloc_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.realloc_run"]

def solana_program_1_18_26_try_borrow_data : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::try_borrow_data"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_data_run"
  check := borrowCheck false
    account_info.AccountInfo.try_borrow_data_contract (fun _ _ =>
    rfl) account_info.AccountInfo.try_borrow_data_run
    AccountInfo.tryBorrowData rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_data_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_da\
    ta_run"]

def solana_program_1_18_26_try_borrow_lamports : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::try_borrow_lamports"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_lamports_\
    run"
  check := borrowCheck true
    account_info.AccountInfo.try_borrow_lamports_contract (fun _ _ =>
    rfl) (returnsOf account_info.AccountInfo.try_borrow_lamports_run)
    account_info.AccountInfo.try_borrow_lamports_run rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_lamports_r\
    un"]
  decidesRequires :=
    ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_lamports_run"]

def solana_program_1_18_26_try_borrow_mut_data : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::try_borrow_mut_data"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_mut_data_\
    run"
  check := borrowCheck false
    account_info.AccountInfo.try_borrow_mut_data_contract (fun _ _ =>
    rfl) account_info.AccountInfo.try_borrow_mut_data_run
    AccountInfo.tryBorrowMutData rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_mut_data_r\
    un"]
  decidesRequires :=
    ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_mut_data_run"]

def solana_program_1_18_26_try_data_len : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::try_data_len"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_data_len_run"
  check := tryLenCheck account_info.AccountInfo.try_data_len_contract
    (fun _ _ => rfl) account_info.AccountInfo.try_data_len_run rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_data_len_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_data_len_\
    run"]

def solana_program_1_18_26_checkers : List SolanalibTest.Conformance.Library.Checker := [
  solana_program_1_18_26_assign,
  solana_program_1_18_26_clone,
  solana_program_1_18_26_data_is_empty,
  solana_program_1_18_26_data_len,
  solana_program_1_18_26_lamports,
  solana_program_1_18_26_realloc,
  solana_program_1_18_26_try_borrow_data,
  solana_program_1_18_26_try_borrow_lamports,
  solana_program_1_18_26_try_borrow_mut_data,
  solana_program_1_18_26_try_data_len
]

end SolanalibTest.Conformance.Library.Families.SdkAccounts

namespace SolanalibTest.Conformance.Library.Families.SdkAccounts

end SolanalibTest.Conformance.Library.Families.SdkAccounts

namespace SolanalibTest.Conformance.Library.Families.SdkAccounts

open Solanalib.Contracts.Model Solanalib.Specs.Core


def solana_program_1_15_2_assign : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::assign"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.assign_run"
  check := assignCheck account_info.AccountInfo.assign_contract (fun
    _ _ => rfl) account_info.AccountInfo.assign_run
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.assign_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.assign_run"]

def solana_program_1_15_2_clone : SolanalibTest.Conformance.Library.Checker where
  function := "<solana_program::account_info::AccountInfo<'a> as core::clone::Clone>::clone"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.clone_run"
  check := cloneCheck (account_info.AccountInfo.clone_run
    SolanalibTest.Conformance.Library.Families.AccountsV1.Info.cloneIndex) rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.clone_run"]

def solana_program_1_15_2_data_len : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::data_len"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.data_len_run"
  check := getterCheck .dataLen
    account_info.AccountInfo.data_len_contract (fun _ _ => rfl)
    account_info.AccountInfo.data_len_run rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.data_len_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.data_len_run"]

def solana_program_1_15_2_lamports : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::lamports"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.lamports_run"
  check := getterCheck .lamports
    account_info.AccountInfo.lamports_contract (fun _ _ => rfl)
    account_info.AccountInfo.lamports_run rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.lamports_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.lamports_run"]

def solana_program_1_15_2_realloc : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::realloc"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.realloc_run"
  check := resizeCheck reallocArgsOf id
    account_info.AccountInfo.realloc_contract (fun _ _ => rfl)
    account_info.AccountInfo.realloc_run (fun _ _ => rfl)
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.realloc_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.realloc_run"]

def solana_program_1_15_2_try_borrow_data : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::try_borrow_data"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_data_run"
  check := borrowCheck false
    account_info.AccountInfo.try_borrow_data_contract (fun _ _ =>
    rfl) account_info.AccountInfo.try_borrow_data_run
    AccountInfo.tryBorrowData rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_data_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_da\
    ta_run"]

def solana_program_1_15_2_try_borrow_mut_data : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::try_borrow_mut_data"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_mut_data_\
    run"
  check := borrowCheck false
    account_info.AccountInfo.try_borrow_mut_data_contract (fun _ _ =>
    rfl) account_info.AccountInfo.try_borrow_mut_data_run
    AccountInfo.tryBorrowMutData rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_mut_data_r\
    un"]
  decidesRequires :=
    ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_mut_data_run"]

def solana_program_1_15_2_try_borrow_mut_lamports : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::try_borrow_mut_lamports"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_mut_lampo\
    rts_run"
  check := borrowCheck true
    account_info.AccountInfo.try_borrow_mut_lamports_contract (fun _
    _ => rfl) (returnsOf
    account_info.AccountInfo.try_borrow_mut_lamports_run)
    account_info.AccountInfo.try_borrow_mut_lamports_run rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_mut_lampor\
    ts_run"]
  decidesRequires :=
    ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_borrow_mut_lamports_run"]

def solana_program_1_15_2_try_data_len : SolanalibTest.Conformance.Library.Checker where
  function := "solana_program::account_info::AccountInfo::<'a>::try_data_len"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_data_len_run"
  check := tryLenCheck account_info.AccountInfo.try_data_len_contract
    (fun _ _ => rfl) account_info.AccountInfo.try_data_len_run rfl
  decides := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_data_len_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.account_info.AccountInfo.try_data_len_\
    run"]

def solana_program_1_15_2_checkers : List SolanalibTest.Conformance.Library.Checker := [
  solana_program_1_15_2_assign,
  solana_program_1_15_2_clone,
  solana_program_1_15_2_data_len,
  solana_program_1_15_2_lamports,
  solana_program_1_15_2_realloc,
  solana_program_1_15_2_try_borrow_data,
  solana_program_1_15_2_try_borrow_mut_data,
  solana_program_1_15_2_try_borrow_mut_lamports,
  solana_program_1_15_2_try_data_len
]

end SolanalibTest.Conformance.Library.Families.SdkAccounts

namespace SolanalibTest.Conformance.Library.Families.SdkAccounts

def corpora : List (String × List Checker) := [
  ("sdk_accounts_2_3_0", solana_account_info_2_3_0_checkers),
  ("sdk_accounts_3_1_1", solana_account_info_3_1_1_checkers),
  ("sdk_accounts_1_18_26", solana_program_1_18_26_checkers),
  ("sdk_accounts_1_15_2", solana_program_1_15_2_checkers)]

end SolanalibTest.Conformance.Library.Families.SdkAccounts
