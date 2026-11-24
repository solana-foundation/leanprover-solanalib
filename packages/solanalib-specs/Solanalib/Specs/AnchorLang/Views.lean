/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorViewsSamples

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

namespace accounts

def wrapper_key_contract := keyFamily
def wrapper_key_run := keyRun
def wrapper_key_sample := Sample.projection
theorem wrapper_key_reference : FamilyReference wrapper_key_contract wrapper_key_run :=
  key_reference
theorem wrapper_key_has_execution : FamilyHasExecution wrapper_key_contract wrapper_key_run
  wrapper_key_sample :=
  Sample.key_execution
theorem wrapper_key_satisfiable : FamilySatisfiable wrapper_key_contract wrapper_key_sample :=
  wrapper_key_has_execution.satisfiable

def borrowed_info_ref_contract := infoFamily .borrowed
def borrowed_info_ref_run := infoRun .borrowed
def borrowed_info_ref_sample := Sample.projection
theorem borrowed_info_ref_reference : FamilyReference borrowed_info_ref_contract
  borrowed_info_ref_run :=
  info_reference .borrowed
theorem borrowed_info_ref_has_execution : FamilyHasExecution borrowed_info_ref_contract
  borrowed_info_ref_run borrowed_info_ref_sample :=
  Sample.info_execution .borrowed
theorem borrowed_info_ref_satisfiable : FamilySatisfiable borrowed_info_ref_contract
  borrowed_info_ref_sample :=
  borrowed_info_ref_has_execution.satisfiable

end accounts

namespace Pubkey

def key_contract := pubkeyFamily
def key_run := pubkeyRun
def key_sample := Sample.pubkeyTypes
theorem key_reference : FamilyReference key_contract key_run :=
  pubkey_reference
theorem key_has_execution : FamilyHasExecution key_contract key_run key_sample :=
  Sample.pubkey_execution
theorem key_satisfiable : FamilySatisfiable key_contract key_sample :=
  key_has_execution.satisfiable

end Pubkey

namespace accounts.account.Account

def deref_mut_contract := mutableFamily
def deref_mut_run := mutableReference
def deref_mut_sample := Sample.mutableTypes
theorem deref_mut_reference : FamilyReference deref_mut_contract deref_mut_run :=
  mutable_reference
theorem deref_mut_has_execution : FamilyHasExecution deref_mut_contract deref_mut_run
  deref_mut_sample :=
  Sample.mutable_execution
theorem deref_mut_satisfiable : FamilySatisfiable deref_mut_contract deref_mut_sample :=
  deref_mut_has_execution.satisfiable

def clone_borrowed_info_contract := cloneFamily .borrowed
def clone_borrowed_info_run := cloneReference .borrowed
def clone_borrowed_info_sample := Sample.cloneTypes .borrowed
theorem clone_borrowed_info_reference : FamilyReference clone_borrowed_info_contract
  clone_borrowed_info_run :=
  clone_reference .borrowed
theorem clone_borrowed_info_has_execution : FamilyHasExecution clone_borrowed_info_contract
  clone_borrowed_info_run clone_borrowed_info_sample :=
  Sample.clone_execution .borrowed
theorem clone_borrowed_info_satisfiable : FamilySatisfiable clone_borrowed_info_contract
  clone_borrowed_info_sample :=
  clone_borrowed_info_has_execution.satisfiable

end accounts.account.Account

end Solanalib.Specs.AnchorLang

namespace Solanalib.Specs.AnchorLang.accounts

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

def clone_borrowed_info_contract := infoCloneFamily .borrowed
def clone_borrowed_info_run := infoCloneReference .borrowed
def clone_borrowed_info_sample := Sample.infoCloneTypes .borrowed
theorem clone_borrowed_info_reference : FamilyReference clone_borrowed_info_contract
  clone_borrowed_info_run :=
  infoClone_reference .borrowed
theorem clone_borrowed_info_has_execution : FamilyHasExecution clone_borrowed_info_contract
  clone_borrowed_info_run clone_borrowed_info_sample :=
  Sample.infoClone_execution .borrowed
theorem clone_borrowed_info_satisfiable : FamilySatisfiable clone_borrowed_info_contract
  clone_borrowed_info_sample :=
  clone_borrowed_info_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts

namespace Solanalib.Specs.AnchorLang.Lamports

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

def get_lamports_contract := AnchorViewsLamports.family
def get_lamports_run := AnchorViewsLamports.reference
def get_lamports_sample := AnchorViewsLamports.sample
theorem get_lamports_reference : FamilyReference get_lamports_contract get_lamports_run :=
  AnchorViewsLamports.reference_holds
theorem get_lamports_has_execution : FamilyHasExecution get_lamports_contract get_lamports_run
  get_lamports_sample :=
  AnchorViewsLamports.reference_execution
theorem get_lamports_satisfiable : FamilySatisfiable get_lamports_contract get_lamports_sample :=
  get_lamports_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.Lamports

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.accounts.account.Account

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

end Solanalib.Specs.AnchorLang.accounts.account.Account

namespace Solanalib.Specs.AnchorLang.accounts.account.Account

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

end Solanalib.Specs.AnchorLang.accounts.account.Account

namespace Solanalib.Specs.AnchorLang.accounts.account.Account

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

end Solanalib.Specs.AnchorLang.accounts.account.Account

namespace Solanalib.Specs.AnchorLang.accounts.account.Account

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

def into_inner_contract := intoInnerFamily .borrowed
def into_inner_run := intoInnerReference .borrowed
def into_inner_sample := Sample.moveTypes .borrowed
theorem into_inner_reference : FamilyReference into_inner_contract into_inner_run :=
  intoInner_reference .borrowed
theorem into_inner_has_execution : FamilyHasExecution into_inner_contract into_inner_run
  into_inner_sample :=
  Sample.intoInner_execution .borrowed
theorem into_inner_satisfiable : FamilySatisfiable into_inner_contract into_inner_sample :=
  into_inner_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.account.Account

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.accounts

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

def owned_info_ref_contract := infoFamily .owned
def owned_info_ref_run := infoRun .owned
def owned_info_ref_sample := Sample.projection
theorem owned_info_ref_reference : FamilyReference owned_info_ref_contract owned_info_ref_run :=
  info_reference .owned
theorem owned_info_ref_has_execution : FamilyHasExecution owned_info_ref_contract
  owned_info_ref_run owned_info_ref_sample :=
  Sample.info_execution .owned
theorem owned_info_ref_satisfiable : FamilySatisfiable owned_info_ref_contract
  owned_info_ref_sample :=
  owned_info_ref_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts

namespace Solanalib.Specs.AnchorLang.accounts.sysvar.Sysvar

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

def deref_contract := sharedFamily
def deref_run := sharedReference
def deref_sample := Sample.projection
theorem deref_reference : FamilyReference deref_contract deref_run :=
  shared_reference
theorem deref_has_execution : FamilyHasExecution deref_contract deref_run deref_sample :=
  Sample.shared_execution
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  deref_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.sysvar.Sysvar

namespace Solanalib.Specs.AnchorLang.accounts.account.Account

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

def set_inner_contract := setInnerFamily
def set_inner_run := setInnerReference
def set_inner_sample := Sample.setTypes
theorem set_inner_reference : FamilyReference set_inner_contract set_inner_run :=
  setInner_reference
theorem set_inner_has_execution : FamilyHasExecution set_inner_contract set_inner_run
  set_inner_sample :=
  Sample.setInner_execution
theorem set_inner_satisfiable : FamilySatisfiable set_inner_contract set_inner_sample :=
  set_inner_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.account.Account
