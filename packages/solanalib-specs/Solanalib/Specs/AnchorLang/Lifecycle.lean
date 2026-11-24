/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleProfiles

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Account lifecycle contracts grouped by their Rust receiver. The source
registry selects each reviewed release and build; the contract indices keep
callback, error, borrow and cleanup behavior explicit. -/

namespace Solanalib.Specs.AnchorLang

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

namespace accounts.account.Account

def try_accounts_contract := familyAtStorage (payloadAccountsFamily .account .borrowed) (fun types
  => types.errorStorage) .boxed
def try_accounts_run : FamilyRun try_accounts_contract := familyAtStorageRun (payloadAccountsFamily
  .account .borrowed) (fun types => types.errorStorage) .boxed (payloadAccountsRun .account
  .borrowed)
def try_accounts_sample : try_accounts_contract.Index := ⟨payloadAccountsSample .boxed, rfl⟩
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.payloadAccounts_reference
    .account .borrowed)
theorem try_accounts_has_execution :
    FamilyHasExecution try_accounts_contract try_accounts_run try_accounts_sample :=
  payloadAccounts_execution .account .borrowed .boxed
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

def close_contract := familyAtStorage (closeFamily true .legacy) (fun types => types.errorStorage)
  .boxed
def close_run : FamilyRun close_contract := familyAtStorageRun (closeFamily true .legacy) (fun
  types => types.errorStorage) .boxed (closeRun true .legacy)
def close_sample : close_contract.Index := ⟨closeSample .boxed, rfl⟩
theorem close_reference : FamilyReference close_contract close_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.close_reference true .legacy)
theorem close_has_execution :
    FamilyHasExecution close_contract close_run close_sample :=
  close_execution true .legacy .boxed
theorem close_satisfiable : FamilySatisfiable close_contract close_sample :=
  close_has_execution.satisfiable

def exit_contract := familyAtStorage (exitFamily .account false) (fun types => types.errorStorage)
  .boxed
def exit_run : FamilyRun exit_contract := familyAtStorageRun (exitFamily .account false) (fun types
  => types.errorStorage) .boxed (exitRun .account false)
def exit_sample : exit_contract.Index := ⟨exitSample .boxed, rfl⟩
theorem exit_reference : FamilyReference exit_contract exit_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.exit_reference .account false)
theorem exit_has_execution :
    FamilyHasExecution exit_contract exit_run exit_sample :=
  exit_execution .account false .boxed
theorem exit_satisfiable : FamilySatisfiable exit_contract exit_sample :=
  exit_has_execution.satisfiable

def try_from_unchecked_contract := familyAtStorage (payloadFamily .account .borrowed) (fun types =>
  types.errorStorage) .boxed
def try_from_unchecked_run : FamilyRun try_from_unchecked_contract := familyAtStorageRun
  (payloadFamily .account .borrowed) (fun types => types.errorStorage) .boxed (payloadRun .account
  .borrowed)
def try_from_unchecked_sample : try_from_unchecked_contract.Index := ⟨payloadSample .boxed, rfl⟩
theorem try_from_unchecked_reference : FamilyReference try_from_unchecked_contract
  try_from_unchecked_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.payload_reference .account
    .borrowed)
theorem try_from_unchecked_has_execution :
    FamilyHasExecution try_from_unchecked_contract try_from_unchecked_run try_from_unchecked_sample
      :=
  payload_execution .account .borrowed .boxed
theorem try_from_unchecked_satisfiable : FamilySatisfiable try_from_unchecked_contract
  try_from_unchecked_sample :=
  try_from_unchecked_has_execution.satisfiable

end accounts.account.Account

namespace accounts.account_info.AccountInfo

def try_accounts_contract := familyAtStorage (validationAccountsFamily .accountInfo .borrowed) (fun
  types => types.errorStorage) .boxed
def try_accounts_run : FamilyRun try_accounts_contract := familyAtStorageRun
  (validationAccountsFamily .accountInfo .borrowed) (fun types => types.errorStorage) .boxed
  (validationAccountsRun .accountInfo .borrowed)
def try_accounts_sample : try_accounts_contract.Index := ⟨validationAccountsSample .boxed, rfl⟩
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .accountInfo .borrowed)
theorem try_accounts_has_execution :
    FamilyHasExecution try_accounts_contract try_accounts_run try_accounts_sample :=
  validationAccounts_execution .boxed .accountInfo .borrowed
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

end accounts.account_info.AccountInfo

namespace accounts.boxed.Box

def try_accounts_contract := familyAtStorage (collectionBoxedFamily) (fun types =>
  types.errorStorage) .boxed
def try_accounts_run : FamilyRun try_accounts_contract := familyAtStorageRun
  (collectionBoxedFamily) (fun types => types.errorStorage) .boxed (collectionBoxedRun)
def try_accounts_sample : try_accounts_contract.Index := ⟨accountCollectionSample .boxed, rfl⟩
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.collectionBoxed_reference)
theorem try_accounts_has_execution :
    FamilyHasExecution try_accounts_contract try_accounts_run try_accounts_sample :=
  collectionBoxed_execution .boxed
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

def close_contract := boxedDispatchFamily
def close_run : FamilyRun close_contract := boxedDispatchRun
def close_sample : close_contract.Index := dispatchSample
theorem close_reference : FamilyReference close_contract close_run :=
  Solanalib.Specs.Core.AnchorLifecycle.boxedDispatch_reference
theorem close_has_execution :
    FamilyHasExecution close_contract close_run close_sample :=
  boxedDispatch_execution
theorem close_satisfiable : FamilySatisfiable close_contract close_sample :=
  close_has_execution.satisfiable

def exit_contract := boxedDispatchFamily
def exit_run : FamilyRun exit_contract := boxedDispatchRun
def exit_sample : exit_contract.Index := dispatchSample
theorem exit_reference : FamilyReference exit_contract exit_run :=
  Solanalib.Specs.Core.AnchorLifecycle.boxedDispatch_reference
theorem exit_has_execution :
    FamilyHasExecution exit_contract exit_run exit_sample :=
  boxedDispatch_execution
theorem exit_satisfiable : FamilySatisfiable exit_contract exit_sample :=
  exit_has_execution.satisfiable

end accounts.boxed.Box

namespace accounts.option.Option

def try_accounts_contract := familyAtStorage (optionalFamily) (fun types => types.errorStorage)
  .boxed
def try_accounts_run : FamilyRun try_accounts_contract := familyAtStorageRun (optionalFamily) (fun
  types => types.errorStorage) .boxed (optionalRun)
def try_accounts_sample : try_accounts_contract.Index := ⟨optionalSample .boxed, rfl⟩
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.optional_reference)
theorem try_accounts_has_execution :
    FamilyHasExecution try_accounts_contract try_accounts_run try_accounts_sample :=
  optional_execution .boxed
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

def exit_contract := optionDispatchFamily
def exit_run : FamilyRun exit_contract := optionDispatchRun
def exit_sample : exit_contract.Index := dispatchSample
theorem exit_reference : FamilyReference exit_contract exit_run :=
  Solanalib.Specs.Core.AnchorLifecycle.optionDispatch_reference
theorem exit_has_execution :
    FamilyHasExecution exit_contract exit_run exit_sample :=
  optionDispatch_execution
theorem exit_satisfiable : FamilySatisfiable exit_contract exit_sample :=
  exit_has_execution.satisfiable

end accounts.option.Option

namespace accounts.program.Program

def try_accounts_contract := familyAtStorage (validationAccountsFamily .program .borrowed) (fun
  types => types.errorStorage) .boxed
def try_accounts_run : FamilyRun try_accounts_contract := familyAtStorageRun
  (validationAccountsFamily .program .borrowed) (fun types => types.errorStorage) .boxed
  (validationAccountsRun .program .borrowed)
def try_accounts_sample : try_accounts_contract.Index := ⟨validationAccountsSample .boxed, rfl⟩
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .program .borrowed)
theorem try_accounts_has_execution :
    FamilyHasExecution try_accounts_contract try_accounts_run try_accounts_sample :=
  validationAccounts_execution .boxed .program .borrowed
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

end accounts.program.Program

namespace accounts.signer.Signer

def try_accounts_contract := familyAtStorage (validationAccountsFamily .signer .borrowed) (fun
  types => types.errorStorage) .boxed
def try_accounts_run : FamilyRun try_accounts_contract := familyAtStorageRun
  (validationAccountsFamily .signer .borrowed) (fun types => types.errorStorage) .boxed
  (validationAccountsRun .signer .borrowed)
def try_accounts_sample : try_accounts_contract.Index := ⟨validationAccountsSample .boxed, rfl⟩
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .signer .borrowed)
theorem try_accounts_has_execution :
    FamilyHasExecution try_accounts_contract try_accounts_run try_accounts_sample :=
  validationAccounts_execution .boxed .signer .borrowed
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

end accounts.signer.Signer

namespace AccountsExit

def exit_contract := defaultExitFamily
def exit_run : FamilyRun exit_contract := defaultExitRun
def exit_sample : exit_contract.Index := defaultExitSample
theorem exit_reference : FamilyReference exit_contract exit_run :=
  Solanalib.Specs.Core.AnchorLifecycle.defaultExit_reference
theorem exit_has_execution :
    FamilyHasExecution exit_contract exit_run exit_sample :=
  defaultExit_execution
theorem exit_satisfiable : FamilySatisfiable exit_contract exit_sample :=
  exit_has_execution.satisfiable

end AccountsExit

end Solanalib.Specs.AnchorLang

namespace Solanalib.Specs.AnchorLang

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

namespace accounts.interface.Interface

def try_accounts_contract := familyAtStorage (validationAccountsFamily .interface .borrowed) (fun
  types => types.errorStorage) .boxed
def try_accounts_run : FamilyRun try_accounts_contract := familyAtStorageRun
  (validationAccountsFamily .interface .borrowed) (fun types => types.errorStorage) .boxed
  (validationAccountsRun .interface .borrowed)
def try_accounts_sample : try_accounts_contract.Index := ⟨validationAccountsSample .boxed, rfl⟩
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .interface .borrowed)
theorem try_accounts_has_execution :
    FamilyHasExecution try_accounts_contract try_accounts_run try_accounts_sample :=
  validationAccounts_execution .boxed .interface .borrowed
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

end accounts.interface.Interface

namespace accounts.interface_account.InterfaceAccount

def try_accounts_contract := familyAtStorage (payloadAccountsFamily .interfaceAccount .borrowed)
  (fun types => types.errorStorage) .boxed
def try_accounts_run : FamilyRun try_accounts_contract := familyAtStorageRun (payloadAccountsFamily
  .interfaceAccount .borrowed) (fun types => types.errorStorage) .boxed (payloadAccountsRun
  .interfaceAccount .borrowed)
def try_accounts_sample : try_accounts_contract.Index := ⟨payloadAccountsSample .boxed, rfl⟩
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.payloadAccounts_reference
    .interfaceAccount .borrowed)
theorem try_accounts_has_execution :
    FamilyHasExecution try_accounts_contract try_accounts_run try_accounts_sample :=
  payloadAccounts_execution .interfaceAccount .borrowed .boxed
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

end accounts.interface_account.InterfaceAccount

namespace accounts.interface_account.InterfaceAccount

def exit_contract := familyAtStorage (exitFamily .interfaceAccount false) (fun types =>
  types.errorStorage) .boxed
def exit_run : FamilyRun exit_contract := familyAtStorageRun (exitFamily .interfaceAccount false)
  (fun types => types.errorStorage) .boxed (exitRun .interfaceAccount false)
def exit_sample : exit_contract.Index := ⟨exitSample .boxed, rfl⟩
theorem exit_reference : FamilyReference exit_contract exit_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.exit_reference .interfaceAccount
    false)
theorem exit_has_execution :
    FamilyHasExecution exit_contract exit_run exit_sample :=
  exit_execution .interfaceAccount false .boxed
theorem exit_satisfiable : FamilySatisfiable exit_contract exit_sample :=
  exit_has_execution.satisfiable

end accounts.interface_account.InterfaceAccount

namespace accounts.sysvar.Sysvar

def try_accounts_contract := familyAtStorage (validationAccountsFamily .sysvar .borrowed) (fun
  types => types.errorStorage) .boxed
def try_accounts_run : FamilyRun try_accounts_contract := familyAtStorageRun
  (validationAccountsFamily .sysvar .borrowed) (fun types => types.errorStorage) .boxed
  (validationAccountsRun .sysvar .borrowed)
def try_accounts_sample : try_accounts_contract.Index := ⟨validationAccountsSample .boxed, rfl⟩
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .sysvar .borrowed)
theorem try_accounts_has_execution :
    FamilyHasExecution try_accounts_contract try_accounts_run try_accounts_sample :=
  validationAccounts_execution .boxed .sysvar .borrowed
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

end accounts.sysvar.Sysvar

namespace accounts.unchecked_account.UncheckedAccount

def try_accounts_contract := familyAtStorage (validationAccountsFamily .unchecked .borrowed) (fun
  types => types.errorStorage) .boxed
def try_accounts_run : FamilyRun try_accounts_contract := familyAtStorageRun
  (validationAccountsFamily .unchecked .borrowed) (fun types => types.errorStorage) .boxed
  (validationAccountsRun .unchecked .borrowed)
def try_accounts_sample : try_accounts_contract.Index := ⟨validationAccountsSample .boxed, rfl⟩
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .unchecked .borrowed)
theorem try_accounts_has_execution :
    FamilyHasExecution try_accounts_contract try_accounts_run try_accounts_sample :=
  validationAccounts_execution .boxed .unchecked .borrowed
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

end accounts.unchecked_account.UncheckedAccount

namespace accounts.account.Account

def reload_contract := familyAtStorage (reloadFamily .legacy) (fun types => types.errorStorage)
  .boxed
def reload_run : FamilyRun reload_contract := familyAtStorageRun (reloadFamily .legacy) (fun types
  => types.errorStorage) .boxed (reloadRun .legacy)
def reload_sample : reload_contract.Index := ⟨reloadSample .boxed, rfl⟩
theorem reload_reference : FamilyReference reload_contract reload_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.reload_reference .legacy)
theorem reload_has_execution :
    FamilyHasExecution reload_contract reload_run reload_sample :=
  reload_execution .legacy .boxed
theorem reload_satisfiable : FamilySatisfiable reload_contract reload_sample :=
  reload_has_execution.satisfiable

end accounts.account.Account

namespace accounts.interface_account.InterfaceAccount

def reload_contract := familyAtStorage (reloadFamily .legacy) (fun types => types.errorStorage)
  .boxed
def reload_run : FamilyRun reload_contract := familyAtStorageRun (reloadFamily .legacy) (fun types
  => types.errorStorage) .boxed (reloadRun .legacy)
def reload_sample : reload_contract.Index := ⟨reloadSample .boxed, rfl⟩
theorem reload_reference : FamilyReference reload_contract reload_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.reload_reference .legacy)
theorem reload_has_execution :
    FamilyHasExecution reload_contract reload_run reload_sample :=
  reload_execution .legacy .boxed
theorem reload_satisfiable : FamilySatisfiable reload_contract reload_sample :=
  reload_has_execution.satisfiable

end accounts.interface_account.InterfaceAccount

end Solanalib.Specs.AnchorLang

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

namespace accounts.account.Account

end accounts.account.Account

namespace accounts.account.Account

def close_checked_contract := familyAtStorage (closeFamily false .checked) (fun types =>
  types.errorStorage) .boxed
def close_checked_run : FamilyRun close_checked_contract := familyAtStorageRun (closeFamily false
  .checked) (fun types => types.errorStorage) .boxed (closeRun false .checked)
def close_checked_sample : close_checked_contract.Index := ⟨closeSample .boxed, rfl⟩
theorem close_checked_reference : FamilyReference close_checked_contract close_checked_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.close_reference false .checked)
theorem close_checked_has_execution :
    FamilyHasExecution close_checked_contract close_checked_run close_checked_sample :=
  close_execution false .checked .boxed
theorem close_checked_satisfiable : FamilySatisfiable close_checked_contract close_checked_sample :=
  close_checked_has_execution.satisfiable

end accounts.account.Account

namespace accounts.account.Account

end accounts.account.Account

namespace accounts.interface.Interface

end accounts.interface.Interface

namespace accounts.interface_account.InterfaceAccount

end accounts.interface_account.InterfaceAccount

namespace accounts.interface_account.InterfaceAccount

end accounts.interface_account.InterfaceAccount

namespace accounts.program.Program

end accounts.program.Program

namespace accounts.signer.Signer

end accounts.signer.Signer

namespace accounts.unchecked_account.UncheckedAccount

end accounts.unchecked_account.UncheckedAccount

namespace AccountsExit

end AccountsExit

namespace accounts.account.Account

end accounts.account.Account

namespace accounts.boxed.Box

end accounts.boxed.Box

namespace accounts.boxed.Box

end accounts.boxed.Box

namespace accounts.interface_account.InterfaceAccount

def reload_released_guard_contract := familyAtStorage (reloadFamily .interfaceAccount) (fun types
  => types.errorStorage) .boxed
def reload_released_guard_run : FamilyRun reload_released_guard_contract := familyAtStorageRun
  (reloadFamily .interfaceAccount) (fun types => types.errorStorage) .boxed (reloadRun
  .interfaceAccount)
def reload_released_guard_sample : reload_released_guard_contract.Index := ⟨reloadSample .boxed,
  rfl⟩
theorem reload_released_guard_reference : FamilyReference reload_released_guard_contract
  reload_released_guard_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.reload_reference
    .interfaceAccount)
theorem reload_released_guard_has_execution :
    FamilyHasExecution reload_released_guard_contract reload_released_guard_run
      reload_released_guard_sample :=
  reload_execution .interfaceAccount .boxed
theorem reload_released_guard_satisfiable : FamilySatisfiable reload_released_guard_contract
  reload_released_guard_sample :=
  reload_released_guard_has_execution.satisfiable

end accounts.interface_account.InterfaceAccount

namespace accounts.interface_account.InterfaceAccount

def try_from_unchecked_contract := familyAtStorage (payloadFamily .interfaceAccount .borrowed) (fun
  types => types.errorStorage) .boxed
def try_from_unchecked_run : FamilyRun try_from_unchecked_contract := familyAtStorageRun
  (payloadFamily .interfaceAccount .borrowed) (fun types => types.errorStorage) .boxed (payloadRun
  .interfaceAccount .borrowed)
def try_from_unchecked_sample : try_from_unchecked_contract.Index := ⟨payloadSample .boxed, rfl⟩
theorem try_from_unchecked_reference : FamilyReference try_from_unchecked_contract
  try_from_unchecked_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.payload_reference
    .interfaceAccount .borrowed)
theorem try_from_unchecked_has_execution :
    FamilyHasExecution try_from_unchecked_contract try_from_unchecked_run try_from_unchecked_sample
      :=
  payload_execution .interfaceAccount .borrowed .boxed
theorem try_from_unchecked_satisfiable : FamilySatisfiable try_from_unchecked_contract
  try_from_unchecked_sample :=
  try_from_unchecked_has_execution.satisfiable

end accounts.interface_account.InterfaceAccount

namespace accounts.option.Option

end accounts.option.Option

namespace accounts.unchecked_account.UncheckedAccount

def try_from_contract := uncheckedFromFamily .borrowed
def try_from_run : FamilyRun try_from_contract := uncheckedFromRun .borrowed
def try_from_sample : try_from_contract.Index := uncheckedFromSample
theorem try_from_reference : FamilyReference try_from_contract try_from_run :=
  Solanalib.Specs.Core.AnchorLifecycle.uncheckedFrom_reference .borrowed
theorem try_from_has_execution :
    FamilyHasExecution try_from_contract try_from_run try_from_sample :=
  uncheckedFrom_execution .borrowed
theorem try_from_satisfiable : FamilySatisfiable try_from_contract try_from_sample :=
  try_from_has_execution.satisfiable

end accounts.unchecked_account.UncheckedAccount

end Solanalib.Specs.AnchorLang

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle






namespace accounts.system_account.SystemAccount

def try_accounts_contract := familyAtStorage (validationAccountsFamily .system .borrowed) (fun
  types => types.errorStorage) .boxed
def try_accounts_run : FamilyRun try_accounts_contract := familyAtStorageRun
  (validationAccountsFamily .system .borrowed) (fun types => types.errorStorage) .boxed
  (validationAccountsRun .system .borrowed)
def try_accounts_sample : try_accounts_contract.Index := ⟨validationAccountsSample .boxed, rfl⟩
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .system .borrowed)
theorem try_accounts_has_execution :
    FamilyHasExecution try_accounts_contract try_accounts_run try_accounts_sample :=
  validationAccounts_execution .boxed .system .borrowed
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

end accounts.system_account.SystemAccount










end Solanalib.Specs.AnchorLang

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

namespace accounts.account.Account

end accounts.account.Account

namespace accounts.account.Account

end accounts.account.Account

namespace accounts.account.Account

def exit_cloned_info_contract := familyAtStorage (exitFamily .account true) (fun types =>
  types.errorStorage) .boxed
def exit_cloned_info_run : FamilyRun exit_cloned_info_contract := familyAtStorageRun (exitFamily
  .account true) (fun types => types.errorStorage) .boxed (exitRun .account true)
def exit_cloned_info_sample : exit_cloned_info_contract.Index := ⟨exitSample .boxed, rfl⟩
theorem exit_cloned_info_reference : FamilyReference exit_cloned_info_contract exit_cloned_info_run
  :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.exit_reference .account true)
theorem exit_cloned_info_has_execution :
    FamilyHasExecution exit_cloned_info_contract exit_cloned_info_run exit_cloned_info_sample :=
  exit_execution .account true .boxed
theorem exit_cloned_info_satisfiable : FamilySatisfiable exit_cloned_info_contract
  exit_cloned_info_sample :=
  exit_cloned_info_has_execution.satisfiable

end accounts.account.Account

namespace accounts.interface_account.InterfaceAccount

end accounts.interface_account.InterfaceAccount

namespace accounts.interface_account.InterfaceAccount

def exit_cloned_info_contract := familyAtStorage (exitFamily .interfaceAccount true) (fun types =>
  types.errorStorage) .boxed
def exit_cloned_info_run : FamilyRun exit_cloned_info_contract := familyAtStorageRun (exitFamily
  .interfaceAccount true) (fun types => types.errorStorage) .boxed (exitRun .interfaceAccount true)
def exit_cloned_info_sample : exit_cloned_info_contract.Index := ⟨exitSample .boxed, rfl⟩
theorem exit_cloned_info_reference : FamilyReference exit_cloned_info_contract exit_cloned_info_run
  :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.exit_reference .interfaceAccount
    true)
theorem exit_cloned_info_has_execution :
    FamilyHasExecution exit_cloned_info_contract exit_cloned_info_run exit_cloned_info_sample :=
  exit_execution .interfaceAccount true .boxed
theorem exit_cloned_info_satisfiable : FamilySatisfiable exit_cloned_info_contract
  exit_cloned_info_sample :=
  exit_cloned_info_has_execution.satisfiable

end accounts.interface_account.InterfaceAccount

namespace accounts.program.Program

end accounts.program.Program

namespace accounts.program.Program

def try_from_contract := familyAtStorage (validationFamily .program .borrowed) (fun types =>
  types.errorStorage) .boxed
def try_from_run : FamilyRun try_from_contract := familyAtStorageRun (validationFamily .program
  .borrowed) (fun types => types.errorStorage) .boxed (validationRun .program .borrowed)
def try_from_sample : try_from_contract.Index := ⟨validationSample .boxed, rfl⟩
theorem try_from_reference : FamilyReference try_from_contract try_from_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validation_reference .program
    .borrowed)
theorem try_from_has_execution :
    FamilyHasExecution try_from_contract try_from_run try_from_sample :=
  validation_execution .boxed .program .borrowed
theorem try_from_satisfiable : FamilySatisfiable try_from_contract try_from_sample :=
  try_from_has_execution.satisfiable

end accounts.program.Program

namespace accounts.signer.Signer

end accounts.signer.Signer

namespace AccountsExit

end AccountsExit

namespace accounts.account.Account

end accounts.account.Account

namespace accounts.account_info.AccountInfo

end accounts.account_info.AccountInfo

namespace accounts.boxed.Box

end accounts.boxed.Box

namespace accounts.boxed.Box

end accounts.boxed.Box

namespace accounts.boxed.Box

end accounts.boxed.Box

namespace accounts.option.Option

end accounts.option.Option

namespace accounts.option.Option

end accounts.option.Option

namespace accounts.signer.Signer

def try_from_contract := familyAtStorage (validationFamily .signer .borrowed) (fun types =>
  types.errorStorage) .boxed
def try_from_run : FamilyRun try_from_contract := familyAtStorageRun (validationFamily .signer
  .borrowed) (fun types => types.errorStorage) .boxed (validationRun .signer .borrowed)
def try_from_sample : try_from_contract.Index := ⟨validationSample .boxed, rfl⟩
theorem try_from_reference : FamilyReference try_from_contract try_from_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validation_reference .signer
    .borrowed)
theorem try_from_has_execution :
    FamilyHasExecution try_from_contract try_from_run try_from_sample :=
  validation_execution .boxed .signer .borrowed
theorem try_from_satisfiable : FamilySatisfiable try_from_contract try_from_sample :=
  try_from_has_execution.satisfiable

end accounts.signer.Signer

end Solanalib.Specs.AnchorLang

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.AccountsExit

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

end Solanalib.Specs.AnchorLang.AccountsExit

namespace Solanalib.Specs.AnchorLang.accounts.account.Account

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

def close_inline_error_contract := familyAtStorage (closeFamily true .legacy) (fun types =>
  types.errorStorage) .inline
def close_inline_error_run : FamilyRun close_inline_error_contract := familyAtStorageRun
  (closeFamily true .legacy) (fun types => types.errorStorage) .inline (closeRun true .legacy)
def close_inline_error_sample : close_inline_error_contract.Index := ⟨closeSample .inline, rfl⟩
theorem close_inline_error_reference : FamilyReference close_inline_error_contract
  close_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.close_reference true .legacy)
theorem close_inline_error_has_execution :
    FamilyHasExecution close_inline_error_contract close_inline_error_run close_inline_error_sample
      :=
  close_execution true .legacy .inline
theorem close_inline_error_satisfiable : FamilySatisfiable close_inline_error_contract
  close_inline_error_sample :=
  close_inline_error_has_execution.satisfiable

def exit_inline_error_contract := familyAtStorage (exitFamily .account true) (fun types =>
  types.errorStorage) .inline
def exit_inline_error_run : FamilyRun exit_inline_error_contract := familyAtStorageRun (exitFamily
  .account true) (fun types => types.errorStorage) .inline (exitRun .account true)
def exit_inline_error_sample : exit_inline_error_contract.Index := ⟨exitSample .inline, rfl⟩
theorem exit_inline_error_reference : FamilyReference exit_inline_error_contract
  exit_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.exit_reference .account true)
theorem exit_inline_error_has_execution :
    FamilyHasExecution exit_inline_error_contract exit_inline_error_run exit_inline_error_sample :=
  exit_execution .account true .inline
theorem exit_inline_error_satisfiable : FamilySatisfiable exit_inline_error_contract
  exit_inline_error_sample :=
  exit_inline_error_has_execution.satisfiable

def reload_inline_error_contract := familyAtStorage (reloadFamily .legacy) (fun types =>
  types.errorStorage) .inline
def reload_inline_error_run : FamilyRun reload_inline_error_contract := familyAtStorageRun
  (reloadFamily .legacy) (fun types => types.errorStorage) .inline (reloadRun .legacy)
def reload_inline_error_sample : reload_inline_error_contract.Index := ⟨reloadSample .inline, rfl⟩
theorem reload_inline_error_reference : FamilyReference reload_inline_error_contract
  reload_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.reload_reference .legacy)
theorem reload_inline_error_has_execution :
    FamilyHasExecution reload_inline_error_contract reload_inline_error_run
      reload_inline_error_sample :=
  reload_execution .legacy .inline
theorem reload_inline_error_satisfiable : FamilySatisfiable reload_inline_error_contract
  reload_inline_error_sample :=
  reload_inline_error_has_execution.satisfiable

def try_accounts_inline_error_contract := familyAtStorage (payloadAccountsFamily .account .owned)
  (fun types => types.errorStorage) .inline
def try_accounts_inline_error_run : FamilyRun try_accounts_inline_error_contract :=
  familyAtStorageRun (payloadAccountsFamily .account .owned) (fun types => types.errorStorage)
  .inline (payloadAccountsRun .account .owned)
def try_accounts_inline_error_sample : try_accounts_inline_error_contract.Index :=
  ⟨payloadAccountsSample .inline, rfl⟩
theorem try_accounts_inline_error_reference : FamilyReference try_accounts_inline_error_contract
  try_accounts_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.payloadAccounts_reference
    .account .owned)
theorem try_accounts_inline_error_has_execution :
    FamilyHasExecution try_accounts_inline_error_contract try_accounts_inline_error_run
      try_accounts_inline_error_sample :=
  payloadAccounts_execution .account .owned .inline
theorem try_accounts_inline_error_satisfiable : FamilySatisfiable
  try_accounts_inline_error_contract try_accounts_inline_error_sample :=
  try_accounts_inline_error_has_execution.satisfiable

def try_from_inline_error_contract := familyAtStorage (payloadFamily .account .owned) (fun types =>
  types.errorStorage) .inline
def try_from_inline_error_run : FamilyRun try_from_inline_error_contract := familyAtStorageRun
  (payloadFamily .account .owned) (fun types => types.errorStorage) .inline (payloadRun .account
  .owned)
def try_from_inline_error_sample : try_from_inline_error_contract.Index := ⟨payloadSample .inline,
  rfl⟩
theorem try_from_inline_error_reference : FamilyReference try_from_inline_error_contract
  try_from_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.payload_reference .account .owned)
theorem try_from_inline_error_has_execution :
    FamilyHasExecution try_from_inline_error_contract try_from_inline_error_run
      try_from_inline_error_sample :=
  payload_execution .account .owned .inline
theorem try_from_inline_error_satisfiable : FamilySatisfiable try_from_inline_error_contract
  try_from_inline_error_sample :=
  try_from_inline_error_has_execution.satisfiable

def try_from_unchecked_inline_error_contract := familyAtStorage (payloadFamily .account .owned)
  (fun types => types.errorStorage) .inline
def try_from_unchecked_inline_error_run : FamilyRun try_from_unchecked_inline_error_contract :=
  familyAtStorageRun (payloadFamily .account .owned) (fun types => types.errorStorage) .inline
  (payloadRun .account .owned)
def try_from_unchecked_inline_error_sample : try_from_unchecked_inline_error_contract.Index :=
  ⟨payloadSample .inline, rfl⟩
theorem try_from_unchecked_inline_error_reference : FamilyReference
  try_from_unchecked_inline_error_contract try_from_unchecked_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.payload_reference .account .owned)
theorem try_from_unchecked_inline_error_has_execution :
    FamilyHasExecution try_from_unchecked_inline_error_contract try_from_unchecked_inline_error_run
      try_from_unchecked_inline_error_sample :=
  payload_execution .account .owned .inline
theorem try_from_unchecked_inline_error_satisfiable : FamilySatisfiable
  try_from_unchecked_inline_error_contract try_from_unchecked_inline_error_sample :=
  try_from_unchecked_inline_error_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.account.Account

namespace Solanalib.Specs.AnchorLang.accounts.account_info.AccountInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

def try_accounts_inline_error_contract := familyAtStorage (validationAccountsFamily .accountInfo
  .owned) (fun types => types.errorStorage) .inline
def try_accounts_inline_error_run : FamilyRun try_accounts_inline_error_contract :=
  familyAtStorageRun (validationAccountsFamily .accountInfo .owned) (fun types =>
  types.errorStorage) .inline (validationAccountsRun .accountInfo .owned)
def try_accounts_inline_error_sample : try_accounts_inline_error_contract.Index :=
  ⟨validationAccountsSample .inline, rfl⟩
theorem try_accounts_inline_error_reference : FamilyReference try_accounts_inline_error_contract
  try_accounts_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .accountInfo .owned)
theorem try_accounts_inline_error_has_execution :
    FamilyHasExecution try_accounts_inline_error_contract try_accounts_inline_error_run
      try_accounts_inline_error_sample :=
  validationAccounts_execution .inline .accountInfo .owned
theorem try_accounts_inline_error_satisfiable : FamilySatisfiable
  try_accounts_inline_error_contract try_accounts_inline_error_sample :=
  try_accounts_inline_error_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.account_info.AccountInfo

namespace Solanalib.Specs.AnchorLang.accounts.boxed.Box

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

def try_accounts_inline_error_contract := familyAtStorage (collectionBoxedFamily) (fun types =>
  types.errorStorage) .inline
def try_accounts_inline_error_run : FamilyRun try_accounts_inline_error_contract :=
  familyAtStorageRun (collectionBoxedFamily) (fun types => types.errorStorage) .inline
  (collectionBoxedRun)
def try_accounts_inline_error_sample : try_accounts_inline_error_contract.Index :=
  ⟨accountCollectionSample .inline, rfl⟩
theorem try_accounts_inline_error_reference : FamilyReference try_accounts_inline_error_contract
  try_accounts_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.collectionBoxed_reference)
theorem try_accounts_inline_error_has_execution :
    FamilyHasExecution try_accounts_inline_error_contract try_accounts_inline_error_run
      try_accounts_inline_error_sample :=
  collectionBoxed_execution .inline
theorem try_accounts_inline_error_satisfiable : FamilySatisfiable
  try_accounts_inline_error_contract try_accounts_inline_error_sample :=
  try_accounts_inline_error_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.boxed.Box

namespace Solanalib.Specs.AnchorLang.accounts.program.Program

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

def try_accounts_inline_error_contract := familyAtStorage (validationAccountsFamily .program
  .owned) (fun types => types.errorStorage) .inline
def try_accounts_inline_error_run : FamilyRun try_accounts_inline_error_contract :=
  familyAtStorageRun (validationAccountsFamily .program .owned) (fun types => types.errorStorage)
  .inline (validationAccountsRun .program .owned)
def try_accounts_inline_error_sample : try_accounts_inline_error_contract.Index :=
  ⟨validationAccountsSample .inline, rfl⟩
theorem try_accounts_inline_error_reference : FamilyReference try_accounts_inline_error_contract
  try_accounts_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .program .owned)
theorem try_accounts_inline_error_has_execution :
    FamilyHasExecution try_accounts_inline_error_contract try_accounts_inline_error_run
      try_accounts_inline_error_sample :=
  validationAccounts_execution .inline .program .owned
theorem try_accounts_inline_error_satisfiable : FamilySatisfiable
  try_accounts_inline_error_contract try_accounts_inline_error_sample :=
  try_accounts_inline_error_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.program.Program

namespace Solanalib.Specs.AnchorLang.accounts.signer.Signer

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

def try_accounts_inline_error_contract := familyAtStorage (validationAccountsFamily .signer .owned)
  (fun types => types.errorStorage) .inline
def try_accounts_inline_error_run : FamilyRun try_accounts_inline_error_contract :=
  familyAtStorageRun (validationAccountsFamily .signer .owned) (fun types => types.errorStorage)
  .inline (validationAccountsRun .signer .owned)
def try_accounts_inline_error_sample : try_accounts_inline_error_contract.Index :=
  ⟨validationAccountsSample .inline, rfl⟩
theorem try_accounts_inline_error_reference : FamilyReference try_accounts_inline_error_contract
  try_accounts_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .signer .owned)
theorem try_accounts_inline_error_has_execution :
    FamilyHasExecution try_accounts_inline_error_contract try_accounts_inline_error_run
      try_accounts_inline_error_sample :=
  validationAccounts_execution .inline .signer .owned
theorem try_accounts_inline_error_satisfiable : FamilySatisfiable
  try_accounts_inline_error_contract try_accounts_inline_error_sample :=
  try_accounts_inline_error_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.signer.Signer

namespace Solanalib.Specs.AnchorLang.accounts.system_account.SystemAccount

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

def try_accounts_inline_error_contract := familyAtStorage (validationAccountsFamily .system .owned)
  (fun types => types.errorStorage) .inline
def try_accounts_inline_error_run : FamilyRun try_accounts_inline_error_contract :=
  familyAtStorageRun (validationAccountsFamily .system .owned) (fun types => types.errorStorage)
  .inline (validationAccountsRun .system .owned)
def try_accounts_inline_error_sample : try_accounts_inline_error_contract.Index :=
  ⟨validationAccountsSample .inline, rfl⟩
theorem try_accounts_inline_error_reference : FamilyReference try_accounts_inline_error_contract
  try_accounts_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .system .owned)
theorem try_accounts_inline_error_has_execution :
    FamilyHasExecution try_accounts_inline_error_contract try_accounts_inline_error_run
      try_accounts_inline_error_sample :=
  validationAccounts_execution .inline .system .owned
theorem try_accounts_inline_error_satisfiable : FamilySatisfiable
  try_accounts_inline_error_contract try_accounts_inline_error_sample :=
  try_accounts_inline_error_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.system_account.SystemAccount

namespace Solanalib.Specs.AnchorLang.accounts.sysvar.Sysvar

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

def try_accounts_inline_error_contract := familyAtStorage (validationAccountsFamily .sysvar .owned)
  (fun types => types.errorStorage) .inline
def try_accounts_inline_error_run : FamilyRun try_accounts_inline_error_contract :=
  familyAtStorageRun (validationAccountsFamily .sysvar .owned) (fun types => types.errorStorage)
  .inline (validationAccountsRun .sysvar .owned)
def try_accounts_inline_error_sample : try_accounts_inline_error_contract.Index :=
  ⟨validationAccountsSample .inline, rfl⟩
theorem try_accounts_inline_error_reference : FamilyReference try_accounts_inline_error_contract
  try_accounts_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .sysvar .owned)
theorem try_accounts_inline_error_has_execution :
    FamilyHasExecution try_accounts_inline_error_contract try_accounts_inline_error_run
      try_accounts_inline_error_sample :=
  validationAccounts_execution .inline .sysvar .owned
theorem try_accounts_inline_error_satisfiable : FamilySatisfiable
  try_accounts_inline_error_contract try_accounts_inline_error_sample :=
  try_accounts_inline_error_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.sysvar.Sysvar

namespace Solanalib.Specs.AnchorLang.accounts.unchecked_account.UncheckedAccount

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

def try_accounts_inline_error_contract := familyAtStorage (validationAccountsFamily .unchecked
  .owned) (fun types => types.errorStorage) .inline
def try_accounts_inline_error_run : FamilyRun try_accounts_inline_error_contract :=
  familyAtStorageRun (validationAccountsFamily .unchecked .owned) (fun types => types.errorStorage)
  .inline (validationAccountsRun .unchecked .owned)
def try_accounts_inline_error_sample : try_accounts_inline_error_contract.Index :=
  ⟨validationAccountsSample .inline, rfl⟩
theorem try_accounts_inline_error_reference : FamilyReference try_accounts_inline_error_contract
  try_accounts_inline_error_run :=
  familyAtStorage_reference (Solanalib.Specs.Core.AnchorLifecycle.validationAccounts_reference
    .unchecked .owned)
theorem try_accounts_inline_error_has_execution :
    FamilyHasExecution try_accounts_inline_error_contract try_accounts_inline_error_run
      try_accounts_inline_error_sample :=
  validationAccounts_execution .inline .unchecked .owned
theorem try_accounts_inline_error_satisfiable : FamilySatisfiable
  try_accounts_inline_error_contract try_accounts_inline_error_sample :=
  try_accounts_inline_error_has_execution.satisfiable

def try_from_owned_info_contract := uncheckedFromFamily .owned
def try_from_owned_info_run : FamilyRun try_from_owned_info_contract := uncheckedFromRun .owned
def try_from_owned_info_sample : try_from_owned_info_contract.Index := uncheckedFromSample
theorem try_from_owned_info_reference : FamilyReference try_from_owned_info_contract
  try_from_owned_info_run :=
  Solanalib.Specs.Core.AnchorLifecycle.uncheckedFrom_reference .owned
theorem try_from_owned_info_has_execution :
    FamilyHasExecution try_from_owned_info_contract try_from_owned_info_run
      try_from_owned_info_sample :=
  uncheckedFrom_execution .owned
theorem try_from_owned_info_satisfiable : FamilySatisfiable try_from_owned_info_contract
  try_from_owned_info_sample :=
  try_from_owned_info_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.unchecked_account.UncheckedAccount
