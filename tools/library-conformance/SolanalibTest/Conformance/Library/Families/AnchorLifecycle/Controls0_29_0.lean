/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.AdmissionControls
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Version0_29_0

set_option autoImplicit false

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Runtime AdmissionControls

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem account_try_accounts_admission :
    ¬ (accounts.account.Account.try_accounts_contract.contract
      ⟨payloadAccountsTypes .boxed script info, rfl⟩).requires (illTyped, accounts) accountsArgs :=
      by
  exact rejects (family :=
    accounts.account.Account.try_accounts_contract)
    accounts.account.Account.try_accounts_contract.contract rfl
    ⟨payloadAccountsTypes .boxed script info, rfl⟩ (illTyped, accounts) accountsArgs _
      (Ready.payloadReadyB_iff .account .borrowed .boxed script info true illTyped args) (by decide)

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem account_close_admission :
    ¬ (accounts.account.Account.close_contract.contract ⟨closeTypes
      .boxed, rfl⟩).requires illTyped closeArgs := by
  exact rejects (family := accounts.account.Account.close_contract)
    accounts.account.Account.close_contract.contract rfl
    ⟨closeTypes .boxed, rfl⟩ illTyped closeArgs _ (Ready.closeReadyB_iff true .legacy .boxed
      illTyped closeArgs) (by decide)

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem account_exit_admission :
    ¬ (accounts.account.Account.exit_cloned_info_contract.contract
      ⟨exitTypes .boxed script info, rfl⟩).requires illTyped (exitArgs .account) := by
  exact rejects (family :=
    accounts.account.Account.exit_cloned_info_contract)
    accounts.account.Account.exit_cloned_info_contract.contract rfl
    ⟨exitTypes .boxed script info, rfl⟩ illTyped (exitArgs .account) _ (Ready.exitReadyB_iff
      .account true .boxed script info illTyped (exitArgs .account)) (by decide)

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem interface_account_try_accounts_admission :
    ¬ (accounts.interface_account.InterfaceAccount.try_accounts_contract.contract
      ⟨payloadAccountsTypes .boxed script info, rfl⟩).requires (illTyped, accounts) accountsArgs :=
      by
  exact rejects (family :=
    accounts.interface_account.InterfaceAccount.try_accounts_contract)
    accounts.interface_account.InterfaceAccount.try_accounts_contract.contract
    rfl
    ⟨payloadAccountsTypes .boxed script info, rfl⟩ (illTyped, accounts) accountsArgs _
      (Ready.payloadReadyB_iff .interfaceAccount .borrowed .boxed script info true illTyped args)
      (by decide)

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem interface_account_exit_admission :
    ¬ (accounts.interface_account.InterfaceAccount.exit_cloned_info_contract.contract ⟨exitTypes
      .boxed script info, rfl⟩).requires illTyped (exitArgs .interfaceAccount) := by
  exact rejects (family :=
    accounts.interface_account.InterfaceAccount.exit_cloned_info_contract)
      accounts.interface_account.InterfaceAccount.exit_cloned_info_contract.contract rfl
    ⟨exitTypes .boxed script info, rfl⟩ illTyped (exitArgs .interfaceAccount) _
      (Ready.exitReadyB_iff .interfaceAccount true .boxed script info illTyped (exitArgs
      .interfaceAccount)) (by decide)

/-- The exact registered precondition holds for every input at the selected
callback interpretation, through the checker admission decision. -/
theorem program_try_accounts_admission (script : Script) (target : AccountInfo.Value)
    (before : W × AccountsState Nat) (arguments : AccountsArgs) :
    (accounts.program.Program.try_accounts_contract.contract
      ⟨validationAccountsTypes .boxed script target true, by rfl⟩).requires before arguments := by
  exact admits (family :=
    accounts.program.Program.try_accounts_contract)
    accounts.program.Program.try_accounts_contract.contract rfl
    ⟨validationAccountsTypes .boxed script target true, by rfl⟩ before arguments true (by
    change true = true ↔ (match before.2.remaining with
      | [] => True
      | reference :: _ => ValidationReady .program (validationTypes .boxed script target true)
          before.1 ⟨arguments.profile, reference⟩)
    cases remaining : before.2.remaining with
    | nil => exact iff_of_true rfl trivial
    | cons reference tail =>
      exact iff_of_true rfl ((Ready.validationReadyB_iff .program .boxed script target true
        before.1 ⟨arguments.profile, reference⟩).mp
          (Ready.validationReadyB_always .program .boxed script target before.1 ⟨arguments.profile,
            reference⟩))) rfl

/-- The exact registered precondition holds for every input at the selected
callback interpretation, through the checker admission decision. -/
theorem program_try_from_admission (script : Script) (target : AccountInfo.Value)
    (before : W) (arguments : ReferenceArgs) :
    (accounts.program.Program.try_from_contract.contract
      ⟨validationTypes .boxed script target true, by rfl⟩).requires before arguments := by
  exact admits (family := accounts.program.Program.try_from_contract)
    accounts.program.Program.try_from_contract.contract rfl
    ⟨validationTypes .boxed script target true, by rfl⟩ before arguments true (by
    exact iff_of_true rfl ((Ready.validationReadyB_iff .program .boxed script target true before
      arguments).mp
      (Ready.validationReadyB_always .program .boxed script target before arguments))) rfl

/-- The exact registered precondition holds for every input at the selected
callback interpretation, through the checker admission decision. -/
theorem signer_try_accounts_admission (script : Script) (target : AccountInfo.Value)
    (before : W × AccountsState Nat) (arguments : AccountsArgs) :
    (accounts.signer.Signer.try_accounts_contract.contract
      ⟨validationAccountsTypes .boxed script target true, by rfl⟩).requires before arguments := by
  exact admits (family := accounts.signer.Signer.try_accounts_contract)
    accounts.signer.Signer.try_accounts_contract.contract rfl
    ⟨validationAccountsTypes .boxed script target true, by rfl⟩ before arguments true (by
    change true = true ↔ (match before.2.remaining with | [] => True | _ :: _ => True)
    cases before.2.remaining <;> exact iff_of_true rfl trivial) rfl

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem account_try_from_unchecked_admission :
    ¬ (accounts.account.Account.try_from_unchecked_contract.contract
      ⟨payloadTypes .boxed script info false, rfl⟩).requires illTyped args := by
  exact rejects (family :=
    accounts.account.Account.try_from_unchecked_contract)
    accounts.account.Account.try_from_unchecked_contract.contract rfl
    ⟨payloadTypes .boxed script info false, rfl⟩ illTyped args _ (Ready.payloadReadyB_iff .account
      .borrowed .boxed script info false illTyped args) (by decide)

/-- The exact registered precondition holds for every input at the selected
callback interpretation, through the checker admission decision. -/
theorem account_info_try_accounts_admission (script : Script) (target : AccountInfo.Value)
    (before : W × AccountsState Nat) (arguments : AccountsArgs) :
    (accounts.account_info.AccountInfo.try_accounts_contract.contract
      ⟨validationAccountsTypes .boxed script target true, by rfl⟩).requires before arguments := by
  exact admits (family :=
    accounts.account_info.AccountInfo.try_accounts_contract)
    accounts.account_info.AccountInfo.try_accounts_contract.contract rfl
    ⟨validationAccountsTypes .boxed script target true, by rfl⟩ before arguments true (by
    change true = true ↔ (match before.2.remaining with | [] => True | _ :: _ => True)
    cases before.2.remaining <;> exact iff_of_true rfl trivial) rfl

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem boxed_close_admission :
    ¬ (accounts.boxed.Box.close_contract.contract (dispatchTypes .boxed
      (innerCloseFn .boxed script info))).requires illTyped ((0 : Nat), info) := by
  exact rejects (family := accounts.boxed.Box.close_contract)
    accounts.boxed.Box.close_contract.contract rfl
    (dispatchTypes .boxed (innerCloseFn .boxed script info)) illTyped ((0 : Nat), info) _
      Option.isSome_iff_exists (by decide)

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem boxed_exit_admission :
    ¬ (accounts.boxed.Box.exit_contract.contract (dispatchTypes .boxed
      (innerExitFn .boxed script info))).requires illTyped ((0 : Nat),
      Solanalib.Runtime.Pubkey.zero) := by
  exact rejects (family := accounts.boxed.Box.exit_contract)
    accounts.boxed.Box.exit_contract.contract rfl
    (dispatchTypes .boxed (innerExitFn .boxed script info)) illTyped ((0 : Nat),
      Solanalib.Runtime.Pubkey.zero) _ Option.isSome_iff_exists (by decide)

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0
