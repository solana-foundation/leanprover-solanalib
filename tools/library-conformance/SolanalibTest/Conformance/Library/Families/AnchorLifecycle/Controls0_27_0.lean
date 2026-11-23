/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.AdmissionControls
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Version0_27_0

set_option autoImplicit false

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Runtime AdmissionControls

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem account_try_accounts_admission :
    ¬ (accounts.account.Account.try_accounts_inline_error_contract.contract ⟨payloadAccountsTypes
      .inline script info, rfl⟩).requires (illTyped, accounts) accountsArgs := by
  exact rejects (family :=
    accounts.account.Account.try_accounts_inline_error_contract)
    accounts.account.Account.try_accounts_inline_error_contract.contract
    rfl
    ⟨payloadAccountsTypes .inline script info, rfl⟩ (illTyped, accounts) accountsArgs _
      (Ready.payloadReadyB_iff .account .owned .inline script info true illTyped args) (by decide)

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem account_close_admission :
    ¬ (accounts.account.Account.close_inline_error_contract.contract
      ⟨closeTypes .inline, rfl⟩).requires illTyped closeArgs := by
  exact rejects (family :=
    accounts.account.Account.close_inline_error_contract)
    accounts.account.Account.close_inline_error_contract.contract rfl
    ⟨closeTypes .inline, rfl⟩ illTyped closeArgs _ (Ready.closeReadyB_iff true .legacy .inline
      illTyped closeArgs) (by decide)

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem account_exit_admission :
    ¬ (accounts.account.Account.exit_inline_error_contract.contract
      ⟨exitTypes .inline script info, rfl⟩).requires illTyped (exitArgs .account) := by
  exact rejects (family :=
    accounts.account.Account.exit_inline_error_contract)
    accounts.account.Account.exit_inline_error_contract.contract rfl
    ⟨exitTypes .inline script info, rfl⟩ illTyped (exitArgs .account) _ (Ready.exitReadyB_iff
      .account true .inline script info illTyped (exitArgs .account)) (by decide)

/-- The exact registered precondition holds for every input at the selected
callback interpretation, through the checker admission decision. -/
theorem program_try_accounts_admission (script : Script) (target : AccountInfo.Value)
    (before : W × AccountsState Nat) (arguments : AccountsArgs) :
    (accounts.program.Program.try_accounts_inline_error_contract.contract ⟨validationAccountsTypes
      .inline script target true, by rfl⟩).requires before arguments := by
  exact admits (family :=
    accounts.program.Program.try_accounts_inline_error_contract)
    accounts.program.Program.try_accounts_inline_error_contract.contract
    rfl
    ⟨validationAccountsTypes .inline script target true, by rfl⟩ before arguments true (by
    change true = true ↔ (match before.2.remaining with
      | [] => True
      | reference :: _ => ValidationReady .program (validationTypes .inline script target true)
          before.1 ⟨arguments.profile, reference⟩)
    cases remaining : before.2.remaining with
    | nil => exact iff_of_true rfl trivial
    | cons reference tail =>
      exact iff_of_true rfl ((Ready.validationReadyB_iff .program .inline script target true
        before.1 ⟨arguments.profile, reference⟩).mp
          (Ready.validationReadyB_always .program .inline script target before.1
            ⟨arguments.profile, reference⟩))) rfl

/-- The exact registered precondition holds for every input at the selected
callback interpretation, through the checker admission decision. -/
theorem signer_try_accounts_admission (script : Script) (target : AccountInfo.Value)
    (before : W × AccountsState Nat) (arguments : AccountsArgs) :
    (accounts.signer.Signer.try_accounts_inline_error_contract.contract
      ⟨validationAccountsTypes .inline script target true, by rfl⟩).requires before arguments := by
  exact admits (family :=
    accounts.signer.Signer.try_accounts_inline_error_contract)
    accounts.signer.Signer.try_accounts_inline_error_contract.contract
    rfl
    ⟨validationAccountsTypes .inline script target true, by rfl⟩ before arguments true (by
    change true = true ↔ (match before.2.remaining with | [] => True | _ :: _ => True)
    cases before.2.remaining <;> exact iff_of_true rfl trivial) rfl

/-- The exact registered precondition holds for every input at the selected
callback interpretation, through the checker admission decision. -/
theorem system_account_try_accounts_admission (script : Script) (target : AccountInfo.Value)
    (before : W × AccountsState Nat) (arguments : AccountsArgs) :
    (accounts.system_account.SystemAccount.try_accounts_inline_error_contract.contract
      ⟨validationAccountsTypes .inline script target true, by rfl⟩).requires before arguments := by
  exact admits (family :=
    accounts.system_account.SystemAccount.try_accounts_inline_error_contract)
      accounts.system_account.SystemAccount.try_accounts_inline_error_contract.contract rfl
    ⟨validationAccountsTypes .inline script target true, by rfl⟩ before arguments true (by
    change true = true ↔ (match before.2.remaining with | [] => True | _ :: _ => True)
    cases before.2.remaining <;> exact iff_of_true rfl trivial) rfl

/-- The exact registered precondition holds for every input at the selected
callback interpretation, through the checker admission decision. -/
theorem sysvar_try_accounts_admission (script : Script) (target : AccountInfo.Value)
    (before : W × AccountsState Nat) (arguments : AccountsArgs) :
    (accounts.sysvar.Sysvar.try_accounts_inline_error_contract.contract
      ⟨validationAccountsTypes .inline script target true, by rfl⟩).requires before arguments := by
  exact admits (family :=
    accounts.sysvar.Sysvar.try_accounts_inline_error_contract)
    accounts.sysvar.Sysvar.try_accounts_inline_error_contract.contract
    rfl
    ⟨validationAccountsTypes .inline script target true, by rfl⟩ before arguments true (by
    change true = true ↔ (match before.2.remaining with | [] => True | _ :: _ => True)
    cases before.2.remaining <;> exact iff_of_true rfl trivial) rfl

/-- The exact registered precondition holds for every input at the selected
callback interpretation, through the checker admission decision. -/
theorem unchecked_account_try_accounts_admission (script : Script) (target : AccountInfo.Value)
    (before : W × AccountsState Nat) (arguments : AccountsArgs) :
    (accounts.unchecked_account.UncheckedAccount.try_accounts_inline_error_contract.contract
      ⟨validationAccountsTypes .inline script target true, by rfl⟩).requires before arguments := by
  exact admits (family :=
    accounts.unchecked_account.UncheckedAccount.try_accounts_inline_error_contract)
      accounts.unchecked_account.UncheckedAccount.try_accounts_inline_error_contract.contract rfl
    ⟨validationAccountsTypes .inline script target true, by rfl⟩ before arguments true (by
    change true = true ↔ (match before.2.remaining with | [] => True | _ :: _ => True)
    cases before.2.remaining <;> exact iff_of_true rfl trivial) rfl

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem account_reload_admission :
    ¬ (accounts.account.Account.reload_inline_error_contract.contract
      ⟨reloadTypes .inline script info, rfl⟩).requires illTyped args := by
  exact rejects (family :=
    accounts.account.Account.reload_inline_error_contract)
    accounts.account.Account.reload_inline_error_contract.contract rfl
    ⟨reloadTypes .inline script info, rfl⟩ illTyped args _ (Ready.reloadReadyB_iff .legacy .inline
      script info illTyped args) (by decide)

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem account_try_from_admission :
    ¬ (accounts.account.Account.try_from_inline_error_contract.contract
      ⟨payloadTypes .inline script info true, rfl⟩).requires illTyped args := by
  exact rejects (family :=
    accounts.account.Account.try_from_inline_error_contract)
    accounts.account.Account.try_from_inline_error_contract.contract rfl
    ⟨payloadTypes .inline script info true, rfl⟩ illTyped args _ (Ready.payloadReadyB_iff .account
      .owned .inline script info true illTyped args) (by decide)

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem account_try_from_unchecked_admission :
    ¬ (accounts.account.Account.try_from_unchecked_inline_error_contract.contract ⟨payloadTypes
      .inline script info false, rfl⟩).requires illTyped args := by
  exact rejects (family :=
    accounts.account.Account.try_from_unchecked_inline_error_contract)
    accounts.account.Account.try_from_unchecked_inline_error_contract.contract
    rfl
    ⟨payloadTypes .inline script info false, rfl⟩ illTyped args _ (Ready.payloadReadyB_iff .account
      .owned .inline script info false illTyped args) (by decide)

/-- The exact registered precondition holds for every input at the selected
callback interpretation, through the checker admission decision. -/
theorem account_info_try_accounts_admission (script : Script) (target : AccountInfo.Value)
    (before : W × AccountsState Nat) (arguments : AccountsArgs) :
    (accounts.account_info.AccountInfo.try_accounts_inline_error_contract.contract
      ⟨validationAccountsTypes .inline script target true, by rfl⟩).requires before arguments := by
  exact admits (family :=
    accounts.account_info.AccountInfo.try_accounts_inline_error_contract)
      accounts.account_info.AccountInfo.try_accounts_inline_error_contract.contract rfl
    ⟨validationAccountsTypes .inline script target true, by rfl⟩ before arguments true (by
    change true = true ↔ (match before.2.remaining with | [] => True | _ :: _ => True)
    cases before.2.remaining <;> exact iff_of_true rfl trivial) rfl

/-- The exact registered precondition rejects a resource shape the native
parser cannot construct; the proof uses the admission decision of the checker. -/
theorem boxed_exit_admission :
    ¬ (accounts.boxed.Box.exit_contract.contract (dispatchTypes .inline
      (innerExitFn .inline script info))).requires illTyped ((0 : Nat),
      Solanalib.Runtime.Pubkey.zero) := by
  exact rejects (family := accounts.boxed.Box.exit_contract)
    accounts.boxed.Box.exit_contract.contract rfl
    (dispatchTypes .inline (innerExitFn .inline script info)) illTyped ((0 : Nat),
      Solanalib.Runtime.Pubkey.zero) _ Option.isSome_iff_exists (by decide)

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0
