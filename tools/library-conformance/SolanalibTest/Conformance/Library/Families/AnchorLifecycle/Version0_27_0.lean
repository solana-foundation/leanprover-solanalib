/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.CollectionChecks
import Solanalib.Specs.AnchorLang.Lifecycle

set_option autoImplicit false

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

def Version0_27_0.checkers : List Checker := [
  payloadAccountsCheck .account .owned .inline true "account"
    accounts.account.Account.try_accounts_inline_error_run rfl
    accounts.account.Account.try_accounts_inline_error_contract.contract
      rfl
    "<anchor_lang::accounts::account::Account<'info, T> as \
      anchor_lang::Accounts<'info>>::try_accounts"
    [("T", "conformance_anchor_lifecycle::script::Payload")]
      "Solanalib.Specs.AnchorLang.accounts.account.Account.try_accounts_inline_error_run",
  closeCheck true .legacy .inline true true "account"
    accounts.account.Account.close_inline_error_run rfl
    accounts.account.Account.close_inline_error_contract.contract rfl
    "<anchor_lang::accounts::account::Account<'info, T> as \
      anchor_lang::AccountsClose<'info>>::close"
    [("T", "conformance_anchor_lifecycle::script::Payload")]
      "Solanalib.Specs.AnchorLang.accounts.account.Account.close_inline_error_run",
  exitCheck .account true .inline true true "account"
    accounts.account.Account.exit_inline_error_run rfl
    accounts.account.Account.exit_inline_error_contract.contract rfl
    "<anchor_lang::accounts::account::Account<'info, T> as \
      anchor_lang::AccountsExit<'info>>::exit"
    [("T", "conformance_anchor_lifecycle::script::ExitPayload")]
      "Solanalib.Specs.AnchorLang.accounts.account.Account.exit_inline_error_run",
  validationAccountsCheck .program .owned .inline true "program"
    accounts.program.Program.try_accounts_inline_error_run rfl
    accounts.program.Program.try_accounts_inline_error_contract.contract
      rfl
    "<anchor_lang::accounts::program::Program<'info, T> as \
      anchor_lang::Accounts<'info>>::try_accounts"
    [("T", "conformance_anchor_lifecycle::script::ProgramTag")]
      "Solanalib.Specs.AnchorLang.accounts.program.Program.try_accounts_inline_error_run",
  validationAccountsCheck .signer .owned .inline true "signer"
    accounts.signer.Signer.try_accounts_inline_error_run rfl
    accounts.signer.Signer.try_accounts_inline_error_contract.contract
      rfl
    "<anchor_lang::accounts::signer::Signer<'info> as \
      anchor_lang::Accounts<'info>>::try_accounts"
    [] "Solanalib.Specs.AnchorLang.accounts.signer.Signer.try_accounts_inline_error_run",
  validationAccountsCheck .system .owned .inline true "system_account"
    accounts.system_account.SystemAccount.try_accounts_inline_error_run
      rfl
    accounts.system_account.SystemAccount.try_accounts_inline_error_contract.contract
      rfl
    "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
      anchor_lang::Accounts<'info>>::try_accounts"
    [] "Solanalib.Specs.AnchorLang.accounts.system_account.SystemAccount.try_accounts_inlin\
      e_error_run",
  validationAccountsCheck .sysvar .owned .inline true "sysvar"
    accounts.sysvar.Sysvar.try_accounts_inline_error_run rfl
    accounts.sysvar.Sysvar.try_accounts_inline_error_contract.contract
      rfl
    "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as \
      anchor_lang::Accounts<'info>>::try_accounts"
    [("T", "conformance_anchor_lifecycle::script::Var")]
      "Solanalib.Specs.AnchorLang.accounts.sysvar.Sysvar.try_accounts_inline_error_run",
  validationAccountsCheck .unchecked .owned .inline true "unchecked_account"
    accounts.unchecked_account.UncheckedAccount.try_accounts_inline_error_run
      rfl
    accounts.unchecked_account.UncheckedAccount.try_accounts_inline_error_contract.contract
      rfl
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
      anchor_lang::Accounts<'info>>::try_accounts"
    [] "Solanalib.Specs.AnchorLang.accounts.unchecked_account.UncheckedAccount.try_accounts\
      _inline_error_run",
  defaultExitCheck .inline true true
    AccountsExit.exit_run rfl
    AccountsExit.exit_contract.contract rfl
    "anchor_lang::AccountsExit::exit"
    [("Self", "conformance_anchor_lifecycle::script::DefaultExit")]
      "Solanalib.Specs.AnchorLang.AccountsExit.exit_run",
  reloadCheck .legacy .inline true true "account"
    accounts.account.Account.reload_inline_error_run rfl
    accounts.account.Account.reload_inline_error_contract.contract rfl
    "anchor_lang::accounts::account::Account::<'a, T>::reload"
    [("T", "conformance_anchor_lifecycle::script::Payload")]
      "Solanalib.Specs.AnchorLang.accounts.account.Account.reload_inline_error_run",
  payloadCheck .account .owned .inline true true "account" "try_from"
    accounts.account.Account.try_from_inline_error_run rfl
    accounts.account.Account.try_from_inline_error_contract.contract rfl
    "anchor_lang::accounts::account::Account::<'a, T>::try_from"
    [("T", "conformance_anchor_lifecycle::script::Payload")]
      "Solanalib.Specs.AnchorLang.accounts.account.Account.try_from_inline_error_run",
  payloadCheck .account .owned .inline true false "account" "try_from_unchecked"
    accounts.account.Account.try_from_unchecked_inline_error_run rfl
    accounts.account.Account.try_from_unchecked_inline_error_contract.contract
      rfl
    "anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked"
    [("T", "conformance_anchor_lifecycle::script::Payload")]
      "Solanalib.Specs.AnchorLang.accounts.account.Account.try_from_unchecked_inline_error_\
        run",
  validationAccountsCheck .accountInfo .owned .inline true "account_info"
    accounts.account_info.AccountInfo.try_accounts_inline_error_run rfl
    accounts.account_info.AccountInfo.try_accounts_inline_error_contract.contract
      rfl
    "anchor_lang::accounts::account_info::<impl anchor_lang::Accounts<'info> for \
      solana_program::account_info::AccountInfo<'info>>::try_accounts"
    [] "Solanalib.Specs.AnchorLang.accounts.account_info.AccountInfo.try_accounts_inline_er\
      ror_run",
  boxAccountsCheck .inline true true
    accounts.boxed.Box.try_accounts_inline_error_run rfl
    accounts.boxed.Box.try_accounts_inline_error_contract.contract rfl
    "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'info> for \
      alloc::boxed::Box<T>>::try_accounts"
    [("T", "conformance_anchor_lifecycle::script::Inner")]
      "Solanalib.Specs.AnchorLang.accounts.boxed.Box.try_accounts_inline_error_run",
  boxExitCheck .inline true true
    accounts.boxed.Box.exit_run rfl
    accounts.boxed.Box.exit_contract.contract rfl
    "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'info> for \
      alloc::boxed::Box<T>>::exit"
    [("T", "conformance_anchor_lifecycle::script::Inner")]
      "Solanalib.Specs.AnchorLang.accounts.boxed.Box.exit_run",
  uncheckedCheck .owned true
    accounts.unchecked_account.UncheckedAccount.try_from_owned_info_run
      rfl
    accounts.unchecked_account.UncheckedAccount.try_from_owned_info_contract.contract
      rfl
    "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'info>::try_from"
    [] "Solanalib.Specs.AnchorLang.accounts.unchecked_account.UncheckedAccount.try_from_own\
      ed_info_run"]

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
