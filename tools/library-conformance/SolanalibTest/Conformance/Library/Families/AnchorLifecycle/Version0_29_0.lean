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

def Version0_29_0.checkers : List Checker := [
  payloadAccountsCheck .account .borrowed .boxed true "account"
    accounts.account.Account.try_accounts_run rfl
    accounts.account.Account.try_accounts_contract.contract rfl
    "<anchor_lang::accounts::account::Account<'info, T> as anchor_lang::Accounts<'info, \
      B>>::try_accounts"
    [("B", "u64"), ("T", "conformance_anchor_lifecycle::script::Payload")]
      "Solanalib.Specs.AnchorLang.accounts.account.Account.try_accounts_run",
  closeCheck true .legacy .boxed true false "account"
    accounts.account.Account.close_run rfl
    accounts.account.Account.close_contract.contract rfl
    "<anchor_lang::accounts::account::Account<'info, T> as \
      anchor_lang::AccountsClose<'info>>::close"
    [("T", "conformance_anchor_lifecycle::script::Payload")]
      "Solanalib.Specs.AnchorLang.accounts.account.Account.close_run",
  exitCheck .account true .boxed true false "account"
    accounts.account.Account.exit_cloned_info_run rfl
    accounts.account.Account.exit_cloned_info_contract.contract rfl
    "<anchor_lang::accounts::account::Account<'info, T> as \
      anchor_lang::AccountsExit<'info>>::exit"
    [("T", "conformance_anchor_lifecycle::script::ExitPayload")]
      "Solanalib.Specs.AnchorLang.accounts.account.Account.exit_cloned_info_run",
  payloadAccountsCheck .interfaceAccount .borrowed .boxed true "interface_account"
    accounts.interface_account.InterfaceAccount.try_accounts_run rfl
    accounts.interface_account.InterfaceAccount.try_accounts_contract.contract
      rfl
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
      anchor_lang::Accounts<'info, B>>::try_accounts"
    [("B", "u64"), ("T", "conformance_anchor_lifecycle::script::Payload")]
      "Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.try_accounts_\
        run",
  exitCheck .interfaceAccount true .boxed true false "interface_account"
    accounts.interface_account.InterfaceAccount.exit_cloned_info_run rfl
    accounts.interface_account.InterfaceAccount.exit_cloned_info_contract.contract
      rfl
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
      anchor_lang::AccountsExit<'info>>::exit"
    [("T", "conformance_anchor_lifecycle::script::ExitPayload")]
      "Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.exit_cloned_i\
        nfo_run",
  validationAccountsCheck .program .borrowed .boxed true "program"
    accounts.program.Program.try_accounts_run rfl
    accounts.program.Program.try_accounts_contract.contract rfl
    "<anchor_lang::accounts::program::Program<'info, T> as anchor_lang::Accounts<'info, \
      B>>::try_accounts"
    [("B", "u64"), ("T", "conformance_anchor_lifecycle::script::ProgramTag")]
      "Solanalib.Specs.AnchorLang.accounts.program.Program.try_accounts_run",
  validationCheck .program .borrowed .boxed true "program"
    accounts.program.Program.try_from_run rfl
    accounts.program.Program.try_from_contract.contract rfl
    "<anchor_lang::accounts::program::Program<'a, T> as core::convert::TryFrom<&'a \
      solana_program::account_info::AccountInfo<'a>>>::try_from"
    [("T", "conformance_anchor_lifecycle::script::ProgramTag")]
      "Solanalib.Specs.AnchorLang.accounts.program.Program.try_from_run",
  validationAccountsCheck .signer .borrowed .boxed true "signer"
    accounts.signer.Signer.try_accounts_run rfl
    accounts.signer.Signer.try_accounts_contract.contract rfl
    "<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Accounts<'info, \
      B>>::try_accounts"
    [("B", "u64")] "Solanalib.Specs.AnchorLang.accounts.signer.Signer.try_accounts_run",
  defaultExitCheck .boxed true false
    AccountsExit.exit_run rfl
    AccountsExit.exit_contract.contract rfl
    "anchor_lang::AccountsExit::exit"
    [("Self", "conformance_anchor_lifecycle::script::DefaultExit")]
      "Solanalib.Specs.AnchorLang.AccountsExit.exit_run",
  payloadCheck .account .borrowed .boxed true false "account" "try_from_unchecked"
    accounts.account.Account.try_from_unchecked_run rfl
    accounts.account.Account.try_from_unchecked_contract.contract rfl
    "anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked"
    [("T", "conformance_anchor_lifecycle::script::Payload")]
      "Solanalib.Specs.AnchorLang.accounts.account.Account.try_from_unchecked_run",
  validationAccountsCheck .accountInfo .borrowed .boxed true "account_info"
    accounts.account_info.AccountInfo.try_accounts_run rfl
    accounts.account_info.AccountInfo.try_accounts_contract.contract rfl
    "anchor_lang::accounts::account_info::<impl anchor_lang::Accounts<'info, B> for \
      solana_program::account_info::AccountInfo<'info>>::try_accounts"
    [("B", "u64")] "Solanalib.Specs.AnchorLang.accounts.account_info.AccountInfo.try_accoun\
      ts_run",
  boxAccountsCheck .boxed true false
    accounts.boxed.Box.try_accounts_run rfl
    accounts.boxed.Box.try_accounts_contract.contract rfl
    "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'info, B> for \
      alloc::boxed::Box<T>>::try_accounts"
    [("B", "u64"), ("T", "conformance_anchor_lifecycle::script::Inner")]
      "Solanalib.Specs.AnchorLang.accounts.boxed.Box.try_accounts_run",
  boxCloseCheck .boxed true false
    accounts.boxed.Box.close_run rfl
    accounts.boxed.Box.close_contract.contract rfl
    "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsClose<'info> for \
      alloc::boxed::Box<T>>::close"
    [("T", "conformance_anchor_lifecycle::script::Inner")]
      "Solanalib.Specs.AnchorLang.accounts.boxed.Box.close_run",
  boxExitCheck .boxed true false
    accounts.boxed.Box.exit_run rfl
    accounts.boxed.Box.exit_contract.contract rfl
    "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'info> for \
      alloc::boxed::Box<T>>::exit"
    [("T", "conformance_anchor_lifecycle::script::Inner")]
      "Solanalib.Specs.AnchorLang.accounts.boxed.Box.exit_run",
  optionAccountsCheck .boxed true false
    accounts.option.Option.try_accounts_run rfl
    accounts.option.Option.try_accounts_contract.contract rfl
    "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'info, B> for \
      core::option::Option<T>>::try_accounts"
    [("B", "u64"), ("T", "conformance_anchor_lifecycle::script::Inner")]
      "Solanalib.Specs.AnchorLang.accounts.option.Option.try_accounts_run",
  optionExitCheck .boxed true false
    accounts.option.Option.exit_run rfl
    accounts.option.Option.exit_contract.contract rfl
    "anchor_lang::accounts::option::<impl anchor_lang::AccountsExit<'info> for \
      core::option::Option<T>>::exit"
    [("T", "conformance_anchor_lifecycle::script::Inner")]
      "Solanalib.Specs.AnchorLang.accounts.option.Option.exit_run",
  validationCheck .signer .borrowed .boxed true "signer"
    accounts.signer.Signer.try_from_run rfl
    accounts.signer.Signer.try_from_contract.contract rfl
    "anchor_lang::accounts::signer::Signer::<'info>::try_from"
    [] "Solanalib.Specs.AnchorLang.accounts.signer.Signer.try_from_run"]

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
