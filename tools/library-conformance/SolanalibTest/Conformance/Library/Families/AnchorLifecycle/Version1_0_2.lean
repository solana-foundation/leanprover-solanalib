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

def Version1_0_2.checkers : List Checker := [
  validationAccountsCheck .interface .borrowed .boxed false "interface"
    accounts.interface.Interface.try_accounts_run rfl
    accounts.interface.Interface.try_accounts_contract.contract rfl
    "<anchor_lang::accounts::interface::Interface<'info, T> as \
      anchor_lang::Accounts<'info, B>>::try_accounts"
    [("B", "u64"), ("T", "conformance_anchor_lifecycle::script::ProgramTag")]
      "Solanalib.Specs.AnchorLang.accounts.interface.Interface.try_accounts_run",
  payloadAccountsCheck .interfaceAccount .borrowed .boxed false "interface_account"
    accounts.interface_account.InterfaceAccount.try_accounts_run rfl
    accounts.interface_account.InterfaceAccount.try_accounts_contract.contract
      rfl
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
      anchor_lang::Accounts<'info, B>>::try_accounts"
    [("B", "u64"), ("T", "conformance_anchor_lifecycle::script::Payload")]
      "Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.try_accounts_\
        run",
  exitCheck .interfaceAccount false .boxed false false "interface_account"
    accounts.interface_account.InterfaceAccount.exit_run rfl
    accounts.interface_account.InterfaceAccount.exit_contract.contract
      rfl
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
      anchor_lang::AccountsExit<'info>>::exit"
    [("T", "conformance_anchor_lifecycle::script::ExitPayload")]
      "Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.exit_run",
  validationAccountsCheck .program .borrowed .boxed false "program"
    accounts.program.Program.try_accounts_run rfl
    accounts.program.Program.try_accounts_contract.contract rfl
    "<anchor_lang::accounts::program::Program<'info, T> as anchor_lang::Accounts<'info, \
      B>>::try_accounts"
    [("B", "u64"), ("T", "conformance_anchor_lifecycle::script::ProgramTag")]
      "Solanalib.Specs.AnchorLang.accounts.program.Program.try_accounts_run",
  validationAccountsCheck .signer .borrowed .boxed false "signer"
    accounts.signer.Signer.try_accounts_run rfl
    accounts.signer.Signer.try_accounts_contract.contract rfl
    "<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Accounts<'info, \
      B>>::try_accounts"
    [("B", "u64")] "Solanalib.Specs.AnchorLang.accounts.signer.Signer.try_accounts_run",
  validationAccountsCheck .system .borrowed .boxed false "system_account"
    accounts.system_account.SystemAccount.try_accounts_run rfl
    accounts.system_account.SystemAccount.try_accounts_contract.contract
      rfl
    "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
      anchor_lang::Accounts<'info, B>>::try_accounts"
    [("B", "u64")]
      "Solanalib.Specs.AnchorLang.accounts.system_account.SystemAccount.try_accounts_run",
  validationAccountsCheck .sysvar .borrowed .boxed false "sysvar"
    accounts.sysvar.Sysvar.try_accounts_run rfl
    accounts.sysvar.Sysvar.try_accounts_contract.contract rfl
    "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as anchor_lang::Accounts<'info, \
      B>>::try_accounts"
    [("B", "u64"), ("T", "conformance_anchor_lifecycle::script::Var")]
      "Solanalib.Specs.AnchorLang.accounts.sysvar.Sysvar.try_accounts_run",
  validationAccountsCheck .unchecked .borrowed .boxed false "unchecked_account"
    accounts.unchecked_account.UncheckedAccount.try_accounts_run rfl
    accounts.unchecked_account.UncheckedAccount.try_accounts_contract.contract
      rfl
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
      anchor_lang::Accounts<'info, B>>::try_accounts"
    [("B", "u64")]
      "Solanalib.Specs.AnchorLang.accounts.unchecked_account.UncheckedAccount.try_accounts_\
        run",
  defaultExitCheck .boxed false false
    AccountsExit.exit_run rfl
    AccountsExit.exit_contract.contract rfl
    "anchor_lang::AccountsExit::exit"
    [("Self", "conformance_anchor_lifecycle::script::DefaultExit")]
      "Solanalib.Specs.AnchorLang.AccountsExit.exit_run",
  boxAccountsCheck .boxed false false
    accounts.boxed.Box.try_accounts_run rfl
    accounts.boxed.Box.try_accounts_contract.contract rfl
    "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'info, B> for \
      alloc::boxed::Box<T>>::try_accounts"
    [("B", "u64"), ("T", "conformance_anchor_lifecycle::script::Inner")]
      "Solanalib.Specs.AnchorLang.accounts.boxed.Box.try_accounts_run",
  boxExitCheck .boxed false false
    accounts.boxed.Box.exit_run rfl
    accounts.boxed.Box.exit_contract.contract rfl
    "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'info> for \
      alloc::boxed::Box<T>>::exit"
    [("T", "conformance_anchor_lifecycle::script::Inner")]
      "Solanalib.Specs.AnchorLang.accounts.boxed.Box.exit_run",
  payloadCheck .interfaceAccount .borrowed .boxed false false "interface_account"
    "try_from_unchecked"
    accounts.interface_account.InterfaceAccount.try_from_unchecked_run
      rfl
    accounts.interface_account.InterfaceAccount.try_from_unchecked_contract.contract
      rfl
    "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, \
      T>::try_from_unchecked"
    [("T", "conformance_anchor_lifecycle::script::Payload")]
      "Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.try_from_unch\
        ecked_run",
  optionAccountsCheck .boxed false false
    accounts.option.Option.try_accounts_run rfl
    accounts.option.Option.try_accounts_contract.contract rfl
    "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'info, B> for \
      core::option::Option<T>>::try_accounts"
    [("B", "u64"), ("T", "conformance_anchor_lifecycle::script::Inner")]
      "Solanalib.Specs.AnchorLang.accounts.option.Option.try_accounts_run",
  optionExitCheck .boxed false false
    accounts.option.Option.exit_run rfl
    accounts.option.Option.exit_contract.contract rfl
    "anchor_lang::accounts::option::<impl anchor_lang::AccountsExit<'info> for \
      core::option::Option<T>>::exit"
    [("T", "conformance_anchor_lifecycle::script::Inner")]
      "Solanalib.Specs.AnchorLang.accounts.option.Option.exit_run",
  uncheckedCheck .borrowed false
    accounts.unchecked_account.UncheckedAccount.try_from_run rfl
    accounts.unchecked_account.UncheckedAccount.try_from_contract.contract
      rfl
    "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'info>::try_from"
    [] "Solanalib.Specs.AnchorLang.accounts.unchecked_account.UncheckedAccount.try_from_run"]

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
