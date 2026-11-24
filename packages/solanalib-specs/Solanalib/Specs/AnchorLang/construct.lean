/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorConstruct
public import Solanalib.Specs.Core.AnchorToInfo
public import Solanalib.Specs.Core.AnchorOwnedSamples

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount

namespace accounts.account.Account

def try_from_observation_contract := constructorFamily .account
def try_from_observation_run := constructorRun .account
def try_from_observation_sample := constructorSample
theorem try_from_observation_reference : FamilyReference try_from_observation_contract
  try_from_observation_run :=
  constructor_reference .account
theorem try_from_observation_has_execution :
    FamilyHasExecution try_from_observation_contract try_from_observation_run
      try_from_observation_sample := constructor_execution .account
theorem try_from_observation_satisfiable : FamilySatisfiable try_from_observation_contract
  try_from_observation_sample :=
  try_from_observation_has_execution.satisfiable

def try_from_contract := AnchorConstructOwned.family .account
def try_from_run := AnchorConstructOwned.reference .account
def try_from_sample := AnchorOwnedSamples.constructor
theorem try_from_reference : FamilyReference try_from_contract try_from_run :=
  AnchorConstructOwned.reference_holds .account
theorem try_from_has_execution :
    FamilyHasExecution try_from_contract try_from_run try_from_sample :=
  AnchorOwnedSamples.constructor_execution .account
theorem try_from_satisfiable : FamilySatisfiable try_from_contract try_from_sample :=
  try_from_has_execution.satisfiable

end accounts.account.Account

namespace accounts.interface_account.InterfaceAccount

def try_from_observation_contract := constructorFamily .interfaceAccount
def try_from_observation_run := constructorRun .interfaceAccount
def try_from_observation_sample := constructorSample
theorem try_from_observation_reference : FamilyReference try_from_observation_contract
  try_from_observation_run :=
  constructor_reference .interfaceAccount
theorem try_from_observation_has_execution :
    FamilyHasExecution try_from_observation_contract try_from_observation_run
      try_from_observation_sample :=
  constructor_execution .interfaceAccount
theorem try_from_observation_satisfiable : FamilySatisfiable try_from_observation_contract
  try_from_observation_sample :=
  try_from_observation_has_execution.satisfiable

def try_from_contract := AnchorConstructOwned.family .interfaceAccount
def try_from_run := AnchorConstructOwned.reference .interfaceAccount
def try_from_sample := AnchorOwnedSamples.constructor
theorem try_from_reference : FamilyReference try_from_contract try_from_run :=
  AnchorConstructOwned.reference_holds .interfaceAccount
theorem try_from_has_execution :
    FamilyHasExecution try_from_contract try_from_run try_from_sample :=
  AnchorOwnedSamples.constructor_execution .interfaceAccount
theorem try_from_satisfiable : FamilySatisfiable try_from_contract try_from_sample :=
  try_from_has_execution.satisfiable

end accounts.interface_account.InterfaceAccount

namespace accounts.account_loader.AccountLoader

def try_from_observation_contract := constructorFamily .loader
def try_from_observation_run := constructorRun .loader
def try_from_observation_sample := constructorSample
theorem try_from_observation_reference : FamilyReference try_from_observation_contract
  try_from_observation_run :=
  constructor_reference .loader
theorem try_from_observation_has_execution :
    FamilyHasExecution try_from_observation_contract try_from_observation_run
      try_from_observation_sample := constructor_execution .loader
theorem try_from_observation_satisfiable : FamilySatisfiable try_from_observation_contract
  try_from_observation_sample :=
  try_from_observation_has_execution.satisfiable

def try_from_contract := AnchorConstructOwned.family .loader
def try_from_run := AnchorConstructOwned.reference .loader
def try_from_sample := AnchorOwnedSamples.constructor
theorem try_from_reference : FamilyReference try_from_contract try_from_run :=
  AnchorConstructOwned.reference_holds .loader
theorem try_from_has_execution :
    FamilyHasExecution try_from_contract try_from_run try_from_sample :=
  AnchorOwnedSamples.constructor_execution .loader
theorem try_from_satisfiable : FamilySatisfiable try_from_contract try_from_sample :=
  try_from_has_execution.satisfiable

end accounts.account_loader.AccountLoader

namespace ToAccountInfo

def to_account_info_observation_contract := toInfoFamily
def to_account_info_observation_run := toInfoRun
def to_account_info_observation_sample := toInfoSample
theorem to_account_info_observation_reference :
    FamilyReference to_account_info_observation_contract to_account_info_observation_run :=
  toInfo_reference
theorem to_account_info_observation_has_execution : FamilyHasExecution
    to_account_info_observation_contract to_account_info_observation_run
    to_account_info_observation_sample := toInfo_execution
theorem to_account_info_observation_satisfiable : FamilySatisfiable
    to_account_info_observation_contract to_account_info_observation_sample :=
  to_account_info_observation_has_execution.satisfiable

def to_account_info_contract := AnchorToInfo.family
def to_account_info_run := AnchorToInfo.reference
def to_account_info_sample := AnchorToInfo.sample
theorem to_account_info_reference :
    FamilyReference to_account_info_contract to_account_info_run := AnchorToInfo.reference_holds
theorem to_account_info_has_execution :
    FamilyHasExecution to_account_info_contract to_account_info_run to_account_info_sample :=
  AnchorToInfo.reference_execution
theorem to_account_info_satisfiable :
    FamilySatisfiable to_account_info_contract to_account_info_sample :=
  to_account_info_has_execution.satisfiable

end ToAccountInfo

end Solanalib.Specs.AnchorLang
