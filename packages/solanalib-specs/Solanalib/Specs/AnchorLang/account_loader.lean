/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLoaderConstruct
public import Solanalib.Specs.Core.AnchorLoaderInitOwned
public import Solanalib.Specs.Core.AnchorLoaderExit
public import Solanalib.Specs.Core.AnchorLoaderClose

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! The shared AccountLoader families have reviewed mathematical profiles for
anchor-lang 0.32.1, 1.0.2 and 1.1.2. Each profile retains its source, dependency
and representation conditions in `Capabilities.catalog`. Source adapters use
the exact selected release and build; `clone` and `close` have 1.0.2 source
registrations. The partial `load_init_observation` family has no source-call
registration and remains separate from the owned-error contract. -/

namespace Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader

open Solanalib.Contracts.Model Solanalib.Specs.Core

def as_ref_contract := AnchorLoader.asRefFamily
def as_ref_run := AnchorLoader.asRefReference
def as_ref_sample := AnchorLoader.identitySample
theorem as_ref_reference : FamilyReference as_ref_contract as_ref_run :=
  AnchorLoader.asRef_reference
theorem as_ref_has_execution : FamilyHasExecution as_ref_contract as_ref_run as_ref_sample :=
  AnchorLoader.asRef_execution
theorem as_ref_satisfiable : FamilySatisfiable as_ref_contract as_ref_sample :=
  as_ref_has_execution.satisfiable

def try_from_unchecked_contract := AnchorLoader.uncheckedFamily
def try_from_unchecked_run := AnchorLoader.uncheckedReference
def try_from_unchecked_sample := AnchorLoader.constructorSample
theorem try_from_unchecked_reference : FamilyReference try_from_unchecked_contract
  try_from_unchecked_run :=
  AnchorLoader.unchecked_reference
theorem try_from_unchecked_has_execution : FamilyHasExecution try_from_unchecked_contract
  try_from_unchecked_run try_from_unchecked_sample :=
  AnchorLoader.unchecked_execution
theorem try_from_unchecked_satisfiable : FamilySatisfiable try_from_unchecked_contract
  try_from_unchecked_sample :=
  try_from_unchecked_has_execution.satisfiable

def try_accounts_contract := AnchorLoader.accountsFamily
def try_accounts_run := AnchorLoader.accountsReference
def try_accounts_sample := AnchorLoader.accountsSample
theorem try_accounts_reference : FamilyReference try_accounts_contract try_accounts_run :=
  AnchorLoader.accounts_reference
theorem try_accounts_has_execution : FamilyHasExecution try_accounts_contract try_accounts_run
  try_accounts_sample :=
  AnchorLoader.accounts_execution
theorem try_accounts_satisfiable : FamilySatisfiable try_accounts_contract try_accounts_sample :=
  try_accounts_has_execution.satisfiable

def load_init_contract := AnchorLoaderInitOwned.family
def load_init_run := AnchorLoaderInitOwned.reference
def load_init_sample := AnchorLoaderInitOwned.sample
theorem load_init_reference : FamilyReference load_init_contract load_init_run :=
  AnchorLoaderInitOwned.reference_holds
theorem load_init_has_execution : FamilyHasExecution load_init_contract load_init_run
  load_init_sample :=
  AnchorLoaderInitOwned.has_execution
theorem load_init_satisfiable : FamilySatisfiable load_init_contract load_init_sample :=
  load_init_has_execution.satisfiable

def load_init_observation_contract := AnchorLoaderInit.family
def load_init_observation_run := AnchorLoaderInit.reference
def load_init_observation_sample := AnchorLoaderInit.sample
theorem load_init_observation_reference : FamilyReference load_init_observation_contract
  load_init_observation_run :=
  AnchorLoaderInit.reference_holds
theorem load_init_observation_has_execution : FamilyHasExecution load_init_observation_contract
  load_init_observation_run load_init_observation_sample :=
  AnchorLoaderInit.has_execution
theorem load_init_observation_satisfiable : FamilySatisfiable load_init_observation_contract
  load_init_observation_sample :=
  load_init_observation_has_execution.satisfiable

def exit_contract := AnchorLoaderExit.family
def exit_run := AnchorLoaderExit.reference
def exit_sample := AnchorLoaderExit.sample
theorem exit_reference : FamilyReference exit_contract exit_run :=
  AnchorLoaderExit.reference_holds
theorem exit_has_execution : FamilyHasExecution exit_contract exit_run exit_sample :=
  AnchorLoaderExit.has_execution
theorem exit_satisfiable : FamilySatisfiable exit_contract exit_sample :=
  exit_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader

open Solanalib.Contracts.Model Solanalib.Specs.Core

def clone_contract := AnchorLoader.cloneFamily
def clone_run := AnchorLoader.cloneReference
def clone_sample := AnchorLoader.identitySample
theorem clone_reference : FamilyReference clone_contract clone_run :=
  AnchorLoader.clone_reference
theorem clone_has_execution : FamilyHasExecution clone_contract clone_run clone_sample :=
  AnchorLoader.clone_execution
theorem clone_satisfiable : FamilySatisfiable clone_contract clone_sample :=
  clone_has_execution.satisfiable

def close_contract := AnchorLoaderClose.family
def close_run := AnchorLoaderClose.reference
def close_sample := AnchorLoaderClose.sample
theorem close_reference : FamilyReference close_contract close_run :=
  AnchorLoaderClose.reference_holds
theorem close_has_execution : FamilyHasExecution close_contract close_run close_sample :=
  AnchorLoaderClose.has_execution
theorem close_satisfiable : FamilySatisfiable close_contract close_sample :=
  close_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader
