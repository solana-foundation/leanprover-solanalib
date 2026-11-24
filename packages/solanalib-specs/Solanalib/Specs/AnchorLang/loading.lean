/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLoading
public import Solanalib.Specs.Core.AnchorOwnedSamples

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount

def load_observation_contract := loadFamily .shared
def load_observation_run := loadRun .shared
def load_observation_sample := loadSample
theorem load_observation_reference : FamilyReference load_observation_contract load_observation_run
  :=
  Solanalib.Specs.Core.AnchorAccount.load_reference .shared
theorem load_observation_has_execution : FamilyHasExecution load_observation_contract
  load_observation_run load_observation_sample :=
  load_execution .shared
theorem load_observation_satisfiable : FamilySatisfiable load_observation_contract
  load_observation_sample :=
  load_observation_has_execution.satisfiable

def load_mut_observation_contract := loadFamily .exclusive
def load_mut_observation_run := loadRun .exclusive
def load_mut_observation_sample := loadSample
theorem load_mut_observation_reference : FamilyReference load_mut_observation_contract
  load_mut_observation_run :=
  Solanalib.Specs.Core.AnchorAccount.load_reference .exclusive
theorem load_mut_observation_has_execution : FamilyHasExecution load_mut_observation_contract
  load_mut_observation_run load_mut_observation_sample :=
  load_execution .exclusive
theorem load_mut_observation_satisfiable : FamilySatisfiable load_mut_observation_contract
  load_mut_observation_sample :=
  load_mut_observation_has_execution.satisfiable

def load_contract := AnchorLoadingOwned.family .shared
def load_run := AnchorLoadingOwned.reference .shared
def load_sample := AnchorOwnedSamples.loading
theorem load_reference : FamilyReference load_contract load_run :=
  AnchorLoadingOwned.reference_holds .shared
theorem load_has_execution : FamilyHasExecution load_contract load_run load_sample :=
  AnchorOwnedSamples.loading_execution .shared
theorem load_satisfiable : FamilySatisfiable load_contract load_sample :=
  load_has_execution.satisfiable

def load_mut_contract := AnchorLoadingOwned.family .exclusive
def load_mut_run := AnchorLoadingOwned.reference .exclusive
def load_mut_sample := AnchorOwnedSamples.loading
theorem load_mut_reference : FamilyReference load_mut_contract load_mut_run :=
  AnchorLoadingOwned.reference_holds .exclusive
theorem load_mut_has_execution : FamilyHasExecution load_mut_contract load_mut_run load_mut_sample
  :=
  AnchorOwnedSamples.loading_execution .exclusive
theorem load_mut_satisfiable : FamilySatisfiable load_mut_contract load_mut_sample :=
  load_mut_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader
