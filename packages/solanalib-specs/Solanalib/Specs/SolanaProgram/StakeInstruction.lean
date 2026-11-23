/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.LegacyStakeInstructionWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.stake.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.LegacyStakeInstruction

def authorize_contract : Family := singleFamily AuthorizeArgs authorizePlan
def authorize_run : FamilyRun authorize_contract := singleReference AuthorizeArgs authorizePlan
def authorize_sample : authorize_contract.Index := Sample.index

theorem authorize_reference : FamilyReference authorize_contract authorize_run :=
  single_reference AuthorizeArgs authorizePlan

theorem authorize_has_execution :
    FamilyHasExecution authorize_contract authorize_run authorize_sample :=
  Sample.single_execution AuthorizeArgs authorizePlan ⟨.zero, .zero, .zero, .staker, none⟩ rfl

theorem authorize_satisfiable : FamilySatisfiable authorize_contract authorize_sample :=
  authorize_has_execution.satisfiable

def delegate_stake_contract : Family := singleFamily DelegateArgs delegatePlan
def delegate_stake_run : FamilyRun delegate_stake_contract := singleReference DelegateArgs
  delegatePlan
def delegate_stake_sample : delegate_stake_contract.Index := Sample.index

theorem delegate_stake_reference : FamilyReference delegate_stake_contract delegate_stake_run :=
  single_reference DelegateArgs delegatePlan

theorem delegate_stake_has_execution :
    FamilyHasExecution delegate_stake_contract delegate_stake_run delegate_stake_sample :=
  Sample.single_execution DelegateArgs delegatePlan ⟨.zero, .zero, .zero⟩ rfl

theorem delegate_stake_satisfiable : FamilySatisfiable delegate_stake_contract
  delegate_stake_sample :=
  delegate_stake_has_execution.satisfiable

def initialize_contract : Family := singleFamily InitializeArgs initializePlan
def initialize_run : FamilyRun initialize_contract := singleReference InitializeArgs initializePlan
def initialize_sample : initialize_contract.Index := Sample.index

theorem initialize_reference : FamilyReference initialize_contract initialize_run :=
  single_reference InitializeArgs initializePlan

theorem initialize_has_execution :
    FamilyHasExecution initialize_contract initialize_run initialize_sample :=
  Sample.single_execution InitializeArgs initializePlan ⟨.zero, ⟨.zero, .zero⟩,
    LegacyStake.defaultLockup⟩ rfl

theorem initialize_satisfiable : FamilySatisfiable initialize_contract initialize_sample :=
  initialize_has_execution.satisfiable

def merge_contract : Family := mergeFamily
def merge_run : FamilyRun merge_contract := mergeReference
def merge_sample : merge_contract.Index := Sample.index

theorem merge_reference : FamilyReference merge_contract merge_run :=
  LegacyStakeInstruction.merge_reference

theorem merge_has_execution :
    FamilyHasExecution merge_contract merge_run merge_sample :=
  Sample.merge_execution ⟨.zero, .zero, .zero⟩

theorem merge_satisfiable : FamilySatisfiable merge_contract merge_sample :=
  merge_has_execution.satisfiable

def set_lockup_contract : Family := singleFamily SetLockupArgs setLockupPlan
def set_lockup_run : FamilyRun set_lockup_contract := singleReference SetLockupArgs setLockupPlan
def set_lockup_sample : set_lockup_contract.Index := Sample.index

theorem set_lockup_reference : FamilyReference set_lockup_contract set_lockup_run :=
  single_reference SetLockupArgs setLockupPlan

theorem set_lockup_has_execution :
    FamilyHasExecution set_lockup_contract set_lockup_run set_lockup_sample :=
  Sample.single_execution SetLockupArgs setLockupPlan ⟨.zero, ⟨none, none, none⟩, .zero⟩ rfl

theorem set_lockup_satisfiable : FamilySatisfiable set_lockup_contract set_lockup_sample :=
  set_lockup_has_execution.satisfiable

def split_contract : Family := splitFamily
def split_run : FamilyRun split_contract := splitReference
def split_sample : split_contract.Index := Sample.index

theorem split_reference : FamilyReference split_contract split_run :=
  LegacyStakeInstruction.split_reference

theorem split_has_execution :
    FamilyHasExecution split_contract split_run split_sample :=
  Sample.split_execution ⟨.zero, .zero, 0, .zero⟩

theorem split_satisfiable : FamilySatisfiable split_contract split_sample :=
  split_has_execution.satisfiable

end Solanalib.Specs.SolanaProgram.stake.instruction
