/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.HashSingle

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaSha256Hasher.zero_initialized

open Solanalib.Contracts.Model Solanalib.Specs.Core

def hashv_contract : Family := Hash.Initialized.family
def hashv_run : FamilyRun hashv_contract := Hash.Initialized.reference
def hashv_sample : hashv_contract.Index := Hash.Initialized.sample

theorem hashv_reference : FamilyReference hashv_contract hashv_run :=
  Hash.Initialized.reference_correct

theorem hashv_hasExecution :
    FamilyHasExecution hashv_contract hashv_run hashv_sample :=
  Hash.Initialized.sample_hasExecution

theorem hashv_satisfiable : FamilySatisfiable hashv_contract hashv_sample :=
  hashv_hasExecution.satisfiable

def hash_contract : Family := Hash.Single.initialized
def hash_run : FamilyRun hash_contract := Hash.Single.initializedRun
def hash_sample : hash_contract.Index := Hash.Initialized.sample

theorem hash_reference : FamilyReference hash_contract hash_run :=
  Hash.Single.initialized_reference

theorem hash_hasExecution :
    FamilyHasExecution hash_contract hash_run hash_sample :=
  Hash.Single.initialized_hasExecution

theorem hash_satisfiable : FamilySatisfiable hash_contract hash_sample :=
  hash_hasExecution.satisfiable

end Solanalib.Specs.SolanaSha256Hasher.zero_initialized
