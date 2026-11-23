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

namespace Solanalib.Specs.SolanaSha256Hasher

open Solanalib.Contracts.Model Solanalib.Specs.Core

def hash_contract : Family := Hash.Single.uninitialized
def hash_run : FamilyRun hash_contract := Hash.Single.uninitializedRun
def hash_sample : hash_contract.Index := Hash.Syscall.sample

theorem hash_reference : FamilyReference hash_contract hash_run :=
  Hash.Single.uninitialized_reference

theorem hash_hasExecution :
    FamilyHasExecution hash_contract hash_run hash_sample :=
  Hash.Single.uninitialized_hasExecution

theorem hash_satisfiable : FamilySatisfiable hash_contract hash_sample :=
  hash_hasExecution.satisfiable

end Solanalib.Specs.SolanaSha256Hasher
