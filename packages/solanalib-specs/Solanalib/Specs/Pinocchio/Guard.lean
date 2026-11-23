/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.PinocchioGuard

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Pinocchio.account_info

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace Ref
def deref_contract := PinocchioAccount.derefFamily false
def deref_run := PinocchioAccount.derefRun false
def deref_sample := PinocchioAccount.guardSample
theorem deref_reference : FamilyReference deref_contract deref_run :=
  PinocchioAccount.deref_reference false
theorem deref_hasExecution : FamilyHasExecution deref_contract deref_run deref_sample :=
  PinocchioAccount.deref_hasExecution false
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  deref_hasExecution.satisfiable

end Ref

namespace RefMut
def deref_contract := PinocchioAccount.derefFamily false
def deref_run := PinocchioAccount.derefRun false
def deref_sample := PinocchioAccount.guardSample
theorem deref_reference : FamilyReference deref_contract deref_run :=
  PinocchioAccount.deref_reference false
theorem deref_hasExecution : FamilyHasExecution deref_contract deref_run deref_sample :=
  PinocchioAccount.deref_hasExecution false
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  deref_hasExecution.satisfiable

def deref_mut_contract := PinocchioAccount.derefFamily true
def deref_mut_run := PinocchioAccount.derefRun true
def deref_mut_sample := PinocchioAccount.guardSample
theorem deref_mut_reference : FamilyReference deref_mut_contract deref_mut_run :=
  PinocchioAccount.deref_reference true
theorem deref_mut_hasExecution : FamilyHasExecution deref_mut_contract deref_mut_run
  deref_mut_sample := PinocchioAccount.deref_hasExecution true
theorem deref_mut_satisfiable : FamilySatisfiable deref_mut_contract deref_mut_sample :=
  deref_mut_hasExecution.satisfiable

def map_contract := PinocchioAccount.mapFamily
def map_run := PinocchioAccount.mapRun
def map_sample := PinocchioAccount.mapSample
theorem map_reference : FamilyReference map_contract map_run := PinocchioAccount.map_reference
theorem map_hasExecution : FamilyHasExecution map_contract map_run map_sample :=
  PinocchioAccount.map_hasExecution
theorem map_satisfiable : FamilySatisfiable map_contract map_sample := map_hasExecution.satisfiable
end RefMut

end Solanalib.Specs.Pinocchio.account_info
