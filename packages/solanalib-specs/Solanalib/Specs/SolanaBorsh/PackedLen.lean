/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorshPackedLen

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaBorsh.v0_10

open Solanalib.Contracts.Model Solanalib.Specs.Core

def get_instance_packed_len_contract : Family := BorshPackedLen.family
def get_instance_packed_len_run : FamilyRun get_instance_packed_len_contract :=
  BorshPackedLen.reference
def get_instance_packed_len_sample : get_instance_packed_len_contract.Index := BorshPackedLen.sample

theorem get_instance_packed_len_reference :
    FamilyReference get_instance_packed_len_contract get_instance_packed_len_run :=
  BorshPackedLen.reference_holds

theorem get_instance_packed_len_satisfiable :
    FamilySatisfiable get_instance_packed_len_contract get_instance_packed_len_sample :=
  BorshPackedLen.sample_satisfiable

theorem get_instance_packed_len_has_execution :
    FamilyHasExecution get_instance_packed_len_contract get_instance_packed_len_run
      get_instance_packed_len_sample := BorshPackedLen.sample_execution

end Solanalib.Specs.SolanaBorsh.v0_10
