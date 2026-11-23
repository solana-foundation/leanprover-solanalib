/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOperationsWitnesses

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorCodec

namespace AccountDeserialize

/-- The provided default delegates to the actual unchecked callback at the same slice-reference and
state, retaining its return, mutation, unwind or terminal result. -/
def try_deserialize_contract : Family := deserializeFamily
def try_deserialize_run : FamilyRun try_deserialize_contract := deserializeRun
def try_deserialize_sample : try_deserialize_contract.Index := deserializeSample
theorem try_deserialize_reference : FamilyReference try_deserialize_contract try_deserialize_run :=
  deserialize_reference
theorem try_deserialize_has_execution :
    FamilyHasExecution try_deserialize_contract try_deserialize_run try_deserialize_sample :=
  deserialize_execution
theorem try_deserialize_satisfiable : FamilySatisfiable try_deserialize_contract
  try_deserialize_sample :=
  try_deserialize_has_execution.satisfiable

end AccountDeserialize

namespace bpf_upgradeable_state.UpgradeableLoaderState

/-- Use the fixed bincode loader-state format without advancing the input slice. On failure
construct the boxed InvalidAccountData error before dropping the original decoder diagnostic. -/
def try_deserialize_unchecked_contract : Family := loaderFamily
def try_deserialize_unchecked_run : FamilyRun try_deserialize_unchecked_contract := loaderRun
def try_deserialize_unchecked_sample : try_deserialize_unchecked_contract.Index := loaderSample
theorem try_deserialize_unchecked_reference : FamilyReference try_deserialize_unchecked_contract
  try_deserialize_unchecked_run :=
  loader_reference
theorem try_deserialize_unchecked_has_execution :
    FamilyHasExecution try_deserialize_unchecked_contract try_deserialize_unchecked_run
      try_deserialize_unchecked_sample :=
  loader_hasExecution
theorem try_deserialize_unchecked_satisfiable : FamilySatisfiable
  try_deserialize_unchecked_contract try_deserialize_unchecked_sample :=
  try_deserialize_unchecked_has_execution.satisfiable

end bpf_upgradeable_state.UpgradeableLoaderState

end Solanalib.Specs.AnchorLang
