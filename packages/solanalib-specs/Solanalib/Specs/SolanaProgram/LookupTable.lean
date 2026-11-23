/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressLookupTableOwned

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.address_lookup_table.state.AddressLookupTable

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The selected bincode decoder and owned error destruction preserve every
reached state effect. The borrowed suffix is constructed only after decoding. -/
def deserialize_contract : Family := AddressLookupTableOwned.family
def deserialize_run : FamilyRun deserialize_contract := AddressLookupTableOwned.reference
def deserialize_sample : deserialize_contract.Index := AddressLookupTableOwned.sample

theorem deserialize_reference : FamilyReference deserialize_contract deserialize_run :=
  AddressLookupTableOwned.reference_holds

theorem deserialize_satisfiable : FamilySatisfiable deserialize_contract deserialize_sample :=
  AddressLookupTableOwned.sample_satisfiable

theorem deserialize_has_execution :
    FamilyHasExecution deserialize_contract deserialize_run deserialize_sample :=
  AddressLookupTableOwned.sample_execution

end Solanalib.Specs.SolanaProgram.address_lookup_table.state.AddressLookupTable
