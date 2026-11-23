/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenMetadataInitializeSample

@[expose] public section

open Solanalib.Contracts.Model

namespace Solanalib.Specs.SplTokenMetadataInterface.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token.MetadataInitialize

/-- Complete local instruction construction, including Borsh, owned string
cleanup and the constructed return place. No program-ID check is made. -/
def initialize_contract := family

/-- The same explicit finite dependency execution relation. -/
def initialize_reference : FamilyRun initialize_contract := reference

/-- Every modeled finite exit retains its actual state and local cleanup. -/
theorem initialize_reference_holds :
    FamilyReference initialize_contract initialize_reference := reference_holds

/-- Closed current-owner interpretation with disjoint byte/metadata ledgers. -/
def initialize_sample : initialize_contract.Index := Sample.index

/-- Complete construction of non-ASCII metadata with actual buffer ownership. -/
theorem initialize_has_execution :
    FamilyHasExecution initialize_contract initialize_reference initialize_sample :=
  ⟨Sample.initial, Sample.args, _, trivial, Sample.executes⟩

/-- The executed example is an admitted source constructor input. -/
theorem initialize_satisfiable : FamilySatisfiable initialize_contract initialize_sample :=
  initialize_has_execution.satisfiable

end Solanalib.Specs.SplTokenMetadataInterface.instruction
