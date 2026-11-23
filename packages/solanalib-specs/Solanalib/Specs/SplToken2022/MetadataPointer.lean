/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenMetadataPointer

@[expose] public section

open Solanalib.Contracts.Model

namespace Solanalib.Specs.SplToken2022.extension.metadata_pointer.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token

/-- Token-2022 8.0.1 metadata-pointer initialization, including the post-allocation
optional-key errors, the exact POD encoding and all dependency cleanup exits. -/
def initialize_contract := MetadataPointer.family 39

/-- Same ordered constructor with the actual vector providers. -/
def initialize_reference : FamilyRun initialize_contract := MetadataPointer.reference 39

/-- Correctness is parametric in the complete dependency interpretation. -/
theorem initialize_reference_holds :
    FamilyReference initialize_contract initialize_reference := MetadataPointer.reference_holds 39

/-- Closed ledger interpretation used by the execution witness. -/
def initialize_sample : initialize_contract.Index := MetadataPointer.sample

/-- An actual successful allocation and two-field encoding. -/
theorem initialize_has_execution :
    FamilyHasExecution initialize_contract initialize_reference initialize_sample :=
  MetadataPointer.has_execution

/-- This finite successful execution also witnesses admission. -/
theorem initialize_satisfiable : FamilySatisfiable initialize_contract initialize_sample :=
  initialize_has_execution.satisfiable

end Solanalib.Specs.SplToken2022.extension.metadata_pointer.instruction
