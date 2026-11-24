/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressDerived

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplAssociatedTokenAccountClient.address

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Operations

/-! Prepare the exact seed boundaries/order and fixed program ID, invoke the
resolved PDA search, and discard only the returned bump. -/

def get_associated_token_address_with_program_id_contract : Family := zeroDerivedFamily
  AssociatedInputs associatedInputs
def get_associated_token_address_with_program_id_run : FamilyRun
  get_associated_token_address_with_program_id_contract := zeroDerivedReference AssociatedInputs
  associatedInputs
def get_associated_token_address_with_program_id_sample :
  get_associated_token_address_with_program_id_contract.Index := zeroFindSample

theorem get_associated_token_address_with_program_id_reference : FamilyReference
  get_associated_token_address_with_program_id_contract
  get_associated_token_address_with_program_id_run :=
  zeroDerivedReference_correct AssociatedInputs associatedInputs

theorem get_associated_token_address_with_program_id_has_execution :
    FamilyHasExecution get_associated_token_address_with_program_id_contract
      get_associated_token_address_with_program_id_run
      get_associated_token_address_with_program_id_sample :=
  zeroDerivedSample_execution AssociatedInputs associatedInputs (⟨.zero, .zero, .zero⟩)

theorem get_associated_token_address_with_program_id_satisfiable :
    FamilySatisfiable get_associated_token_address_with_program_id_contract
      get_associated_token_address_with_program_id_sample :=
  get_associated_token_address_with_program_id_has_execution.satisfiable

end Solanalib.Specs.SplAssociatedTokenAccountClient.address
