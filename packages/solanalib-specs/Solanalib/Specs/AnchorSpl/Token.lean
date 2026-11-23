/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSpl
public import Solanalib.Specs.Core.AnchorOwnedSamples
public import Solanalib.Specs.Core.AnchorSplTransferSample
public import Solanalib.Specs.Core.AnchorSplTokenOperations.Sample
public import Solanalib.Specs.Core.AnchorSplTokenOperations.Continuation
public import Solanalib.Specs.Core.AnchorSplTokenOperations.BuilderErrors

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace token.Mint

def deref_contract := AnchorAccount.projectionFamily
  (fun _ => AnchorSpl.Mint) (fun _ => Token.Mint) (fun _ => AnchorSpl.mintDeref)
def deref_run := AnchorAccount.projectionRun
  (fun _ => AnchorSpl.Mint) (fun _ => Token.Mint) (fun _ => AnchorSpl.mintDeref)
def deref_sample := AnchorAccount.projectionSample
theorem deref_reference : FamilyReference deref_contract deref_run :=
  AnchorAccount.projection_reference _ _ _
theorem deref_has_execution : FamilyHasExecution deref_contract deref_run deref_sample :=
  AnchorAccount.projection_execution _ _ _ ⟨AnchorSpl.sampleMint⟩
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  deref_has_execution.satisfiable

end token.Mint

namespace token_interface.Mint

def deref_contract := AnchorAccount.projectionFamily
  (fun _ => AnchorSpl.InterfaceMint) (fun _ => Token.Mint) (fun _ => AnchorSpl.interfaceMintDeref)
def deref_run := AnchorAccount.projectionRun
  (fun _ => AnchorSpl.InterfaceMint) (fun _ => Token.Mint) (fun _ => AnchorSpl.interfaceMintDeref)
def deref_sample := AnchorAccount.projectionSample
theorem deref_reference : FamilyReference deref_contract deref_run :=
  AnchorAccount.projection_reference _ _ _
theorem deref_has_execution : FamilyHasExecution deref_contract deref_run deref_sample :=
  AnchorAccount.projection_execution _ _ _ ⟨AnchorSpl.sampleMint⟩
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  deref_has_execution.satisfiable

end token_interface.Mint

namespace token.accessor

def amount_observation_contract := AnchorSpl.amountContract
def amount_observation_run := AnchorSpl.amountRun
theorem amount_observation_reference : amount_observation_contract.Holds amount_observation_run :=
  AnchorSpl.amount_reference
theorem amount_observation_has_execution : amount_observation_contract.HasExecution
  amount_observation_run := AnchorSpl.amount_execution
theorem amount_observation_satisfiable : amount_observation_contract.Satisfiable :=
  amount_observation_has_execution.satisfiable

def amount_contract := AnchorSplAmountOwned.family
def amount_run := AnchorSplAmountOwned.reference
def amount_sample := AnchorOwnedSamples.amount
theorem amount_reference : FamilyReference amount_contract amount_run :=
  AnchorSplAmountOwned.reference_holds
theorem amount_has_execution : FamilyHasExecution amount_contract amount_run amount_sample :=
  AnchorOwnedSamples.amount_execution
theorem amount_satisfiable : FamilySatisfiable amount_contract amount_sample :=
  amount_has_execution.satisfiable

end token.accessor

namespace token

def transfer_observation_contract := AnchorSpl.transferFamily
def transfer_observation_run := AnchorSpl.transferRun
def transfer_observation_sample := AnchorSpl.transferSample
theorem transfer_observation_reference : FamilyReference transfer_observation_contract
  transfer_observation_run := AnchorSpl.transfer_reference
theorem transfer_observation_has_execution :
    FamilyHasExecution transfer_observation_contract transfer_observation_run
      transfer_observation_sample := AnchorSpl.transfer_execution
theorem transfer_observation_satisfiable : FamilySatisfiable transfer_observation_contract
  transfer_observation_sample :=
  transfer_observation_has_execution.satisfiable

def transfer_contract := AnchorSplTransfer.family
def transfer_run := AnchorSplTransfer.reference
def transfer_sample := AnchorSplTransfer.Sample.types
theorem transfer_reference : FamilyReference transfer_contract transfer_run :=
  AnchorSplTransfer.reference_holds
theorem transfer_has_execution :
    FamilyHasExecution transfer_contract transfer_run transfer_sample :=
      AnchorSplTransfer.Sample.execution
theorem transfer_satisfiable : FamilySatisfiable transfer_contract transfer_sample :=
  transfer_has_execution.satisfiable

end token

end Solanalib.Specs.AnchorSpl

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorSpl.token

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplTokenOperations

/-- Exact reviewed 0.27.0 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def burn_contract := family .tokenBurn027
def burn_run := reference .tokenBurn027
def burn_sample := Sample.types .tokenBurn027
theorem burn_reference : FamilyReference burn_contract burn_run :=
  reference_holds .tokenBurn027
theorem burn_has_execution :
    FamilyHasExecution burn_contract burn_run burn_sample :=
  Sample.execution .tokenBurn027
theorem burn_satisfiable : FamilySatisfiable burn_contract burn_sample :=
  burn_has_execution.satisfiable

/-- Exact reviewed 0.27.0 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def mint_to_contract := family .tokenMintTo027
def mint_to_run := reference .tokenMintTo027
def mint_to_sample := Sample.types .tokenMintTo027
theorem mint_to_reference : FamilyReference mint_to_contract mint_to_run :=
  reference_holds .tokenMintTo027
theorem mint_to_has_execution :
    FamilyHasExecution mint_to_contract mint_to_run mint_to_sample :=
  Sample.execution .tokenMintTo027
theorem mint_to_satisfiable : FamilySatisfiable mint_to_contract mint_to_sample :=
  mint_to_has_execution.satisfiable

/-- Exact reviewed 0.27.0 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def transfer_inline_error_contract := family .tokenTransfer027
def transfer_inline_error_run := reference .tokenTransfer027
def transfer_inline_error_sample := Sample.types .tokenTransfer027
theorem transfer_inline_error_reference : FamilyReference transfer_inline_error_contract
  transfer_inline_error_run :=
  reference_holds .tokenTransfer027
theorem transfer_inline_error_has_execution :
    FamilyHasExecution transfer_inline_error_contract transfer_inline_error_run
      transfer_inline_error_sample :=
  Sample.execution .tokenTransfer027
theorem transfer_inline_error_satisfiable : FamilySatisfiable transfer_inline_error_contract
  transfer_inline_error_sample :=
  transfer_inline_error_has_execution.satisfiable

end Solanalib.Specs.AnchorSpl.token
