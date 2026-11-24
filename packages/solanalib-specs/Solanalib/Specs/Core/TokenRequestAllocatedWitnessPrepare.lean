/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessSteps

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.Witness

/-- The shared mint-data guard retains all 82 bytes of the initialized base mint. -/
def mintReference : AllocatedControl.DataRef := ⟨⟨0, 0⟩, 82⟩

/-- The real account-borrow world while the mint guard occupies slot zero. -/
def mintBorrowWorld : AccountInfo.State := { Onchain.witnessState with
  slots := [some ⟨⟨1⟩, .shared, 0, .whole⟩] }

/-- Mint parsing sees the live guard and all constructed owned values. -/
def mintState : State := (mintBorrowWorld, infosState.2)
/-- The guard slot is retired before the original AccountInfo arguments drop. -/
def guardReleasedState : State := (Onchain.witnessAfter, infosState.2)

/-- The concrete initialized bare mint decoded by the sample execution. -/
def decodedMint : Mint := ⟨none, 0, 0, true, none⟩

/-- The real shared-borrow transition creates the retained mint reference. -/
theorem mint_borrow_returns :
    AllocatedControl.borrow sampleTypes.raise true Onchain.witnessArgs.mint infosState
      (.returned (.ok mintReference) mintState) := by
  rfl

/-- The retained reference follows the currently borrowed mint bytes. -/
theorem mint_reference_reads :
    mintReference.read mintState = some Onchain.witnessMintBytes := by
  rfl

/-- The initialized 82-byte mint is decoded, and its empty extension remainder
returns without the source 3.0.0 padding allocation or any hook callback. -/
theorem mint_hook_absent :
    readMintHook sampleTypes mintReference mintState
      (.returned (.ok none) mintState) := by
  refine ⟨.returned (.ok Onchain.witnessMintBytes) mintState,
    ⟨Onchain.witnessMintBytes, mint_reference_reads, rfl⟩, ?_⟩
  refine ⟨.returned (.ok decodedMint) mintState, (by rfl), ?_⟩
  refine ⟨.returned (.ok ([] : Bytes)) mintState, ?_, ?_⟩
  · exact AllocatedTlv.mintTail_empty _ _ _ _ (by rfl)
  · change AllocatedControl.pure (Onchain.hookProgram ([] : Bytes)) mintState
      (.returned (.ok none) mintState)
    have absent : Onchain.hookProgram ([] : Bytes) = none := by decide +kernel
    simp only [AllocatedControl.pure, absent]

/-- Successful mint preparation retains its live reference for the scope of the caller; it does not
release the guard before returning that reference. -/
theorem begin_mint_returns :
    beginMint sampleTypes Onchain.witnessArgs infosState
      (.returned (.ok (mintReference, none)) mintState) := by
  refine ⟨.returned (.ok mintReference) mintState, mint_borrow_returns, ?_⟩
  exact ⟨.returned (.ok (mintReference, none)) mintState,
    ⟨.returned (.ok none) mintState, mint_hook_absent, rfl⟩, rfl⟩

/-- The caller consumes the actual mint guard and leaves a retired slot. -/
theorem mint_guard_drop :
    mintReference.drop mintState
      (.returned () guardReleasedState : Outcome State Unit Nat Nat) := by
  rfl

/-- Owned function arguments in their source cleanup order. -/
def arguments : List AccountInfo.Value :=
  [Onchain.witnessArgs.authority, Onchain.witnessArgs.destination,
    Onchain.witnessArgs.mint, Onchain.witnessArgs.source]

/-- The call boundary after guard release and all four original argument drops. -/
def preparedState : State := dropped arguments guardReleasedState

/-- All four moved argument owners exist when their reverse-order cleanup
begins; the live cloned account-vector owners are retained. -/
theorem argument_drops_ready : dropsReady arguments guardReleasedState := by
  unfold arguments
  simp only [dropsReady, dropReady, rcReady]
  decide +kernel

theorem argument_cleanup :
    Owned.cleanup sampleTypes.doubleUnwind (argumentDrops sampleTypes Onchain.witnessArgs)
      (.returned (.ok prepared) guardReleasedState :
        Outcome State (Except Error (Prepared sampleTypes)) Nat Nat)
      (.returned (.ok prepared) preparedState) := by
  exact (drop_trace arguments guardReleasedState argument_drops_ready).cleanup_returned
    sampleTypes.doubleUnwind (Except.ok prepared : Except Error (Prepared sampleTypes))

/-- Every allocation, clone, mint read, guard retirement and argument drop is
executed before preparation returns. The no-hook path needs no collection or
invocation dependency; those cannot serve as assumed preparation witnesses. -/
theorem prepare_returns (deps : Dependencies sampleTypes) :
    prepare sampleTypes deps Onchain.witnessArgs initialState
      (.returned (.ok prepared) preparedState) := by
  refine ⟨.returned (.ok prepared) infosState,
    ⟨.returned (.ok prepared) infosState, base_returns, rfl⟩, ?_⟩
  refine ⟨.returned (.ok (mintReference, none)) mintState, ?_, ?_⟩
  · exact ⟨.returned (.ok (mintReference, none)) mintState,
      ⟨.returned (.ok (mintReference, none)) mintState, begin_mint_returns, rfl⟩, rfl⟩
  · exact ⟨.returned (.ok prepared) guardReleasedState,
      ⟨.returned (.ok prepared) mintState, rfl,
        .returned () guardReleasedState, mint_guard_drop, rfl⟩,
      argument_cleanup⟩

/-- The CPI boundary observes the exact packed instruction, four live cloned
account entries and the original nested signer seed slices. -/
def expectedRequest : CpiRequest.Request AccountInfo.Value :=
  Onchain.witnessPrepared.request Onchain.witnessArgs.signers

theorem prepared_observation :
    prepared.observe sampleTypes preparedState Onchain.witnessArgs.signers =
      some expectedRequest := by
  rfl

/-- Preparation has released the shared guard and only its moved argument
owners. Four cloned entries and the outside owner remain at the call boundary. -/
theorem prepared_resource_counts :
    preparedState.1 = Onchain.witnessAfter ∧
    preparedState.1.lease Onchain.witnessInfo.data = .free ∧
    preparedState.2.lamportsOwners = 5 ∧ preparedState.2.dataOwners = 5 ∧
    preparedState.2.rcEvents.length = 16 ∧
    preparedState.2.infos = [some accounts] := by
  decide +kernel

end Solanalib.Specs.Core.Token.OnchainAllocated.Witness
