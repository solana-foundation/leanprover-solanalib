/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessPrepare
public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessAdmission
public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessResources
public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessBorrows

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.Witness

/-- The sample callback checks the actual observed request, released mint
lease and remaining owners before accepting a finite invocation. -/
def invocationReady (state : State) (request : CpiRequest.Request AccountInfo.Value) : Prop :=
  request = expectedRequest ∧
  prepared.observe sampleTypes state Onchain.witnessArgs.signers = some request ∧
  state.1.lease Onchain.witnessInfo.data = .free ∧
  state.2.lamportsOwners = 5 ∧ state.2.dataOwners = 5

/-- An observable state change made by the opaque sample CPI callback. This
is an explicit mathematical dependency, not a proof of the invoked program. -/
def invocationAfter (state : State) : State :=
  (state.1, { state.2 with invocations := state.2.invocations + 1 })

/-- A normal sample CPI exit preserves its chosen Result and records the
call in the actual state, after checking the complete invocation boundary. -/
def returningInvocation (result : Except Error Unit) :
    CpiRequest.Invocation State AccountInfo.Value Error Nat Nat :=
  fun state request outcome => invocationReady state request ∧
    outcome = .returned result (invocationAfter state)

/-- No-hook preparation never calls collection. This deliberately partial
provider supplies no assumed execution of a populated hook collection. -/
def unusedCollection : AllocatedCollect.Provider Extra Nat Nat Nat where
  run := fun _ _ _ _ => False

/-- The explicit dependencies for the closed successful operational sample. -/
def sampleDependencies : Dependencies sampleTypes where
  collect := unusedCollection
  invoke := returningInvocation (.ok ())

/-- The same explicit types and dependencies are used for both closed family
witnesses; neither witness takes a successful preparation as a parameter. -/
def sample : Index := ⟨sampleTypes, sampleDependencies⟩

/-- The same actual protocol discharges the guard, input, storage
and cleanup admission of the sample. Its opaque invocation changes only its event counter. -/
theorem sample_ready : (family.contract sample).requires initialState Onchain.witnessArgs := by
  refine ⟨sampleGuardProtocol,
    sample_admitted sampleDependencies (fun _ _ _ _ impossible => impossible),
    sample_resources sampleDependencies ?_, sample_borrows sampleDependencies sampleGuardProtocol⟩
  intro _ _ _ _ _ _ called retained current _
  cases called.2
  cases retained <;> exact current

/-- The normal or unwinding state of the callback, before local vector cleanup. -/
def invokedState : State := invocationAfter preparedState

/-- The state after dropping the four current elements of the account vector. -/
def elementsDroppedState : State := dropped accounts invokedState

/-- Element destruction precedes retirement of the account vector slot. -/
def infosDroppedState : State := infosFocus.set elementsDroppedState [none]

/-- The metadata allocation of the instruction is retired after its account vector. -/
def metasDroppedState : State := metasFocus.set infosDroppedState [none]

/-- All temporary instruction and account-vector allocations have been retired. -/
def finalState : State := bytesFocus.set metasDroppedState [none]

/-- The independently derived preparation meets every callback check. -/
theorem invocation_ready : invocationReady preparedState expectedRequest := by
  refine ⟨rfl, prepared_observation, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The closed callback is actually called with the current constructed request. -/
theorem invocation_returns : sampleDependencies.invoke preparedState expectedRequest
    (.returned (.ok ()) invokedState) :=
  ⟨invocation_ready, rfl⟩

/-- The four vector entries retain enough live Rc owners for their actual
destruction after CPI, including the state mutation of the callback. -/
theorem element_drops_ready : dropsReady accounts invokedState := by
  unfold accounts
  simp only [List.replicate, dropsReady, dropReady, rcReady]
  decide +kernel

/-- The info-vector destructor drops its actual current entries in order
and only then retires its allocation. It retains the CPI state effect. -/
theorem infos_drop_returns : sampleTypes.infos.drop invokedState (0 : Nat)
    (.returned () infosDroppedState) := by
  refine ⟨accounts, rfl, .returned () elementsDroppedState,
    drop_infos_returns accounts invokedState element_drops_ready, ?_⟩
  exact ⟨.returned () [none], ⟨accounts, rfl, rfl⟩, rfl⟩

/-- The exact current metadata allocation is retired after info cleanup. -/
theorem metas_drop_returns : sampleTypes.metas.drop infosDroppedState (0 : Nat)
    (.returned () metasDroppedState) :=
  ⟨.returned () [none], ⟨plan.metas.items, rfl, rfl⟩, rfl⟩

/-- The exact current packed data allocation is retired last. -/
theorem bytes_drop_returns : sampleTypes.bytes.drop metasDroppedState (0 : Nat)
    (.returned () finalState) :=
  ⟨.returned () [none], ⟨plan.data, rfl, rfl⟩, rfl⟩

/-- This trace contains actual element and vector destructor executions in
the source order: account entries, account vector, metadata, instruction data. -/
theorem prepared_drop_trace :
    Owned.DropReturns (prepared.drops sampleTypes) invokedState finalState :=
  .cons _ _ invokedState infosDroppedState finalState infos_drop_returns
    (.cons _ _ infosDroppedState metasDroppedState finalState metas_drop_returns
      (.cons _ _ metasDroppedState finalState finalState bytes_drop_returns (.nil finalState)))

/-- Any supplied primitive CPI exit composes with the fully derived
preparation and actual cleanup; this lemma assumes no whole-builder callback. -/
theorem invoke_from_prepared (deps : Dependencies sampleTypes)
    (pending final : Outcome State (Except Error Unit) Nat Nat)
    (called : deps.invoke preparedState expectedRequest pending)
    (cleaned : Owned.cleanup sampleTypes.doubleUnwind
      (prepared.drops sampleTypes) pending final) :
    invoke sampleTypes deps Onchain.witnessArgs initialState final := by
  refine ⟨.returned (.ok prepared) preparedState, prepare_returns deps, ?_⟩
  exact ⟨pending,
    ⟨.returned (.ok expectedRequest) preparedState,
      ⟨expectedRequest, prepared_observation, rfl⟩, called⟩,
    cleaned⟩

/-- Complete successful execution includes ordinary instruction construction,
Rc clones, live mint parsing, guard and argument cleanup, CPI and final drops. -/
theorem invoke_returns :
    invoke sampleTypes sampleDependencies Onchain.witnessArgs initialState
      (.returned (.ok ()) finalState) :=
  invoke_from_prepared sampleDependencies _ _ invocation_returns
    (prepared_drop_trace.cleanup_returned sampleTypes.doubleUnwind (Except.ok () : Except Error
      Unit))

/-- All 24 Rc operations in this sample: four two-field clones, four
two-field argument drops, then four two-field account-vector element drops. -/
def expectedRcTrace : List AccountInfoRc.Event :=
  (List.replicate 4 Onchain.witnessInfo).flatMap (fun info =>
    [.clone .lamports info.lamports, .clone .data info.data]) ++
  (List.replicate 8 Onchain.witnessInfo).flatMap (fun info =>
    [.drop .lamports info.lamports, .drop .data info.data])

/-- No temporary guard or vector is live on return. The outside Rc owner
remains, and both the precise clone/drop order and CPI state effect survive. -/
theorem final_resources :
    finalState.1 = Onchain.witnessAfter ∧
    finalState.1.lease Onchain.witnessInfo.data = .free ∧
    finalState.2.bytes = [none] ∧ finalState.2.metas = [none] ∧
    finalState.2.infos = [none] ∧ finalState.2.guards = [] ∧
    finalState.2.discriminators = [] ∧ finalState.2.seeds = [] ∧
    finalState.2.seedRefs = [] ∧ finalState.2.lamportsOwners = 1 ∧
    finalState.2.dataOwners = 1 ∧ finalState.2.rcEvents = expectedRcTrace ∧
    finalState.2.cleanupEvents = [] ∧ finalState.2.invocations = 1 := by
  decide +kernel

/-- Closed nonvacuity for the full allocated source family: the exhibited
finite exit is a successful CPI return after all local ownership cleanup. -/
theorem has_execution : FamilyHasExecution family reference sample :=
  ⟨initialState, Onchain.witnessArgs, .returned (.ok ()) finalState,
    sample_ready, invoke_returns⟩

/-- The execution witness also inhabits the same admitted family index. -/
theorem satisfiable : FamilySatisfiable family sample := has_execution.satisfiable

end Solanalib.Specs.Core.Token.OnchainAllocated.Witness
