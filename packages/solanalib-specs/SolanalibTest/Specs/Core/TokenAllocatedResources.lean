/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessResources

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.TokenAllocatedResources

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Token.OnchainAllocated Token.OnchainAllocated.Admission Token.OnchainAllocated.Witness

/-- This dependency returns a token while leaving its current slot absent. -/
def missingLiteralTypes : Types :=
  { sampleTypes with seedOps := { sampleTypes.seedOps with
      bytes := { sampleTypes.seedOps.bytes with
        fromList := fun before _ outcome => outcome = .returned (0 : Nat) before } } }

theorem missing_literal_actual_return :
    missingLiteralTypes.seedOps.bytes.fromList initialState [7] (.returned (0 : Nat) initialState)
      := rfl

theorem missing_literal_next_read :
    Token.AllocatedSeeds.widthAt missingLiteralTypes.seedOps.bytes initialState (.literal (0 :
      Nat)) = none := rfl

/-- Account guard preservation alone admits this bad constructor exit. -/
theorem missing_literal_keeps_guards :
    Token.AllocatedGuard.Preserves missingLiteralTypes.seedOps.bytes.fromList := by
  apply Token.AllocatedGuard.Preserves.of_accounts
  intro before args outcome called
  cases called
  rfl

/-- Constructor admission rejects it at that actual return, before the
missing width read can erase all later finite SDK outcomes. -/
theorem missing_literal_rejected : ¬ ConstructorsReady missingLiteralTypes := by
  intro ready
  have current := (ready.literalList initialState [7] (0 : Nat) initialState
    missing_literal_actual_return).1
  cases current

/-- One owned instruction byte vector and an empty, independently owned meta vector. -/
def beforePush : State :=
  (initialState.1, { initialState.2 with bytes := [some [12]], metas := [some []] })

def item : Solanalib.Runtime.CpiMeta := Instruction.accountMeta Solanalib.Runtime.Pubkey.zero false
  false

def afterGoodPush : State := metasFocus.set beforePush [some [item]]

/-- This finite push performs the correct own-vector update, then erases
the unrelated retained instruction byte ledger. -/
def erasingMetaTypes : Types :=
  { sampleTypes with metas := { sampleTypes.metas with
      push := fun before input outcome => ∃ after,
        sampleTypes.metas.push before input (.returned () after) ∧
        outcome = .returned () (bytesFocus.set after []) } }

def afterErasingPush : State := bytesFocus.set afterGoodPush []

theorem good_push_actual_return :
    sampleTypes.metas.push beforePush ((0 : Nat), item) (.returned () afterGoodPush) :=
  ⟨.returned () [some [item]], ⟨[], rfl, rfl⟩, rfl⟩

theorem erasing_push_actual_return :
    erasingMetaTypes.metas.push beforePush ((0 : Nat), item) (.returned () afterErasingPush) :=
  ⟨afterGoodPush, good_push_actual_return, rfl⟩

theorem erasing_push_own_shape : erasingMetaTypes.metas.current afterErasingPush (0 : Nat) = some
  [item] := rfl

theorem erasing_push_next_read : erasingMetaTypes.bytes.current afterErasingPush (0 : Nat) = none
  := rfl

/-- The typed retained-resource frame detects destruction even though the vector update of the
provider has the expected contents. -/
theorem erasing_push_rejected :
    ¬ PrimitiveResources (ResourcePrimitive.metasPush (types := erasingMetaTypes)) := by
  intro law
  have current := law beforePush ((0 : Nat), item) (.bytes (0 : Nat) [12]) rfl
    (.returned () afterErasingPush) erasing_push_actual_return
    (by simp [Touches, Retained.resource])
  cases current

theorem erasing_push_not_ready (deps : Dependencies erasingMetaTypes)
    (protocol : Token.AllocatedCollect.Protocol erasingMetaTypes.Extra
      erasingMetaTypes.GuardResource
      erasingMetaTypes.Unwind erasingMetaTypes.Terminal) :
    ¬ ResourceReady erasingMetaTypes deps protocol := by
  intro ready
  exact erasing_push_rejected (ready.primitive .metasPush)

/-- A real metadata mutation retains the independently owned byte vector
and reaches its next current read in the actual post-push state. -/
theorem good_push_retains_current : sampleTypes.bytes.current afterGoodPush (0 : Nat) = some [12] :=
  sample_resource_primitives .metasPush beforePush ((0 : Nat), item) (.bytes (0 : Nat) [12]) rfl
    (.returned () afterGoodPush) good_push_actual_return (by simp [Touches, Retained.resource])

theorem good_push_local_read :
    Token.AllocatedControl.bind
      (Token.AllocatedControl.perform fun state => sampleTypes.metas.push state ((0 : Nat), item))
      (fun _ => Token.AllocatedControl.inspect fun state => sampleTypes.metas.current state (0 :
        Nat))
      beforePush (.returned (.ok [item]) afterGoodPush) :=
  (sample_resource_mutations.metasPush.read_after_exit (values := []) rfl good_push_actual_return).1

/-- A finite unwinding push may retain partial current contents for cleanup. -/
def unwindingPush : Callback.Run State (Nat × UInt8) Unit Nat Nat :=
  fun before input outcome =>
    outcome = .unwound 7 (bytesFocus.set before (before.2.bytes.set input.1 (some [input.2])))

def unwindingBytes : Owned.VectorOps State UInt8 Nat Nat Nat :=
  { sampleTypes.bytes with push := unwindingPush }

theorem unwinding_bytes_ready : PushReady unwindingBytes := by
  constructor
  · intro before resource value values after current called
    cases called
  · rintro before resource value reason after ⟨values, current⟩ called
    cases called
    exact ⟨[value], Owned.VectorState.current_set before.2.bytes resource _
      (Owned.VectorState.current_bound current)⟩

def afterUnwind : State := bytesFocus.set beforePush [some [99]]

theorem unwind_actual_exit : unwindingBytes.push beforePush (0, 99) (.unwound 7 afterUnwind) := rfl

/-- The read is skipped on unwind and the changed current token remains
available to source cleanup; no drop termination assumption is introduced. -/
theorem unwind_local_continuation :
    Token.AllocatedControl.bind
      (Token.AllocatedControl.perform fun state => unwindingBytes.push state (0, 99))
      (fun _ => Token.AllocatedControl.inspect fun state => unwindingBytes.current state 0)
      beforePush (.unwound 7 afterUnwind) ∧ unwindingBytes.Live afterUnwind 0 :=
  unwinding_bytes_ready.read_after_exit (values := [12]) rfl unwind_actual_exit

theorem unwind_partial_effect :
    unwindingBytes.current afterUnwind 0 = some [99] ∧
    sampleTypes.metas.current afterUnwind (0 : Nat) = some [] := ⟨rfl, rfl⟩

/-- A local sample index with an unavailable collection and invocation;
neither dependency is given an invented finite execution by resource admission. -/
def controlDependencies : Dependencies sampleTypes where
  collect := { run := fun _ _ _ _ => False }
  invoke := fun _ _ _ => False

theorem control_resources : ResourceReady sampleTypes controlDependencies sampleGuardProtocol := by
  apply sample_resources
  intro prepared before signers request observed outcome impossible
  exact False.elim impossible

def afterPadding : State := bytesFocus.set beforePush [some [12], some (List.replicate 83 0)]

def afterPaddingDrop : State := bytesFocus.set afterPadding [some [12], none]

theorem padding_actual_return : sampleTypes.paddingBytes.fromList beforePush (List.replicate 83 0)
    (.returned (1 : Nat) afterPadding) := ⟨.returned 1 [some [12], some (List.replicate 83 0)],
      rfl, rfl⟩

theorem padding_actual_drop : sampleTypes.paddingBytes.drop afterPadding (1 : Nat) (.returned ()
  afterPaddingDrop) :=
  ⟨.returned () [some [12], none], ⟨List.replicate 83 0, rfl, rfl⟩, rfl⟩

/-- Freshness is consumed by an actual constructor/destructor composition:
the temporary retires while the old byte owner of the instruction remains current. -/
theorem padding_cleanup_keeps_instruction :
    Callback.bind sampleTypes.paddingBytes.fromList
      (fun resource state outcome => sampleTypes.paddingBytes.drop state resource outcome)
      beforePush (List.replicate 83 0) (.returned () afterPaddingDrop) ∧
    sampleTypes.bytes.current afterPaddingDrop (0 : Nat) = some [12] :=
  control_resources.padding_cleanup_retains_data rfl padding_actual_return padding_actual_drop

def literalArgs : Token.AllocatedSeeds.Args State where
  extraAt := fun _ => none
  instructionAt := fun state => sampleTypes.bytes.current state (0 : Nat)
  programAt := fun _ => some Solanalib.Runtime.Pubkey.zero
  accountsAt := fun _ => some []

def instructionView : Token.AllocatedSeeds.BytesView State :=
  ⟨1, fun state => sampleTypes.bytes.current state (0 : Nat)⟩

def literalView : Token.AllocatedSeeds.BytesView State :=
  ⟨1, fun state => sampleTypes.seedOps.bytes.current state (0 : Nat)⟩

theorem literal_view_actual_return :
    Token.AllocatedSeeds.seedView sampleTypes.seedOps literalArgs instructionView
      (.literal (0 : Nat)) beforePush () (.returned (.ok (some literalView)) beforePush) :=
  ⟨[12], rfl, rfl⟩

/-- The view is obtained from an actual source borrow before the effectful
metadata call. Its current bytes survive that call through resource retention. -/
theorem literal_view_good_effect : literalView.observe afterGoodPush = some [12] := by
  have source : SourceSeedView sampleTypes literalArgs instructionView literalView :=
    seedView_source (types := sampleTypes) literalArgs instructionView literal_view_actual_return
  apply source.observe_kept (before := beforePush)
  · intro resource values current
    exact sample_resource_primitives .metasPush beforePush ((0 : Nat), item)
      (.literal resource values) current (.returned () afterGoodPush) good_push_actual_return
      (by simp [Touches, Retained.resource])
  · intro bytes current
    exact current
  · intro accounts current
    exact current
  · rfl

/-- The destructive provider also loses this actual captured seed view. -/
theorem literal_view_erased : literalView.observe afterErasingPush = none := rfl

end SolanalibTest.Specs.Core.TokenAllocatedResources
