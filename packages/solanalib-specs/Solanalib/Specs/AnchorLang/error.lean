/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorCallbacks
public import Solanalib.Specs.Core.AnchorErrorOwnedContracts
public import Solanalib.Specs.Core.AnchorErrorOwnedCallbackContracts
public import Solanalib.Specs.Core.ProgramError
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.error

abbrev Source := Solanalib.Specs.Core.AnchorError.Source
abbrev ErrorOrigin := Solanalib.Specs.Core.AnchorError.Origin
abbrev ComparedValues := Solanalib.Specs.Core.AnchorError.ComparedValues
abbrev AnchorError := Solanalib.Specs.Core.AnchorError.AnchorValue
abbrev ProgramErrorWithOrigin :=
  Solanalib.Specs.Core.AnchorError.ProgramValue Solanalib.Specs.Core.ProgramError.Value
abbrev Error := Solanalib.Specs.Core.AnchorError.Value Solanalib.Specs.Core.ProgramError.Value

namespace Error

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AnchorError

/-- The selected `From<AnchorError>` value conversion. Box representation and
allocation outcomes require a separate implementation binding. -/
def from_anchor_error_observation_contract (State : Type) :
    Solanalib.Contracts.Model State AnchorError Error :=
  fromAnchorContract State ProgramError.Value

def from_anchor_error_observation_family : Family where
  Index := Type
  State := fun State => State
  Args := fun _ => AnchorError
  Value := fun _ => Error
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := from_anchor_error_observation_contract

def from_anchor_error_observation_run : FamilyRun from_anchor_error_observation_family :=
  fun _ => returnsOf fromAnchorReference

def from_anchor_error_observation_sample : from_anchor_error_observation_family.Index := Unit

/-- All state instantiations satisfy the same complete payload-preservation
contract. The theorem has no term or universe parameters. -/
theorem from_anchor_error_observation_reference :
    FamilyReference from_anchor_error_observation_family from_anchor_error_observation_run := by
  intro State
  exact (realized_iff_holds _ _).mp (fromAnchorReference_realizes State ProgramError.Value)

private def sampleAnchor : AnchorError :=
  ⟨"ConstraintRaw", 2003, "A raw constraint was violated", none, none⟩

theorem from_anchor_error_observation_satisfiable :
    FamilySatisfiable from_anchor_error_observation_family from_anchor_error_observation_sample :=
  ⟨(), sampleAnchor, trivial⟩

theorem from_anchor_error_observation_has_execution :
    FamilyHasExecution from_anchor_error_observation_family from_anchor_error_observation_run
      from_anchor_error_observation_sample :=
  ⟨(), sampleAnchor, .returned (.anchor sampleAnchor) (), trivial, rfl⟩

abbrev PubkeysArgs := AnchorError.PubkeysArgs ProgramError.Value

def with_pubkeys_observation_contract (State : Type) : Solanalib.Contracts.Model State PubkeysArgs
  Error :=
  withPubkeysContract State ProgramError.Value

def with_pubkeys_observation_family : Family where
  Index := Type
  State := fun State => State
  Args := fun _ => PubkeysArgs
  Value := fun _ => Error
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := with_pubkeys_observation_contract

def with_pubkeys_observation_run : FamilyRun with_pubkeys_observation_family :=
  fun _ => returnsOf withPubkeysReference

def with_pubkeys_observation_sample : with_pubkeys_observation_family.Index := Unit

theorem with_pubkeys_observation_reference : FamilyReference with_pubkeys_observation_family
  with_pubkeys_observation_run := by
  intro State
  exact (realized_iff_holds _ _).mp (withPubkeysReference_realizes State ProgramError.Value)

private def samplePubkeys : PubkeysArgs :=
  ⟨.anchor sampleAnchor, .zero, .ofNat 1⟩

theorem with_pubkeys_observation_satisfiable : FamilySatisfiable with_pubkeys_observation_family
  with_pubkeys_observation_sample :=
  ⟨(), samplePubkeys, trivial⟩

theorem with_pubkeys_observation_has_execution :
    FamilyHasExecution with_pubkeys_observation_family with_pubkeys_observation_run
      with_pubkeys_observation_sample :=
  ⟨(), samplePubkeys,
    .returned (samplePubkeys.error.replaceCompared
      (.pubkeys samplePubkeys.left samplePubkeys.right)) (), trivial, rfl⟩

def from_anchor_error_contract := AnchorErrorOwned.fromAnchorFamily
def from_anchor_error_run := AnchorErrorOwned.fromAnchorRun
def from_anchor_error_sample := AnchorErrorOwned.fromAnchor_sample
theorem from_anchor_error_reference : FamilyReference from_anchor_error_contract
  from_anchor_error_run :=
  AnchorErrorOwned.fromAnchor_reference
theorem from_anchor_error_satisfiable : FamilySatisfiable from_anchor_error_contract
  from_anchor_error_sample :=
  AnchorErrorOwned.fromAnchor_satisfiable
theorem from_anchor_error_has_execution :
    FamilyHasExecution from_anchor_error_contract from_anchor_error_run from_anchor_error_sample :=
  AnchorErrorOwned.fromAnchor_hasExecution

def with_pubkeys_contract := AnchorErrorOwned.withPubkeysFamily
def with_pubkeys_run := AnchorErrorOwned.withPubkeysRun
def with_pubkeys_sample := AnchorErrorOwned.withPubkeys_sample
theorem with_pubkeys_reference : FamilyReference with_pubkeys_contract with_pubkeys_run :=
  AnchorErrorOwned.withPubkeys_reference
theorem with_pubkeys_satisfiable : FamilySatisfiable with_pubkeys_contract with_pubkeys_sample :=
  AnchorErrorOwned.withPubkeys_satisfiable
theorem with_pubkeys_has_execution :
    FamilyHasExecution with_pubkeys_contract with_pubkeys_run with_pubkeys_sample :=
  AnchorErrorOwned.withPubkeys_hasExecution

/-- Source type parameters and explicit trait/cleanup interfaces. Callback
relations can be nondeterministic or have no finite exit. -/
structure WithValuesObservationIndex where
  State : Type
  Left : Type
  Right : Type
  Unwind : Type
  Terminal : Type
  callbacks : ValuesCallbacks State ProgramError.Value Left Right Unwind Terminal

def with_values_observation_contract (index : WithValuesObservationIndex) :
    Solanalib.Contracts.Model index.State (ValuesArgs ProgramError.Value index.Left index.Right)
      Error index.Unwind index.Terminal :=
  withValuesContract index.callbacks

def with_values_observation_family : Family where
  Index := WithValuesObservationIndex
  State := WithValuesObservationIndex.State
  Args := fun index => ValuesArgs ProgramError.Value index.Left index.Right
  Value := fun _ => Error
  Unwind := WithValuesObservationIndex.Unwind
  Terminal := WithValuesObservationIndex.Terminal
  contract := with_values_observation_contract

def with_values_observation_run : FamilyRun with_values_observation_family :=
  fun index => ValuesRun index.callbacks

/-- Universal correctness of the reference relation includes all nine finite
paths, without assuming either conversion or cleanup succeeds. -/
theorem with_values_observation_reference : FamilyReference with_values_observation_family
  with_values_observation_run := by
  intro index
  exact valuesRun_holds index.callbacks

/-- One observed source specialization is `(usize, i32)`. This sample uses
64-bit unsigned values and signed 32-bit values, with explicit pure formatting
and no-op cleanup interfaces. Their Rust implementations are not proved here. -/
def with_values_observation_sample : with_values_observation_family.Index where
  State := Unit
  Left := UInt64
  Right := Int32
  Unwind := Empty
  Terminal := Empty
  callbacks := {
    left := Callback.ofFunction (fun before value => .returned (toString value) before)
    right := Callback.ofFunction (fun before value => .returned (toString value) before)
    normalCleanup := Callback.ofFunction (fun before _ => .returned () before)
    unwindCleanup := Callback.ofFunction (fun before _ => .returned () before) }

private def sampleValues : ValuesArgs ProgramError.Value UInt64 Int32 :=
  ⟨.anchor sampleAnchor, 7, -3⟩

theorem with_values_observation_satisfiable : FamilySatisfiable with_values_observation_family
  with_values_observation_sample :=
  ⟨(), sampleValues, trivial⟩

theorem with_values_observation_has_execution :
    FamilyHasExecution with_values_observation_family with_values_observation_run
      with_values_observation_sample := by
  refine ⟨(), sampleValues, .returned
    (sampleValues.error.replaceCompared
      (.values (toString sampleValues.left) (toString sampleValues.right))) (), trivial, ?_⟩
  exact ValuesRun.returned rfl rfl rfl

def with_values_contract := AnchorErrorOwned.withValuesFamily
def with_values_run := AnchorErrorOwned.withValuesRun
def with_values_sample := AnchorErrorOwned.withValues_sample
theorem with_values_reference : FamilyReference with_values_contract with_values_run :=
  AnchorErrorOwned.withValues_reference
theorem with_values_satisfiable : FamilySatisfiable with_values_contract with_values_sample :=
  AnchorErrorOwned.withValues_satisfiable
theorem with_values_has_execution :
    FamilyHasExecution with_values_contract with_values_run with_values_sample :=
  AnchorErrorOwned.withValues_hasExecution

end Error

end Solanalib.Specs.AnchorLang.error
