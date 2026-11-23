/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplToken2022Interface.FeeReference
public import Solanalib.Specs.SplToken2022Interface.Fees

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SplToken2022Interface.FeeReference

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token
open Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFeeConfig

/-- Separate parent identities and admission make retained-reference tests
independent of equal copied values. The marker tests complete state retention. -/
structure Store where
  /-- Current represented configurations at stable parent indices. -/
  configs : List (Option Token.TransferFeeConfig)
  /-- Existing parent references currently admitted for reads. -/
  liveParents : List Nat
  /-- An unrelated ambient observation preserved by the selector. -/
  marker : Nat
  deriving DecidableEq, Repr

/-- A finite current-state interpretation; no operation creates a borrow. -/
abbrev model : Token.FeeReference.Model where
  State := Store
  Parent := Nat
  access :=
    { live := fun state parent => parent ∈ state.liveParents
      current := fun state parent => (state.configs[parent]?).join }

/-- The older epoch is deliberately later than the newer activation epoch. -/
def config : Token.TransferFeeConfig :=
  ⟨.zero, .zero, 77, ⟨200, 9, 100⟩, ⟨100, 3, 200⟩⟩

/-- Two distinct parents initially have exactly equal contents. -/
def initial : Store := ⟨[some config, some config], [0, 1], 41⟩

/-- A borrowed reference into the first older field. -/
def older0 : Token.FeeReference.Reference Nat := ⟨0, .older⟩

/-- A borrowed reference into the second older field. -/
def older1 : Token.FeeReference.Reference Nat := ⟨1, .older⟩

/-- A borrowed reference into the first newer field. -/
def newer0 : Token.FeeReference.Reference Nat := ⟨0, .newer⟩

/-- The zero epoch and the predecessor of the activation epoch both return
the older field; equality and the largest epoch return the newer field. -/
theorem exact_boundary_executions :
    Token.FeeReference.run model initial ⟨0, 0⟩ (.returned older0 initial) ∧
    Token.FeeReference.run model initial ⟨0, 99⟩ (.returned older0 initial) ∧
    Token.FeeReference.run model initial ⟨0, 100⟩ (.returned newer0 initial) ∧
    Token.FeeReference.run model initial ⟨0, UInt64.ofNat (2^64 - 1)⟩
      (.returned newer0 initial) := by
  constructor
  · exact ⟨config, ⟨by decide, rfl⟩, rfl⟩
  constructor
  · exact ⟨config, ⟨by decide, rfl⟩, rfl⟩
  constructor
  · exact ⟨config, ⟨by decide, rfl⟩, rfl⟩
  · exact ⟨config, ⟨by decide, rfl⟩, rfl⟩

/-- Equal copied values do not collapse the identities of returned fields. -/
theorem equal_values_distinct_parents :
    Token.FeeReference.run model initial ⟨0, 99⟩ (.returned older0 initial) ∧
    Token.FeeReference.run model initial ⟨1, 99⟩ (.returned older1 initial) ∧
    older0 ≠ older1 ∧
    FieldReference.Reads model.access Token.FeeReference.Field.get initial older0 config.older ∧
    FieldReference.Reads model.access Token.FeeReference.Field.get initial older1 config.older := by
  refine ⟨⟨config, ⟨by decide, rfl⟩, rfl⟩,
    ⟨config, ⟨by decide, rfl⟩, rfl⟩, by decide, ?_, ?_⟩
  · exact ⟨by decide, rfl⟩
  · exact ⟨by decide, rfl⟩

/-- The registered contract accepts a concrete full reference execution,
preserving the receiver state including unrelated data and access records. -/
theorem primary_contract_nonempty :
    (get_epoch_fee_live_contract.contract model).HasExecution
      (getEpochFeeLiveReference model) := by
  refine ⟨initial, ⟨0, 100⟩, .returned newer0 initial, ?_, ?_⟩
  · exact ⟨config, by decide, rfl⟩
  · exact ⟨config, ⟨by decide, rfl⟩, rfl⟩

/-- Immediate dereference agrees with the pre-existing copied-value contract. -/
theorem immediate_value_observation :
    get_epoch_fee_contract.ensures config 99 config.older config ∧
    FieldReference.Reads model.access Token.FeeReference.Field.get initial older0 config.older :=
  ⟨⟨rfl, rfl⟩, ⟨by decide, rfl⟩⟩

/-- A later mathematical observation changes both fee values and crosses
the newer epoch. This tests reference liveness; it does not assert that Rust
permits mutation during a shared borrow of this non-interior-mutable type. -/
def changedConfig : Token.TransferFeeConfig :=
  { config with older := ⟨300, 21, 500⟩, newer := ⟨10, 4, 600⟩ }

/-- Only the first parent receives the changed current contents. A source
binding must justify any actual state transition between such observations. -/
def changed : Store := ⟨[some changedConfig, some config], [0, 1], 42⟩

/-- A retained older reference reads the new older contents. A fresh call at
the same epoch selects newer instead; the retained reference never reselects. -/
theorem later_read_without_reselection :
    Token.FeeReference.run model initial ⟨0, 99⟩ (.returned older0 initial) ∧
    FieldReference.Reads model.access Token.FeeReference.Field.get changed older0
      changedConfig.older ∧
    changedConfig.older ≠ config.older ∧
    Token.FeeReference.run model changed ⟨0, 99⟩ (.returned newer0 changed) ∧
    FieldReference.Reads model.access Token.FeeReference.Field.get changed older1 config.older := by
  refine ⟨⟨config, ⟨by decide, rfl⟩, rfl⟩, ⟨by decide, rfl⟩,
    by decide, ⟨changedConfig, ⟨by decide, rfl⟩, rfl⟩, ?_⟩
  exact ⟨by decide, rfl⟩

/-- The same newer reference also reads current contents after a threshold
change that would cause a fresh selector call to return the older field. -/
def delayedConfig : Token.TransferFeeConfig :=
  { config with newer := ⟨250, 25, 700⟩ }

/-- A second state observation retains both parent identities. -/
def delayed : Store := ⟨[some delayedConfig, some config], [0, 1], 43⟩

/-- Both directions of threshold change preserve the originally chosen field. -/
theorem retained_newer_does_not_reselect :
    Token.FeeReference.run model initial ⟨0, 100⟩ (.returned newer0 initial) ∧
    FieldReference.Reads model.access Token.FeeReference.Field.get delayed newer0
      delayedConfig.newer ∧
    Token.FeeReference.run model delayed ⟨0, 100⟩ (.returned older0 delayed) :=
  ⟨⟨config, ⟨by decide, rfl⟩, rfl⟩, ⟨by decide, rfl⟩,
    ⟨delayedConfig, ⟨by decide, rfl⟩, rfl⟩⟩

/-- Stale represented contents remain, but the original borrow is unavailable. -/
def expired : Store := { initial with liveParents := [] }

/-- A stale snapshot cannot bypass the current parent admission. -/
theorem no_read_after_expiry :
    model.access.current expired 0 = some config ∧
    ¬ ∃ value, FieldReference.Reads model.access Token.FeeReference.Field.get
      expired older0 value := by
  refine ⟨rfl, ?_⟩
  rintro ⟨value, read⟩
  exact FieldReference.no_read_of_not_live model.access Token.FeeReference.Field.get
    expired older0 (by simp [model, expired]) value read

/-- Calling the selector cannot manufacture new access to an expired parent. -/
theorem no_execution_after_expiry :
    ¬ ∃ outcome, Token.FeeReference.run model expired ⟨0, 99⟩ outcome := by
  rintro ⟨outcome, execution⟩
  exact Token.FeeReference.no_run_of_not_live model expired ⟨0, 99⟩
    (by simp [expired]) outcome execution

/-- The original identity remains admitted but its value is no longer present. -/
def missing : Store := { initial with configs := [none, some config] }

/-- No saved fee or alternate parent supplies a read after representation loss. -/
theorem no_read_after_representation_loss :
    ¬ ∃ value, FieldReference.Reads model.access Token.FeeReference.Field.get
      missing older0 value := by
  rintro ⟨value, read⟩
  exact FieldReference.no_read_of_missing model.access Token.FeeReference.Field.get
    missing older0 rfl value read

/-- A missing represented parent does not become an invented finite source exit. -/
theorem no_execution_after_representation_loss :
    ¬ ∃ outcome, Token.FeeReference.run model missing ⟨0, 99⟩ outcome := by
  rintro ⟨outcome, execution⟩
  exact Token.FeeReference.no_run_of_missing model missing ⟨0, 99⟩ rfl outcome execution

end SolanalibTest.Specs.SplToken2022Interface.FeeReference
