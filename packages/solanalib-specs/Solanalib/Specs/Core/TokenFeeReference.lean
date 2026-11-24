/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.FieldReference
public import Solanalib.Specs.Core.TokenFee

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.FeeReference

/-- The two fields returned by the pinned transfer-fee selector. These are
symbolic source fields; physical offsets require a separate layout binding. -/
inductive Field where
  /-- The source `older_transfer_fee` field. -/
  | older
  /-- The source `newer_transfer_fee` field. -/
  | newer
  deriving DecidableEq, Repr

/-- Dereference the already selected field without redoing epoch selection. -/
def Field.get : Field → TransferFeeConfig → TransferFee
  | .older, config => config.older
  | .newer, config => config.newer

/-- The source compares against the current newer activation epoch only. -/
def selectField (config : TransferFeeConfig) (epoch : UInt64) : Field :=
  if config.newer.epoch.toNat ≤ epoch.toNat then .newer else .older

/-- Independent branch description of the returned field identity. -/
def Selected (config : TransferFeeConfig) (epoch : UInt64) (field : Field) : Prop :=
  (config.newer.epoch.toNat ≤ epoch.toNat ∧ field = .newer) ∨
    (epoch.toNat < config.newer.epoch.toNat ∧ field = .older)

/-- The mathematical selector satisfies the exact source comparison. -/
theorem selectField_selected (config : TransferFeeConfig) (epoch : UInt64) :
    Selected config epoch (selectField config epoch) := by
  by_cases after : config.newer.epoch.toNat ≤ epoch.toNat
  · exact Or.inl ⟨after, by simp [selectField, after]⟩
  · exact Or.inr ⟨Nat.lt_of_not_ge after, by simp [selectField, after]⟩

/-- At the call state, reading the selected field recovers the frozen value
observation. The returned reference itself contains neither value nor epoch. -/
theorem selected_value (config : TransferFeeConfig) (epoch : UInt64) :
    (selectField config epoch).get config = config.getEpochFee epoch := by
  unfold selectField TransferFeeConfig.getEpochFee
  split <;> rfl

/-- The source receiver is an existing parent reference, followed by epoch. -/
structure Args (Parent : Type) where
  /-- Identity of the borrowed configuration passed as `self`. -/
  parent : Parent
  /-- The requested epoch, copied by value. -/
  epoch : UInt64
  deriving DecidableEq, Repr

/-- A full field-reference result preserves parent identity and field choice. -/
abbrev Reference (Parent : Type) := FieldReference Parent Field

/-- Generic state and parent-reference interpretation for the source model.
Current admission and decoded observations require an external source binding;
this record does not acquire, release or transform an existing borrow guard. -/
structure Model where
  /-- Ambient state containing current configurations and access information. -/
  State : Type
  /-- Identities of already borrowed configurations. -/
  Parent : Type
  /-- Current reads through those existing references. -/
  access : FieldReference.Access State Parent TransferFeeConfig

/-- Ordinary `get_epoch_fee` control flow after valid source reads are admitted.
The method compares one current epoch and returns a derived field reference
without changing state. A missing or inaccessible representation supplies no
execution; it is not an additional source error or panic branch. -/
def run (model : Model) (before : model.State) (args : Args model.Parent)
    (outcome : Outcome model.State (Reference model.Parent) Empty Empty) : Prop :=
  ∃ config, model.access.Reads before args.parent config ∧
    outcome = .returned ⟨args.parent, selectField config args.epoch⟩ before

/-- Every admitted parent read produces its actual selected field reference. -/
theorem run_returned (model : Model) (before : model.State) (args : Args model.Parent)
    (config : TransferFeeConfig) (read : model.access.Reads before args.parent config) :
    run model before args (.returned ⟨args.parent, selectField config args.epoch⟩ before) :=
  ⟨config, read, rfl⟩

/-- Return characterization retains the original parent and unchanged state,
and uses the current configuration at the source comparison. -/
theorem run_returned_iff (model : Model) (before after : model.State)
    (args : Args model.Parent) (reference : Reference model.Parent) :
    run model before args (.returned reference after) ↔
      ∃ config, model.access.Reads before args.parent config ∧
        reference = ⟨args.parent, selectField config args.epoch⟩ ∧ after = before := by
  constructor
  · rintro ⟨config, read, equal⟩
    cases equal
    exact ⟨config, read, rfl, rfl⟩
  · rintro ⟨config, read, rfl, stateEq⟩
    subst after
    exact run_returned model before args config read

/-- The first permitted read through a returned reference agrees with the
existing copied-value observation, while retaining the actual parent identity. -/
theorem run_observation (model : Model) (before after : model.State)
    (args : Args model.Parent) (reference : Reference model.Parent)
    (execution : run model before args (.returned reference after)) :
    ∃ config, model.access.Reads before args.parent config ∧
      reference.parent = args.parent ∧ after = before ∧
      FieldReference.Reads model.access Field.get after reference (config.getEpochFee args.epoch)
        := by
  obtain ⟨config, read, rfl, stateEq⟩ := (run_returned_iff model before after args reference).1
    execution
  subst after
  refine ⟨config, read, rfl, rfl, ?_⟩
  rw [← selected_value]
  exact FieldReference.reads_of_parent model.access Field.get before
    ⟨args.parent, selectField config args.epoch⟩ config read

/-- An expired parent does not acquire a replacement reference by calling
this selector; source validity must come from the existing borrow. -/
theorem no_run_of_not_live (model : Model) (before : model.State)
    (args : Args model.Parent) (notLive : ¬ model.access.live before args.parent) :
    ∀ outcome, ¬ run model before args outcome := by
  rintro outcome ⟨config, read, _⟩
  exact notLive read.1

/-- A missing current parent cannot yield a fabricated field reference. -/
theorem no_run_of_missing (model : Model) (before : model.State)
    (args : Args model.Parent) (missing : model.access.current before args.parent = none) :
    ∀ outcome, ¬ run model before args outcome := by
  rintro outcome ⟨config, read, _⟩
  simpa [missing] using read.2

end Solanalib.Specs.Core.Token.FeeReference
