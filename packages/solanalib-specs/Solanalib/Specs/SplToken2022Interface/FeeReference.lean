/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenFeeReference
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFeeConfig

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token

/-- The full mathematical result of the pinned borrowed-field selector.
The same parent reference and the field selected from its current epoch are
returned with unchanged state. Access and lifetime admission come from the
existing parent borrow; no new guard is acquired or consumed. The ordinary
return profile still requires a source validity and primitive-load binding. -/
def get_epoch_fee_live_contract : Family where
  Index := FeeReference.Model
  State := fun model => model.State
  Args := fun model => FeeReference.Args model.Parent
  Value := fun model => FeeReference.Reference model.Parent
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun model => .returning
    (fun before args => ∃ config, model.access.Reads before args.parent config)
    (fun before args reference after =>
      after = before ∧ reference.parent = args.parent ∧
        ∃ config, model.access.Reads before args.parent config ∧
          FeeReference.Selected config args.epoch reference.field)

/-- A reference relation for every current-state and parent-identity model. -/
def getEpochFeeLiveReference : FamilyRun get_epoch_fee_live_contract :=
  fun model => FeeReference.run model

/-- The source branch description holds for every admitted interpretation. -/
theorem get_epoch_fee_live_reference :
    FamilyReference get_epoch_fee_live_contract getEpochFeeLiveReference := by
  intro model before args outcome _ execution
  obtain ⟨config, read, rfl⟩ := execution
  exact ⟨rfl, rfl, config, read, FeeReference.selectField_selected config args.epoch⟩

/-- A closed mathematical interpretation with one existing parent identity.
It is a nonvacuity sample, not a concrete memory implementation. -/
def getEpochFeeLiveSample : FeeReference.Model where
  State := Token.TransferFeeConfig
  Parent := Unit
  access :=
    { live := fun _ _ => True
      current := fun config _ => some config }

/-- Distinct fee records ensure the sample tests the selected field. -/
def getEpochFeeLiveSampleConfig : Token.TransferFeeConfig :=
  ⟨.zero, .zero, 7, ⟨200, 9, 100⟩, ⟨100, 3, 200⟩⟩

/-- The registered family has an explicit admitted receiver and epoch. -/
theorem get_epoch_fee_live_satisfiable :
    FamilySatisfiable get_epoch_fee_live_contract getEpochFeeLiveSample :=
  ⟨getEpochFeeLiveSampleConfig, ⟨(), 100⟩, getEpochFeeLiveSampleConfig, trivial, rfl⟩

/-- The same registered sample has a real relation execution at the equality
boundary; the reference retains its parent and selects the newer field. -/
theorem get_epoch_fee_live_has_execution :
    FamilyHasExecution get_epoch_fee_live_contract getEpochFeeLiveReference
      getEpochFeeLiveSample := by
  refine ⟨getEpochFeeLiveSampleConfig, ⟨(), 100⟩,
    .returned ⟨(), .newer⟩ getEpochFeeLiveSampleConfig, ?_, ?_⟩
  · exact ⟨getEpochFeeLiveSampleConfig, trivial, rfl⟩
  · exact ⟨getEpochFeeLiveSampleConfig, ⟨trivial, rfl⟩, rfl⟩

/-- The primary contract exposes field identity for any satisfying relation,
independently of the particular mathematical reference implementation. -/
theorem get_epoch_fee_live_selected (model : FeeReference.Model)
    (run : model.State → FeeReference.Args model.Parent →
      Outcome model.State (FeeReference.Reference model.Parent) Empty Empty → Prop)
    (spec : (get_epoch_fee_live_contract.contract model).Holds run)
    (before after : model.State) (args : FeeReference.Args model.Parent)
    (reference : FeeReference.Reference model.Parent)
    (admitted : (get_epoch_fee_live_contract.contract model).requires before args)
    (execution : run before args (.returned reference after)) :
    after = before ∧ reference.parent = args.parent ∧
      ∃ config, model.access.Reads before args.parent config ∧
        FeeReference.Selected config args.epoch reference.field :=
  spec before args (.returned reference after) admitted execution

end Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFeeConfig
