/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OraclePyth

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.PythSolanaReceiverSdk.price_update.PriceUpdateV2

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Oracle

/-- A framed world and the selected Rust panic strategy. -/
structure GetterIndex where
  /-- Ambient state framed by this immutable getter. -/
  State : Type
  /-- Whether an unwrapped conversion failure aborts instead of unwinding. -/
  aborts : Bool

/-- The value checks of the pinned getter and every finite error/panic exit. The
mathematical operation is total on canonical clocks; Rust clock widths,
account deserialization and ownership are separate interpretation obligations. -/
def get_price_no_older_than_with_custom_verification_level_contract : Family where
  Index := GetterIndex
  State := GetterIndex.State
  Args := fun _ => Pyth.Args
  Value := fun _ => Except Pyth.GetPriceError Pyth.Price
  Unwind := fun _ => Pyth.Panic
  Terminal := fun _ => Pyth.Panic
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before args outcome => outcome = Pyth.run index.aborts before args
  }

/-- The computed reference is parameterized by the full framed state type. -/
def get_price_no_older_than_with_custom_verification_level_run :
    FamilyRun get_price_no_older_than_with_custom_verification_level_contract :=
  fun index before args outcome => outcome = Pyth.run index.aborts before args

/-- Universal reference correctness covers either panic strategy. -/
theorem get_price_no_older_than_with_custom_verification_level_reference :
    FamilyReference get_price_no_older_than_with_custom_verification_level_contract
      get_price_no_older_than_with_custom_verification_level_run :=
  fun _ _ _ _ _ execution => execution

/-- The concrete witness uses a nontrivial framed state and an aborting target. -/
def get_price_no_older_than_with_custom_verification_level_sample : GetterIndex :=
  ⟨Nat, true⟩

/-- A permitted execution returns the nonzero sample price at the age boundary. -/
theorem get_price_no_older_than_with_custom_verification_level_hasExecution :
    FamilyHasExecution get_price_no_older_than_with_custom_verification_level_contract
      get_price_no_older_than_with_custom_verification_level_run
      get_price_no_older_than_with_custom_verification_level_sample := by
  refine ⟨(7 : Nat), Pyth.sampleArgs,
    .returned (.ok Pyth.sampleUpdate.message.toPrice) (7 : Nat), ?_, ?_⟩
  · trivial
  · rfl

/-- The same concrete permitted execution witnesses a nonempty precondition. -/
theorem get_price_no_older_than_with_custom_verification_level_satisfiable :
    FamilySatisfiable get_price_no_older_than_with_custom_verification_level_contract
      get_price_no_older_than_with_custom_verification_level_sample :=
  get_price_no_older_than_with_custom_verification_level_hasExecution.satisfiable

end Solanalib.Specs.PythSolanaReceiverSdk.price_update.PriceUpdateV2
