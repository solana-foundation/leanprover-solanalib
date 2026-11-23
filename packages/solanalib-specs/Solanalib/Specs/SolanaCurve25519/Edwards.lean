/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Curve
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaCurve25519.edwards.target_arch

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The explicit syscall provider of the Solana target. A host decompression path is
a different interpretation; this family never substitutes that path. -/
structure ValidationIndex where
  /-- State observed and changed by the syscall provider. -/
  State : Type
  /-- Provider-specific unwind reasons. -/
  Unwind : Type
  /-- Provider-specific terminal reasons. -/
  Terminal : Type
  /-- The explicit finite-exit validation provider. -/
  validate : Callback.Run State Curve.ValidationRequest Curve.ValidationReply Unwind Terminal

/-- The complete status-based wrapper contract for every provider instance. -/
def validate_edwards_contract : Family where
  Index := ValidationIndex
  State := ValidationIndex.State
  Args := fun _ => Curve.Point
  Value := fun _ => Bool
  Unwind := ValidationIndex.Unwind
  Terminal := ValidationIndex.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := Curve.validationPost index.validate
  }

/-- The common callback mapper instantiated by the selected SDK family. -/
def validate_edwards_run : FamilyRun validate_edwards_contract :=
  fun index => Curve.validateEdwards index.validate

theorem validate_edwards_reference :
    FamilyReference validate_edwards_contract validate_edwards_run := by
  intro index before point outcome _ step
  exact Curve.validateEdwards_post index.validate before point outcome step

/-- A provider that changes state and disagrees between status and scratch. -/
def validate_edwards_sample : ValidationIndex where
  State := Nat
  Unwind := Empty
  Terminal := Empty
  validate := Callback.ofFunction fun calls _ => .returned ⟨0, 255⟩ (calls + 1)

theorem validate_edwards_hasExecution :
    FamilyHasExecution validate_edwards_contract validate_edwards_run
      validate_edwards_sample := by
  refine ⟨(0 : Nat), Curve.samplePoint, .returned true (1 : Nat), trivial, ?_⟩
  exact ⟨.returned ⟨0, 255⟩ (1 : Nat), rfl, rfl⟩

theorem validate_edwards_satisfiable :
    FamilySatisfiable validate_edwards_contract validate_edwards_sample :=
  validate_edwards_hasExecution.satisfiable

end Solanalib.Specs.SolanaCurve25519.edwards.target_arch
