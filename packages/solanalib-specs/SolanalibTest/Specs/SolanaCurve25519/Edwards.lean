/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaCurve25519

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaCurve25519

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.SolanaCurve25519.edwards.target_arch

theorem request_is_edwards_with_initialized_scratch (point : Curve.Point) :
    (Curve.edwardsRequest point).curve = 0 ∧
    (Curve.edwardsRequest point).point = point ∧
    (Curve.edwardsRequest point).initialScratch = 0 := ⟨rfl, rfl, rfl⟩

theorem zero_status_ignores_nonzero_scratch :
    validate_edwards_run validate_edwards_sample (4 : Nat) Curve.samplePoint
      (.returned true (5 : Nat)) :=
  ⟨.returned ⟨0, 255⟩ (5 : Nat), rfl, rfl⟩

/-- A nonzero status with a zero scratch byte. -/
def rejected : ValidationIndex where
  State := Nat
  Unwind := Empty
  Terminal := Empty
  validate := Callback.ofFunction fun calls _ => .returned ⟨9, 0⟩ (calls + 1)

theorem nonzero_status_ignores_zero_scratch :
    validate_edwards_run rejected (4 : Nat) Curve.samplePoint (.returned false (5 : Nat)) :=
  ⟨.returned ⟨9, 0⟩ (5 : Nat), rfl, rfl⟩

/-- A provider that changes state before unwinding. -/
def unwinding : ValidationIndex where
  State := Nat
  Unwind := Unit
  Terminal := Unit
  validate := Callback.ofFunction fun calls _ => .unwound () (calls + 3)

theorem callback_unwind_retains_state :
    validate_edwards_run unwinding (7 : Nat) Curve.samplePoint (.unwound () (10 : Nat)) :=
  ⟨.unwound () (10 : Nat), rfl, rfl⟩

/-- A provider that supplies a terminal exit without a post-state. -/
def terminating : ValidationIndex where
  State := Nat
  Unwind := Unit
  Terminal := Unit
  validate := Callback.ofFunction fun _ _ => .terminated ()

theorem callback_terminal_has_no_post_state :
    validate_edwards_run terminating (7 : Nat) Curve.samplePoint (.terminated ()) :=
  ⟨.terminated (), rfl, rfl⟩

theorem zero_status_cannot_report_false :
    ¬ validate_edwards_run validate_edwards_sample (4 : Nat) Curve.samplePoint
      (.returned false (5 : Nat)) := by
  rintro ⟨intermediate, rfl, impossible⟩
  cases impossible

end SolanalibTest.Specs.SolanaCurve25519
