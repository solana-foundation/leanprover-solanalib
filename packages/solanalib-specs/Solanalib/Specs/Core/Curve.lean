/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback
public import Solanalib.Runtime.Prims

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Curve

universe u v w

/-- The selected Edwards API receives exactly 32 encoded point bytes. -/
abbrev Point := { bytes : Solanalib.Runtime.Bytes // bytes.length = 32 }

/-- The mathematical syscall request includes the initialized output byte.
Its addresses and physical allocation remain interpretation obligations. -/
structure ValidationRequest where
  /-- The curve selector of the syscall; Edwards is zero. -/
  curve : UInt64
  /-- The complete encoded Edwards point. -/
  point : Point
  /-- Contents of the one-byte output before calling the provider. -/
  initialScratch : UInt8

/-- The separate return register and final output byte of the provider. -/
structure ValidationReply where
  /-- Zero denotes a successful point validation. -/
  status : UInt64
  /-- This byte is not inspected by the selected SDK wrapper. -/
  scratch : UInt8
  deriving DecidableEq, Repr

/-- Construct the exact curve selector and initialized destination. -/
def edwardsRequest (point : Point) : ValidationRequest := ⟨0, point, 0⟩

/-- The selected Solana source path tests the status register, not the scratch
byte. Every state change and non-returning finite exit belongs to the provider. -/
def validateEdwards {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (validate : Callback.Run State ValidationRequest ValidationReply Unwind Terminal) :
    Callback.Run State Point Bool Unwind Terminal :=
  fun before point => Callback.map (fun reply => reply.status == 0)
    validate before (edwardsRequest point)

/-- Characterize each forwarded exit independently of the reference mapper. -/
def validationPost {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (validate : Callback.Run State ValidationRequest ValidationReply Unwind Terminal)
    (before : State) (point : Point) (outcome : Outcome State Bool Unwind Terminal) : Prop :=
  match outcome with
  | .returned value after =>
      ∃ reply, validate before (edwardsRequest point) (.returned reply after) ∧
        value = (reply.status == 0)
  | .unwound reason after => validate before (edwardsRequest point) (.unwound reason after)
  | .terminated reason => validate before (edwardsRequest point) (.terminated reason)

theorem validateEdwards_post {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (validate : Callback.Run State ValidationRequest ValidationReply Unwind Terminal)
    (before : State) (point : Point) (outcome : Outcome State Bool Unwind Terminal)
    (step : validateEdwards validate before point outcome) :
    validationPost validate before point outcome := by
  obtain ⟨intermediate, source, rfl⟩ := step
  cases intermediate with
  | returned reply after => exact ⟨reply, source, rfl⟩
  | unwound reason after => exact source
  | terminated reason => exact source

/-- The canonical admitted Edwards primitive reports validation in its status.
This does not discharge syscall admission, feature, metering or memory checks. -/
def primitiveReply (primitives : Solanalib.Runtime.Prims) (point : Point) : ValidationReply :=
  ⟨if primitives.validatePoint 0 point.val then 0 else 1, 0⟩

theorem primitiveReply_status (primitives : Solanalib.Runtime.Prims) (point : Point) :
    ((primitiveReply primitives point).status == 0) = primitives.onCurve point.val := by
  simp only [primitiveReply, Solanalib.Runtime.Prims.validatePoint_edwards]
  cases primitives.onCurve point.val <;> rfl

/-- A concrete point encoding for model nonvacuity, without a validity claim. -/
def samplePoint : Point := ⟨List.replicate 32 0, by simp⟩

end Solanalib.Specs.Core.Curve
