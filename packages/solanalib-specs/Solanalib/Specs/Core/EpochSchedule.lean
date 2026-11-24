/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.SysvarSdk

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.EpochSchedule

/-- All public source fields, including arbitrary schedules not constructed by
`custom`. No consistency invariant is required by the slot-query functions. -/
structure Value where
  slotsPerEpoch : UInt64
  leaderScheduleSlotOffset : UInt64
  warmup : Bool
  firstNormalEpoch : UInt64
  firstNormalSlot : UInt64
  deriving DecidableEq, Repr

/-- The exact default reached by the typed SDK getter. -/
def defaultValue : Value := ⟨432000, 432000, true, 14, 524256⟩

def saturate (value : Nat) : UInt64 := UInt64.ofNat (min value (2^64 - 1))
def add (left right : UInt64) : UInt64 := saturate (left.toNat + right.toNat)
def mul (left right : UInt64) : UInt64 := saturate (left.toNat * right.toNat)
def sub (left right : UInt64) : UInt64 := UInt64.ofNat (left.toNat - right.toNat)

/-- Saturating exponentiation, bounded before evaluating a potentially huge
power. The caller first performs the truncating `as u32` cast in the source. -/
def powTwo (exponent : UInt32) : UInt64 :=
  if exponent.toNat < 64 then UInt64.ofNat (2^exponent.toNat) else UInt64.ofNat (2^64 - 1)

/-- The boundary uses `<=`, even when arbitrary public fields make it differ
from the first-normal-slot field. The `warmup` field is not consulted. -/
def firstSlot (schedule : Value) (epoch : UInt64) : UInt64 :=
  if epoch ≤ schedule.firstNormalEpoch then
    mul (sub (powTwo (UInt32.ofNat epoch.toNat)) 1) 32
  else add (mul (sub epoch schedule.firstNormalEpoch) schedule.slotsPerEpoch)
    schedule.firstNormalSlot

def slotsInEpoch (schedule : Value) (epoch : UInt64) : UInt64 :=
  if epoch < schedule.firstNormalEpoch then
    powTwo (UInt32.ofNat (min ((UInt32.ofNat epoch.toNat).toNat + 5) (2^32 - 1)))
  else schedule.slotsPerEpoch

/-- Saturate the addition before subtracting one. In particular an overflowing
sum returns `u64::MAX - 1`, not `u64::MAX`. -/
def lastSlot (schedule : Value) (epoch : UInt64) : UInt64 :=
  sub (add (firstSlot schedule epoch) (slotsInEpoch schedule epoch)) 1

theorem firstSlot_warmup (schedule : Value) (epoch : UInt64)
    (beforeNormal : epoch ≤ schedule.firstNormalEpoch) :
    firstSlot schedule epoch = mul (sub (powTwo (UInt32.ofNat epoch.toNat)) 1) 32 := by
  simp only [firstSlot, beforeNormal, ite_true]

theorem firstSlot_normal (schedule : Value) (epoch : UInt64)
    (afterNormal : ¬ epoch ≤ schedule.firstNormalEpoch) :
    firstSlot schedule epoch =
      add (mul (sub epoch schedule.firstNormalEpoch) schedule.slotsPerEpoch)
        schedule.firstNormalSlot := by
  simp only [firstSlot, afterNormal, ite_false]

/-- A typed getter starts from the actual default, preserving partial writes
and mapping every nonzero status to UnsupportedSysvar in SDK 3.1.1. -/
def getterConfig : Sysvar.GetterConfig Value where
  request := ⟨.typed .epochSchedule, some defaultValue⟩
  valid := fun _ => True
  error := Sysvar.typedError

end Solanalib.Specs.Core.EpochSchedule
