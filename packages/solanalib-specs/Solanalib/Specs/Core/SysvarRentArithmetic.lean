/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.SysvarRent
public import Solanalib.Specs.Core.Float64

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Sysvar

/-- Solana Rent 3.0.0 retains the floating threshold and burn field. Widths are
part of this value type; the arithmetic never substitutes the fixed canonical
runtime rent profile for arbitrary threshold bits. -/
structure Rent300 where
  lamportsPerByteYear : UInt64
  thresholdBits : Float64.Bits
  burnPercent : UInt8
  deriving DecidableEq, Repr

def Rent300.toCanonical (rent : Rent300) : Solanalib.Runtime.RentSysvar :=
  ⟨rent.lamportsPerByteYear.toNat, rent.thresholdBits.toNat, rent.burnPercent.toNat⟩

def Rent300.prefix111 (rent : Rent300) : Rent111 := ⟨rent.lamportsPerByteYear⟩

def defaultRent300 : Rent300 := ⟨3480, 0x4000000000000000, 50⟩

def thresholdOne : Float64.Bits := 0x3ff0000000000000
def thresholdTwo : Float64.Bits := 0x4000000000000000

inductive Panic where
  | additionOverflow
  | multiplicationOverflow
  | bpfFloatingPoint
  deriving DecidableEq, Repr

inductive PanicStrategy where
  | unwind
  | abort
  deriving DecidableEq, Repr

/-- The recorded source build selects wrapping or checked integer operations,
and its panic strategy. These are model-environment choices, not Rust arguments. -/
structure ArithmeticProfile where
  overflowChecks : Bool
  panicStrategy : PanicStrategy
  deriving DecidableEq, Repr

def ArithmeticProfile.release : ArithmeticProfile := ⟨false, .abort⟩
def ArithmeticProfile.checked : ArithmeticProfile := ⟨true, .abort⟩

def arithmetic (profile : ArithmeticProfile) (reason : Panic) (value : Nat) :
    Except Panic UInt64 :=
  if profile.overflowChecks && decide (Solanalib.Runtime.U64_LIMIT ≤ value) then .error reason
  else .ok (UInt64.ofNat value)

def add (profile : ArithmeticProfile) (left right : UInt64) : Except Panic UInt64 :=
  arithmetic profile .additionOverflow (left.toNat + right.toNat)

def mul (profile : ArithmeticProfile) (left right : UInt64) : Except Panic UInt64 :=
  arithmetic profile .multiplicationOverflow (left.toNat * right.toNat)

/-- Solana Rent 3.0.0: integer addition, integer multiplication, rounded u64 to
binary64 conversion, rounded multiplication, then the saturating cast of Rust. -/
def rent300Minimum (profile : ArithmeticProfile) (rent : Rent300) (dataLength : UInt64) :
    Except Panic UInt64 := do
  let bytes ← add profile 128 dataLength
  let integer ← mul profile bytes rent.lamportsPerByteYear
  pure (Float64.multiplyUInt64ThenCast integer rent.thresholdBits)

/-- Turn an arithmetic panic into the selected source panic exit. State is
preserved on normal return and unwind; no post-state is invented for abort. -/
def arithmeticOutcome {State Value : Type} (strategy : PanicStrategy)
    (state : State) (result : Except Panic Value) : Outcome State Value Panic Panic :=
  match result with
  | .ok value => .returned value state
  | .error reason => match strategy with
    | .unwind => .unwound reason state
    | .abort => .terminated reason


end Solanalib.Specs.Core.Sysvar
