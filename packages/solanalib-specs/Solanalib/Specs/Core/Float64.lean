/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

import Init.Data.Nat.Log2
public import Solanalib.Runtime.Basic

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.Core.Float64

/-- The complete binary64 bit pattern, including signed zero and nonfinite
inputs. No host floating-point operation is used by this mathematical model. -/
abbrev Bits := UInt64

def fractionUnit : Nat := 2^52
def signUnit : Nat := 2^63
def positiveInfinity : Bits := UInt64.ofNat 0x7ff0000000000000
def quietNaN : Bits := UInt64.ofNat 0x7ff8000000000000

/-- A finite value denotes `(-1)^negative * significand * 2^exponent`.
NaN payloads are deliberately unobserved: the Rent call chain casts the
arithmetic result to an integer, which maps every NaN to zero. -/
inductive Decoded where
  | finite (negative : Bool) (significand : Nat) (exponent : Int)
  | infinite (negative : Bool)
  | nan
  deriving DecidableEq, Repr

def decode (bits : Bits) : Decoded :=
  let negative := decide (signUnit ≤ bits.toNat)
  let exponent := bits.toNat / fractionUnit % 2048
  let fraction := bits.toNat % fractionUnit
  if exponent = 2047 then
    if fraction = 0 then .infinite negative else .nan
  else if exponent = 0 then .finite negative fraction (-1074)
  else .finite negative (fractionUnit + fraction) ((exponent : Int) - 1075)

/-- Round a nonnegative rational quotient to the nearest integer; exact ties
choose the even integer. All call sites supply a positive power of two. -/
def roundQuotient (numerator denominator : Nat) : Nat :=
  let quotient := numerator / denominator
  let twiceRemainder := 2 * (numerator % denominator)
  if twiceRemainder < denominator then quotient
  else if denominator < twiceRemainder then quotient + 1
  else if quotient % 2 = 0 then quotient else quotient + 1

/-- Round the exact dyadic `significand * 2^shift` to an integer. -/
def roundScale (significand : Nat) (shift : Int) : Nat :=
  if 0 ≤ shift then significand * 2^shift.toNat
  else roundQuotient significand (2^(-shift).toNat)

def signedBits (negative : Bool) (magnitude : Nat) : Bits :=
  UInt64.ofNat ((if negative then signUnit else 0) + magnitude)

/-- Binary64 round-to-nearest, ties-to-even for an exact finite dyadic.
The quantum is clamped at `2^-1074` for gradual underflow. A rounded carry
raises the exponent; overflow produces signed infinity. -/
def roundDyadic (negative : Bool) (significand : Nat) (exponent : Int) : Bits :=
  if significand = 0 then signedBits negative 0 else
  let quantum := max (-1074) ((significand.log2 : Int) + exponent - 52)
  let rounded := roundScale significand (exponent - quantum)
  let (coefficient, quantum) :=
    if 2^53 ≤ rounded then (rounded / 2, quantum + 1) else (rounded, quantum)
  if coefficient = 0 then signedBits negative 0
  else if 971 < quantum then signedBits negative positiveInfinity.toNat
  else if coefficient < fractionUnit then signedBits negative coefficient
  else signedBits negative
    ((quantum + 1075).toNat * fractionUnit + (coefficient - fractionUnit))

/-- Conversion of a source `u64` to binary64 performs its own rounding before
the multiplication. This is not a single exact rational multiplication. -/
def fromUInt64 (value : UInt64) : Bits := roundDyadic false value.toNat 0

/-- Rounded binary64 multiplication. Invalid `0 * infinity` and every NaN
input produce a NaN representative; payload/sign choice is not a Rent output. -/
def multiply (left right : Bits) : Bits :=
  match decode left, decode right with
  | .nan, _ | _, .nan => quietNaN
  | .infinite negativeLeft, .infinite negativeRight =>
      signedBits (negativeLeft != negativeRight) positiveInfinity.toNat
  | .infinite negativeLeft, .finite negativeRight coefficient _ =>
      if coefficient = 0 then quietNaN
      else signedBits (negativeLeft != negativeRight) positiveInfinity.toNat
  | .finite negativeLeft coefficient _, .infinite negativeRight =>
      if coefficient = 0 then quietNaN
      else signedBits (negativeLeft != negativeRight) positiveInfinity.toNat
  | .finite negativeLeft coefficientLeft exponentLeft,
      .finite negativeRight coefficientRight exponentRight =>
      roundDyadic (negativeLeft != negativeRight)
        (coefficientLeft * coefficientRight) (exponentLeft + exponentRight)

/-- Floor of a nonnegative finite dyadic. -/
def floorDyadic (significand : Nat) (exponent : Int) : Nat :=
  if 0 ≤ exponent then significand * 2^exponent.toNat
  else significand / 2^(-exponent).toNat

/-- The saturating Rust conversion `f64 as u64`: NaN and negative values yield zero;
positive infinity and out-of-range values yield `u64::MAX`; finite values
truncate toward zero. -/
def toUInt64 (bits : Bits) : UInt64 :=
  match decode bits with
  | .nan => 0
  | .infinite negative => if negative then 0 else UInt64.ofNat Solanalib.Runtime.U64_MAX
  | .finite negative coefficient exponent =>
      if negative then 0
      else UInt64.ofNat (min Solanalib.Runtime.U64_MAX (floorDyadic coefficient exponent))

/-- The exact operation order used after the source integer arithmetic of Rent. -/
def multiplyUInt64ThenCast (integer : UInt64) (threshold : Bits) : UInt64 :=
  toUInt64 (multiply (fromUInt64 integer) threshold)

theorem roundQuotient_below_half (numerator denominator : Nat)
    (below : 2 * (numerator % denominator) < denominator) :
    roundQuotient numerator denominator = numerator / denominator := by
  simp only [roundQuotient, below, ite_true]

theorem roundQuotient_above_half (numerator denominator : Nat)
    (above : denominator < 2 * (numerator % denominator)) :
    roundQuotient numerator denominator = numerator / denominator + 1 := by
  have notBelow : ¬ 2 * (numerator % denominator) < denominator := by omega
  simp only [roundQuotient, notBelow, ite_false, above, ite_true]

theorem roundQuotient_tie_even (numerator denominator : Nat)
    (tie : 2 * (numerator % denominator) = denominator)
    (even : numerator / denominator % 2 = 0) :
    roundQuotient numerator denominator = numerator / denominator := by
  simp only [roundQuotient, tie, Nat.lt_irrefl, ite_false, even, ite_true]

theorem roundQuotient_tie_odd (numerator denominator : Nat)
    (tie : 2 * (numerator % denominator) = denominator)
    (odd : numerator / denominator % 2 ≠ 0) :
    roundQuotient numerator denominator = numerator / denominator + 1 := by
  simp only [roundQuotient, tie, Nat.lt_irrefl, ite_false, odd]

theorem cast_negative_finite (bits : Bits) (coefficient : Nat) (exponent : Int)
    (decoded : decode bits = .finite true coefficient exponent) :
    toUInt64 bits = 0 := by simp only [toUInt64, decoded, ite_true]

theorem cast_nan (bits : Bits) (decoded : decode bits = .nan) :
    toUInt64 bits = 0 := by simp only [toUInt64, decoded]

theorem cast_positive_infinity (bits : Bits) (decoded : decode bits = .infinite false) :
    toUInt64 bits = UInt64.ofNat Solanalib.Runtime.U64_MAX := by
  simp only [toUInt64, decoded, Bool.false_eq_true, ite_false]

end Solanalib.Specs.Core.Float64
