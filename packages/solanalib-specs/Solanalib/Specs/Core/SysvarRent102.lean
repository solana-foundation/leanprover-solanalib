/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.SysvarRentArithmetic

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Sysvar

/-- The two-field Pinocchio 0.10.2 representation, with the threshold retained
as its exact little-endian binary64 bits. -/
structure Rent102 where
  lamportsPerByte : UInt64
  thresholdBits : Float64.Bits
  deriving DecidableEq, Repr

def Rent300.prefix102 (rent : Rent300) : Rent102 :=
  ⟨rent.lamportsPerByteYear, rent.thresholdBits⟩

def Rent102.encode (rent : Rent102) : Solanalib.Runtime.Bytes :=
  Solanalib.Runtime.u64le rent.lamportsPerByte.toNat ++ Solanalib.Runtime.u64le
    rent.thresholdBits.toNat

def currentMaxRate : Nat := 879598564933
structure PinocchioProfile where
  arithmetic : ArithmeticProfile
  targetBpf : Bool
  deriving DecidableEq, Repr

def PinocchioProfile.release : PinocchioProfile := ⟨.release, false⟩

/-- Preserve the threshold branches and operation order of the source. In the BPF
floating branch the panic occurs without evaluating the absent arithmetic. -/
def rent102Unchecked (profile : PinocchioProfile) (rent : Rent102) (dataLength : UInt64) :
    Except Panic UInt64 :=
  if rent.thresholdBits = thresholdOne then do
    let bytes ← add profile.arithmetic 128 dataLength
    mul profile.arithmetic bytes rent.lamportsPerByte
  else if rent.thresholdBits = thresholdTwo then do
    let bytes ← add profile.arithmetic 128 dataLength
    let twice ← mul profile.arithmetic 2 bytes
    mul profile.arithmetic twice rent.lamportsPerByte
  else if profile.targetBpf then .error .bpfFloatingPoint
  else do
    let bytes ← add profile.arithmetic 128 dataLength
    let integer ← mul profile.arithmetic bytes rent.lamportsPerByte
    pure (Float64.multiplyUInt64ThenCast integer rent.thresholdBits)

/-- The 0.10.2 guards are kept in their source order. The second rate guard
is unreachable, since the first threshold is smaller; it is not repaired here. -/
def rent102Rejected (rent : Rent102) (dataLength : UInt64) : Bool :=
  if maxDataLength < dataLength.toNat then true
  else if currentMaxRate < rent.lamportsPerByte.toNat then
    rent.thresholdBits == thresholdTwo
  else if simdMaxRate < rent.lamportsPerByte.toNat then
    rent.thresholdBits == thresholdOne
  else false

def rent102Try (profile : PinocchioProfile) (rent : Rent102) (dataLength : UInt64) :
    Except Panic (Except ProgramError.Value UInt64) :=
  if rent102Rejected rent dataLength then .ok (.error .invalidArgument)
  else (rent102Unchecked profile rent dataLength).map Except.ok

theorem rent102_second_rate_guard_unreachable (rate : UInt64)
    (firstFalse : ¬ currentMaxRate < rate.toNat) : ¬ simdMaxRate < rate.toNat := by
  unfold currentMaxRate at firstFalse
  unfold simdMaxRate
  omega

@[simp] theorem rent102_encode_length (rent : Rent102) : rent.encode.length = 16 := by
  simp [Rent102.encode, Solanalib.Runtime.u64le]


end Solanalib.Specs.Core.Sysvar
