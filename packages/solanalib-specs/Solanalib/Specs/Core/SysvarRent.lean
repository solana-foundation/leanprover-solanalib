/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.ProgramError
public import Solanalib.Runtime.Sysvar

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Sysvar

/-- Pinocchio 0.11.1 removed the threshold field. Its Rust value is eight bytes. -/
structure Rent111 where
  lamportsPerByte : UInt64
  deriving DecidableEq, Repr

def Rent111.encode (rent : Rent111) : Solanalib.Runtime.Bytes := Solanalib.Runtime.u64le
  rent.lamportsPerByte.toNat

def maxDataLength : Nat := 10 * 1024 * 1024
def storageOverhead : Nat := 128
def simdMaxRate : Nat := 1759197129867
/-- The 0.11.1 integer bound is independent of any floating threshold. -/
def rent111Try (rent : Rent111) (dataLength : UInt64) : Except ProgramError.Value UInt64 :=
  if maxDataLength < dataLength.toNat then .error .invalidArgument
  else if simdMaxRate < rent.lamportsPerByte.toNat then .error .invalidArgument
  else .ok (UInt64.ofNat ((storageOverhead + dataLength.toNat) * rent.lamportsPerByte.toNat))

theorem rent111_product_fits (rent : Rent111) (dataLength : UInt64)
    (dataBound : dataLength.toNat ≤ maxDataLength)
    (rateBound : rent.lamportsPerByte.toNat ≤ simdMaxRate) :
    (storageOverhead + dataLength.toNat) * rent.lamportsPerByte.toNat < Solanalib.Runtime.U64_LIMIT
      := by
  have productBound := Nat.mul_le_mul
    (Nat.add_le_add_left dataBound storageOverhead) rateBound
  have limit : (storageOverhead + maxDataLength) * simdMaxRate < Solanalib.Runtime.U64_LIMIT := by
    decide
  exact Nat.lt_of_le_of_lt productBound limit

@[simp] theorem rent111_encode_length (rent : Rent111) : rent.encode.length = 8 := by
  simp [Rent111.encode, Solanalib.Runtime.u64le]

end Solanalib.Specs.Core.Sysvar
