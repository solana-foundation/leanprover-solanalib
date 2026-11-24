/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Log
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.SdkLog

inductive Target where
  | solana
  | hostStub
  deriving DecidableEq, Repr

/-- Legacy host paths call a replaceable SyscallStubs object. They are not
unconditionally stdout. Compute-unit logging has no fabricated integer return. -/
inductive Request where
  | text (target : Target) (message : String)
  | computeUnits (target : Target)
  deriving DecidableEq, Repr

structure Index where
  State : Type
  Unwind : Type
  Terminal : Type
  target : Target
  sink : Callback.Run State Request Unit Unwind Terminal

def textFamily : Family where
  Index := Index
  State := Index.State
  Args := fun _ => String
  Value := fun _ => Unit
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before message => index.sink before (.text index.target message)
  }

def computeFamily : Family where
  Index := Index
  State := Index.State
  Args := fun _ => Unit
  Value := fun _ => Unit
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before _ => index.sink before (.computeUnits index.target)
  }

def textReference : FamilyRun textFamily :=
  fun index before message => index.sink before (.text index.target message)
def computeReference : FamilyRun computeFamily :=
  fun index before _ => index.sink before (.computeUnits index.target)

theorem text_reference : FamilyReference textFamily textReference := by
  intro _ _ _ _ _ called
  exact called

theorem compute_reference : FamilyReference computeFamily computeReference := by
  intro _ _ _ _ _ called
  exact called

def sample : Index where
  State := List Request
  Unwind := String
  Terminal := String
  target := .solana
  sink := Callback.ofFunction fun before request => .returned () (before ++ [request])

theorem text_hasExecution : FamilyHasExecution textFamily textReference sample :=
  ⟨[], "hello", .returned () [.text .solana "hello"], True.intro, rfl⟩

theorem compute_hasExecution : FamilyHasExecution computeFamily computeReference sample :=
  ⟨[], (), .returned () [.computeUnits .solana], True.intro, rfl⟩

end Solanalib.Specs.Core.SdkLog
