/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressSyscall
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Address.Syscall

/-- Model types for the selected Solana syscall and panic finite exits. -/
structure Types where
  State : Type
  Unwind : Type
  Terminal : Type

structure TryCall (types : Types) where
  inputs : PdaInputs
  syscall : Callback.Run types.State PdaRequest PdaReply types.Unwind types.Terminal

structure FindCall (types : Types) extends TryCall types where
  panic : Callback.Run types.State SearchPanic Empty types.Unwind types.Terminal

structure CurveCall (types : Types) where
  address : Value
  syscall : Callback.Run types.State CurveRequest UInt64 types.Unwind types.Terminal

/-- The selected-target wrapper admits providers whose actual status-zero
replies initialize the address. This is exactly the local decoding obligation. -/
def tryFamily : Family where
  Index := Types
  State := Types.State
  Args := TryCall
  Value := fun _ => Option (Address.Value × UInt8)
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun _ => {
    requires := fun before args => SuccessInitialized args.syscall before args.inputs
    post := fun before args => tryPost args.syscall before args.inputs }

def tryFamilyRun : FamilyRun tryFamily :=
  fun _ before args => tryRun args.syscall before args.inputs

theorem tryFamilyReference : FamilyReference tryFamily tryFamilyRun := by
  intro _ before args outcome _ execution
  exact tryRun_post args.syscall before args.inputs outcome execution

/-- The local find wrapper uses the same initialization admission. Its panic
site is reached only after returned None; panic execution remains explicit. -/
def findFamily : Family where
  Index := Types
  State := Types.State
  Args := FindCall
  Value := fun _ => Address.Value × UInt8
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun _ => {
    requires := fun before args => SuccessInitialized args.syscall before args.inputs
    post := fun before args => findPost args.syscall args.panic before args.inputs }

def findFamilyRun : FamilyRun findFamily :=
  fun _ before args => findRun args.syscall args.panic before args.inputs

theorem findFamilyReference : FamilyReference findFamily findFamilyRun := by
  intro _ before args outcome _ execution
  exact findRun_post args.syscall args.panic before args.inputs outcome execution

/-- Address::is_on_curve on the selected Solana profile forwards the finite exits of the null-
output syscall. No arbitrary generic AsRef is introduced. -/
def curveFamily : Family where
  Index := Types
  State := Types.State
  Args := CurveCall
  Value := fun _ => Bool
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun _ => {
    requires := fun _ _ => True
    post := fun before args => curvePost args.syscall before args.address }

def curveFamilyRun : FamilyRun curveFamily :=
  fun _ before args => curveRun args.syscall before args.address

theorem curveFamilyReference : FamilyReference curveFamily curveFamilyRun := by
  intro _ before args outcome _ execution
  exact curveRun_post args.syscall before args.address outcome execution

end Solanalib.Specs.Core.Address.Syscall
