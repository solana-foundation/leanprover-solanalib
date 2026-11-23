/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionAllocated
public import Solanalib.Specs.Core.TokenInstructionVariants
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.InstructionAllocated

/-- Instantiate the operational engine with the program check, data plan and metadata plan of a
versioned constructor. -/
def family (Args : Type) (plan : Args → Plan) : Family where
  Index := Types
  State := Types.State
  Args := fun _ => Args
  Value := fun types => Except Error (Value types)
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun state args => run types state (plan args) }

/-- The generic reference traverses the actual dependency sequence. -/
def reference (Args : Type) (plan : Args → Plan) :
    FamilyRun (family Args plan) :=
  fun types state args => run types state (plan args)

/-- Reference correctness holds for every dependency interpretation, not only
for the concrete witness heap. -/
theorem reference_holds (Args : Type) (plan : Args → Plan) :
    FamilyReference (family Args plan) (reference Args plan) := by
  intro _ _ _ _ _ execution
  exact execution

end Solanalib.Specs.Core.Token.InstructionAllocated
