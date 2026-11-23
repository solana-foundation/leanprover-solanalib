/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionBuilder
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionBuilder

/-- Primitive vector laws and serializer framing can establish value observations.
The complete control flow is valid for every supplied dependency relation. -/
def family (format : Format) : Family where
  Index := Types
  State := Types.State
  Args := Args
  Value := Value
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := run types format }

def familyRun (format : Format) : FamilyRun (family format) :=
  fun types => run types format

theorem familyReference (format : Format) :
    FamilyReference (family format) (familyRun format) := by
  intro _ _ _ _ _ execution
  exact execution

end Solanalib.Specs.Core.InstructionBuilder
