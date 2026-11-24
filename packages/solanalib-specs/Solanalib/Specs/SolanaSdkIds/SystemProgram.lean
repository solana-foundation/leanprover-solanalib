/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Runtime.Ids

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaSdkIds.system_program

/-- The returned key of the SDK macro, using the identical canonical 32-byte ID. -/
def id_model (before : Unit) (_ : Unit) : Solanalib.Runtime.Pubkey × Unit :=
  (Solanalib.Runtime.Ids.systemProgram, before)

/-- Return the exact system key and preserve the mathematical state. -/
def id_contract : Solanalib.Contracts.Model Unit Unit Solanalib.Runtime.Pubkey :=
  .returning (fun _ _ => True)
    (fun before _ value after => value = Solanalib.Runtime.Ids.systemProgram ∧ after = before)

theorem id_reference : id_contract.RealizedBy id_model :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem id_satisfiable : id_contract.Satisfiable := ⟨(), (), trivial⟩

end Solanalib.Specs.SolanaSdkIds.system_program
