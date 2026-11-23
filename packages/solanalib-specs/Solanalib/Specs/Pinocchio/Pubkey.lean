/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Address

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Pinocchio.pubkey

open Solanalib.Contracts.Model Solanalib.Specs.Core

def pubkey_eq_contract : Solanalib.Contracts.Model Unit (Solanalib.Runtime.Pubkey ×
  Solanalib.Runtime.Pubkey) Bool :=
  .returning (fun _ _ => True)
    (fun before args value after => after = before ∧ value = decide (args.1.bytes = args.2.bytes))
def pubkey_eq_run (state : Unit) (args : Solanalib.Runtime.Pubkey × Solanalib.Runtime.Pubkey) :
  Bool × Unit :=
  (Address.equal args.1 args.2, state)
theorem pubkey_eq_reference : pubkey_eq_contract.RealizedBy pubkey_eq_run := by
  intro _ _ _
  exact ⟨rfl, rfl⟩
theorem pubkey_eq_satisfiable : pubkey_eq_contract.Satisfiable := ⟨(), (.zero, .zero), trivial⟩

end Solanalib.Specs.Pinocchio.pubkey
