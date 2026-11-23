/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Instruction

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaInstruction.AccountMeta

open Solanalib.Specs.Core.Instruction

/-- Supporting constructor models used by instruction builders. These are
transitive requirements, not additional direct-call inventory entries. -/

def new_model (before : Unit) (args : _root_.Solanalib.Runtime.Pubkey × Bool) : Meta × Unit :=
  (accountMeta args.1 args.2 true, before)

def new_contract : Solanalib.Contracts.Model Unit (_root_.Solanalib.Runtime.Pubkey × Bool) (Meta) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = accountMeta args.1 args.2 true)

theorem new_reference : new_contract.RealizedBy new_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem new_satisfiable : new_contract.Satisfiable :=
  ⟨(), (.zero, false), trivial⟩

def new_readonly_model (before : Unit) (args : _root_.Solanalib.Runtime.Pubkey × Bool) : Meta ×
  Unit :=
  (accountMeta args.1 args.2 false, before)

def new_readonly_contract : Solanalib.Contracts.Model Unit (_root_.Solanalib.Runtime.Pubkey × Bool)
  (Meta) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = accountMeta args.1 args.2 false)

theorem new_readonly_reference : new_readonly_contract.RealizedBy new_readonly_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem new_readonly_satisfiable : new_readonly_contract.Satisfiable :=
  ⟨(), (.zero, false), trivial⟩

end Solanalib.Specs.SolanaInstruction.AccountMeta
