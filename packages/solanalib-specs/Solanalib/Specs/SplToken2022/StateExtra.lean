/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenStateExtra

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplToken2022.state.Account

open Solanalib.Specs.Core.Token

/-- Compare the validated AccountState field without changing any account
field. The runtime account owner and initialization are not preconditions. -/
def is_frozen_contract : Solanalib.Contracts.Model Account Unit Bool :=
  .returning (fun _ _ => True) fun before _ value after =>
    value = before.isFrozen ∧ after = before

/-- Exact mathematical discriminator observation. -/
def isFrozenReference (account : Account) (_ : Unit) : Bool × Account :=
  (account.isFrozen, account)

/-- The comparison realizes the complete contract. -/
theorem is_frozen_reference : is_frozen_contract.RealizedBy isFrozenReference := by
  intro before args _
  exact ⟨rfl, rfl⟩

/-- The frozen branch has an explicit account inhabitant. -/
theorem is_frozen_satisfiable : is_frozen_contract.Satisfiable :=
  ⟨⟨.zero, .zero, 0, none, .frozen, none, 0, none⟩, (), trivial⟩

end Solanalib.Specs.SplToken2022.state.Account
