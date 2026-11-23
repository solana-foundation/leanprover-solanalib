/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.PinocchioToken.Capabilities
import Solanalib.Specs.PinocchioToken2022.Capabilities

/-!
# Family `Instructions`: the shared token observation models

`shared-token::{amount, mint, owner, decimals, state}` (`Solanalib.Specs.Core.Token`) have no Rust
identity of their own: they are the references of `Account::{amount, mint, owner, state}` and
`Mint::decimals` in pinocchio-token 0.6.0 and pinocchio-token-2022 0.3.1, by
definition. Family `TokenViews` records those getters and decides the pinocchio references, so
its records check these models. The theorems state the definitional identity that makes this so.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.Instructions.SharedToken

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem amount_is_shared :
    Solanalib.Specs.PinocchioToken.state.account.Account.amount_reference = Token.amountReference ∧
      Solanalib.Specs.PinocchioToken2022.state.account.Account.amount_reference =
        Token.amountReference :=
  ⟨rfl, rfl⟩

theorem mint_is_shared :
    Solanalib.Specs.PinocchioToken.state.account.Account.mint_reference = Token.mintReference ∧
      Solanalib.Specs.PinocchioToken2022.state.account.Account.mint_reference = Token.mintReference
        :=
  ⟨rfl, rfl⟩

theorem owner_is_shared :
    Solanalib.Specs.PinocchioToken.state.account.Account.owner_reference = Token.ownerReference ∧
      Solanalib.Specs.PinocchioToken2022.state.account.Account.owner_reference =
        Token.ownerReference :=
  ⟨rfl, rfl⟩

theorem decimals_is_shared :
    Solanalib.Specs.PinocchioToken.state.mint.Mint.decimals_reference = Token.decimalsReference ∧
      Solanalib.Specs.PinocchioToken2022.state.mint.Mint.decimals_reference =
        Token.decimalsReference :=
  ⟨rfl, rfl⟩

theorem state_is_shared :
    HEq Solanalib.Specs.PinocchioToken.state.account.Account.state_reference Token.stateFamilyRun ∧
      HEq Solanalib.Specs.PinocchioToken2022.state.account.Account.state_reference
        Token.stateFamilyRun :=
  ⟨HEq.rfl, HEq.rfl⟩

end SolanalibTest.Conformance.Library.Families.Instructions.SharedToken
