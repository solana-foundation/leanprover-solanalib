/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenState

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- The token account helper compares only the validated state enum. -/
def Account.isFrozen (account : Account) : Bool := account.state == .frozen

/-- The helper is true exactly at the frozen discriminant. -/
theorem Account.isFrozen_iff (account : Account) :
    account.isFrozen = true ↔ account.state = .frozen := by
  cases stateEq : account.state <;> simp [isFrozen, stateEq]

/-- The metadata value contains the raw nullable authority key, a mint key,
three UTF-8 strings and an ordered sequence of additional key/value strings.
This value observation does not impose the documented unique-key convention. -/
structure Metadata where
  /-- All-zero bytes denote no update authority. -/
  updateAuthority : Solanalib.Runtime.Pubkey
  /-- Associated mint, including the all-zero default. -/
  mint : Solanalib.Runtime.Pubkey
  /-- Token name. -/
  name : String
  /-- Token symbol. -/
  symbol : String
  /-- Metadata URI. -/
  uri : String
  /-- Additional entries retain their source order and duplicates. -/
  additionalMetadata : List (String × String)
  deriving DecidableEq, Repr

/-- Deriving Default constructs empty String/Vec values with zero capacities;
no heap allocation is required by any of these empty constructors. A source
adapter must return actual owned empty containers, not arbitrary dangling data. -/
def Metadata.default : Metadata := ⟨.zero, .zero, "", "", "", []⟩

end Solanalib.Specs.Core.Token
