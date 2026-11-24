/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenStateContracts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.PinocchioToken.state

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace account.Account

/-- The versioned account-view parser retains the acquired typed guard.
Length/owner/borrow error order comes from the shared parser policy of this version. -/
def from_account_view_contract := Token.fromViewContract .legacy .account

/-- The complete mathematical reference parser, including ordinary failures. -/
def from_account_view_reference := Token.fromAccountView .legacy .account

/-- Closed parser reference correctness; no source execution is assumed. -/
theorem from_account_view_reference_realizes :
    from_account_view_contract.RealizedBy from_account_view_reference :=
  Token.fromViewReference_realizes .legacy .account

/-- The parser contract has a concrete account input. -/
theorem from_account_view_satisfiable : from_account_view_contract.Satisfiable :=
  Token.fromViewContract_satisfiable .legacy .account

/-- Observe the amount through the live typed account guard. -/
def amount_contract := Token.amountContract

/-- The mathematical amount reference preserves all shared state. -/
def amount_reference := Token.amountReference

/-- Closed correctness of the amount reference interpretation. -/
theorem amount_reference_realizes : amount_contract.RealizedBy amount_reference :=
  Token.amountReference_realizes

/-- The amount observation has a live account-reference witness. -/
theorem amount_satisfiable : amount_contract.Satisfiable :=
  Token.amountContract_satisfiable

/-- Return a mint-field descriptor carrying the supplied parent guard identity. -/
def mint_contract := Token.mintContract

/-- The mathematical mint reference preserves all shared state. -/
def mint_reference := Token.mintReference

/-- Closed correctness of the mint reference interpretation. -/
theorem mint_reference_realizes : mint_contract.RealizedBy mint_reference :=
  Token.mintReference_realizes

/-- The mint observation has a live account-reference witness. -/
theorem mint_satisfiable : mint_contract.Satisfiable :=
  Token.mintContract_satisfiable

/-- Return an owner-field descriptor carrying the supplied parent guard identity. -/
def owner_contract := Token.ownerContract

/-- The mathematical owner reference preserves all shared state. -/
def owner_reference := Token.ownerReference

/-- Closed correctness of the owner reference interpretation. -/
theorem owner_reference_realizes : owner_contract.RealizedBy owner_reference :=
  Token.ownerReference_realizes

/-- The owner observation has a live account-reference witness. -/
theorem owner_satisfiable : owner_contract.Satisfiable :=
  Token.ownerContract_satisfiable

/-- The partial account-state projection can panic on raw bytes the parser
accepted. Unreadable guards have no finite exit; target-specific panic outcomes
remain explicit on readable bytes. -/
def state_contract := Token.stateFamily

/-- The reference relation of the state projection at every panic-policy index. -/
def state_reference : FamilyRun state_contract := Token.stateFamilyRun

/-- A concrete abort policy witnesses an inhabited family instance. -/
def state_sample := Token.stateAbortPolicy

/-- Every handler instance satisfies the same state-projection outcome relation. -/
theorem state_reference_holds : FamilyReference state_contract state_reference :=
  Token.stateFamily_reference

/-- The selected sample has a represented live reference. -/
theorem state_satisfiable : FamilySatisfiable state_contract state_sample :=
  Token.stateFamily_satisfiable

/-- The selected sample admits an actual finite reference execution. -/
theorem state_execution : FamilyHasExecution state_contract state_reference state_sample :=
  Token.stateFamily_execution

end account.Account

namespace mint.Mint

/-- The versioned mint parser preserves its distinct owner error and returns
the actual mapped shared guard, without requiring initialization. -/
def from_account_view_contract := Token.fromViewContract .legacy .mint

/-- The complete mint parser reference, including guard effects on failure. -/
def from_account_view_reference := Token.fromAccountView .legacy .mint

/-- Closed correctness of the mint parser interpretation. -/
theorem from_account_view_reference_realizes :
    from_account_view_contract.RealizedBy from_account_view_reference :=
  Token.fromViewReference_realizes .legacy .mint

/-- The mint parser contract has a concrete account input. -/
theorem from_account_view_satisfiable : from_account_view_contract.Satisfiable :=
  Token.fromViewContract_satisfiable .legacy .mint

/-- Decimal precision is read from the current guarded mint byte view. -/
def decimals_contract := Token.decimalsContract

/-- The state-preserving reference interpretation of decimal precision. -/
def decimals_reference := Token.decimalsReference

/-- Closed correctness of the decimal observation. -/
theorem decimals_reference_realizes : decimals_contract.RealizedBy decimals_reference :=
  Token.decimalsReference_realizes

/-- A live mint guard satisfies the decimal-read precondition. -/
theorem decimals_satisfiable : decimals_contract.Satisfiable :=
  Token.decimalsContract_satisfiable

end mint.Mint
end Solanalib.Specs.PinocchioToken.state
