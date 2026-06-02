/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Primitives.Lamports

/-!
# Accounts

A minimal model of a Solana account. A real on-chain account also carries
an owner program, a data blob, an executable flag, and a rent epoch; this
initial model captures only the lamport balance so the first theorems can
stay focused on value conservation. Richer fields will be added in
subsequent modules without altering this signature.
-/

namespace Solanalib

/-- A simplified Solana account, tracking only its lamport balance. -/
structure Account where
  /-- The number of lamports held by this account. -/
  lamports : Lamports
  deriving Repr, DecidableEq

namespace Account

/-- Credit `amount` lamports to an account, returning the updated account. -/
def credit (a : Account) (amount : Lamports) : Account :=
  { a with lamports := a.lamports + amount }

/-- Debit `amount` lamports from an account.

Requires a proof `h` that the account holds at least `amount` lamports, so
this operation can never silently underflow. -/
def debit (a : Account) (amount : Lamports) (_h : amount ≤ a.lamports) : Account :=
  { a with lamports := a.lamports - amount }

end Account
end Solanalib
