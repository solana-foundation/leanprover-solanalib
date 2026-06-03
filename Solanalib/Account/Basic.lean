/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Primitives.Lamports
import Solanalib.Primitives.Pubkey

/-!
# Accounts

The Solana account model. An on-chain account carries five fields:
its lamport balance, the program that owns it, an opaque data blob,
an executable flag (true for programs, false for data accounts), and
the rent epoch at which rent next comes due.

This module models all five so downstream specs can reason about
account ownership, data layout, and program-vs-data distinctions —
not just balance arithmetic.

## Main definitions

* `Solanalib.Account` — the five-field account record.
* `Solanalib.Account.credit` / `Account.debit` — balance-only updates
  that preserve every other field by construction.

## Main statements

* `credit_lamports`, `debit_lamports` — `@[simp]` projection lemmas.
  Other-field projections (`credit_owner`, `credit_data`, …) reduce
  to `rfl` automatically via Lean's structure-update semantics.
-/

namespace Solanalib

/-- A Solana account: lamport balance, owning program, data blob,
executable flag, and rent epoch. -/
@[ext]
structure Account where
  /-- The number of lamports held by this account. -/
  lamports : Lamports
  /-- The program that owns this account and is authorised to mutate it. -/
  owner : Pubkey
  /-- The opaque data the account holds. Interpretation is owner-specific. -/
  data : ByteArray
  /-- True if this account is a program (BPF binary), false for data. -/
  executable : Bool
  /-- Slot at which rent next becomes due. -/
  rentEpoch : Nat
  deriving Repr, DecidableEq

namespace Account

/-- Credit `amount` lamports to an account; all other fields unchanged. -/
def credit (a : Account) (amount : Lamports) : Account :=
  { a with lamports := a.lamports + amount }

/-- Debit `amount` lamports from an account; all other fields unchanged.

Requires a proof `h` that the account holds at least `amount` lamports,
so this operation can never silently underflow. -/
def debit (a : Account) (amount : Lamports) (_h : amount ≤ a.lamports) : Account :=
  { a with lamports := a.lamports - amount }

@[simp]
theorem credit_lamports (a : Account) (amount : Lamports) :
    (credit a amount).lamports = a.lamports + amount := rfl

@[simp]
theorem debit_lamports (a : Account) (amount : Lamports) (h : amount ≤ a.lamports) :
    (debit a amount h).lamports = a.lamports - amount := rfl

end Account
end Solanalib
