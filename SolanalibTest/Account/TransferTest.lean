/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Account.Transfer

/-!
# Regression tests for `Solanalib.Account.Transfer`

Each `example` here passes iff the file type-checks. The tests below pin
specific shape-preserving properties: if a future refactor breaks them
(e.g. `Lamports` reverts from `notation` to `abbrev` and `omega` stops
firing, or the `@[simp]` projection lemmas are removed), CI catches it.
-/

namespace SolanalibTest.Account

open Solanalib Solanalib.Account

/-- `omega` must continue to work over the `Lamports` notation. If `Lamports`
ever reverts to `abbrev`, this fails. -/
example (a b : Lamports) (h : a ≤ b) : b - a + a = b := by omega

/-- The structural `@[simp]` lemmas expose lamports through `credit` and
`debit` so downstream `simp` calls can finish their job. -/
example (a : Account) (n : Lamports) :
    (Account.credit a n).lamports = a.lamports + n := by simp

example (a : Account) (n : Lamports) (h : n ≤ a.lamports) :
    (Account.debit a n h).lamports = a.lamports - n := by simp

/-- `transfer_preserves_total` is applicable to concrete amounts. -/
example (src dst : Account) (h : 100 ≤ src.lamports) :
    (transfer src dst 100 h).source.lamports
      + (transfer src dst 100 h).destination.lamports
      = src.lamports + dst.lamports :=
  transfer_preserves_total src dst 100 h

end SolanalibTest.Account
