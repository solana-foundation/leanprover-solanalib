/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Finance.MonotoneSequence
import Solanalib.Numeric.Fraction

/-!
# CompoundInterest: discrete compounding as a `MonotoneSequence`

This module is the first downstream consumer that **composes** two
Solanalib layers we built earlier:

* `Solanalib.Numeric.Fraction` is the *rate's* type — a Q68.60 fixed-point
  multiplier (1.0 = no growth, 1.01 = 1% growth per period, …).
* `Solanalib.Finance.MonotoneSequence` is the *output*'s bundled type —
  the family of unbounded monotone Nat-indexed sequences.

The definition itself is short:

```lean
def balance (principal : Nat) (multiplier : Fraction) : Nat → Nat
  | 0     => principal
  | n + 1 => balance principal multiplier n * multiplier.bits / Fraction.scale
```

Each step multiplies by the Q68.60-encoded `multiplier` and divides
back out by `Fraction.scale`. With `multiplier ≥ Fraction.one`
(equivalently, `multiplier.bits ≥ scale`), this is provably monotone
non-decreasing in `n` — that's the bundled-structure proof obligation
for `MonotoneSequence`.

## Main definitions

* `Solanalib.Finance.CompoundInterest.balance` — the discrete-compounding
  function.
* `Solanalib.Finance.CompoundInterest.toMonotoneSequence` — the
  composition: a `(principal, multiplier ≥ 1)` pair becomes a
  `MonotoneSequence`, inheriting all generic theorems.

## Main statements

* `balance_zero`               — `balance p m 0 = p`.
* `balance_at_one_multiplier`  — with `multiplier = 1.0`, balance is constant.
* `balance_succ_ge`            — one-step monotonicity (given `multiplier ≥ 1`).
* `balance_monotone`           — arbitrary-step monotonicity.
* `balance_ge_principal`       — balance never drops below the principal.

The four-property pattern follows `LinearDecay`'s `value_*` discipline:
one operation, several named theorems, each catching a distinct
refactor-bug class (`balance < principal` would be a "lender loses
funds" exploit; non-monotonicity would be a "wait longer, owe less"
exploit; etc.).

The real-world step from this MVP to Kamino's
`approximate_compounded_interest` is its truncated Taylor-series
approximation of `(1 + r)^n` for large `n`. That refinement — and the
error-bound theorem relating the approximation to the exact
compounding done here — is roadmap work documented in the project
README.
-/

namespace Solanalib.Finance.CompoundInterest

open Solanalib

/-- The balance after `periods` periods of compounding from `principal`
at multiplier `multiplier`. -/
def balance (principal : Nat) (multiplier : Fraction) : Nat → Nat
  | 0       => principal
  | n + 1   => balance principal multiplier n * multiplier.bits / Fraction.scale

/-! ## Theorems -/

/-- Boundary: balance at step 0 is the principal. -/
@[simp] theorem balance_zero (principal : Nat) (multiplier : Fraction) :
    balance principal multiplier 0 = principal := rfl

/-- With a unit multiplier (i.e. `Fraction.one`, no growth), the
balance is constant across all periods. -/
theorem balance_at_one_multiplier (principal : Nat) (n : Nat) :
    balance principal Fraction.one n = principal := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show balance principal Fraction.one k * Fraction.one.bits
            / Fraction.scale = principal
    rw [ih, Fraction.one_bits, Nat.mul_div_cancel _ Fraction.scale_pos]

/-- **One-step monotonicity.** With `multiplier ≥ Fraction.one`, the
balance never decreases from one period to the next. -/
theorem balance_succ_ge (principal : Nat) (multiplier : Fraction)
    (h : Fraction.one ≤ multiplier) (n : Nat) :
    balance principal multiplier n ≤ balance principal multiplier (n + 1) := by
  show balance principal multiplier n
        ≤ balance principal multiplier n * multiplier.bits / Fraction.scale
  -- `Fraction.one ≤ multiplier` reduces to `Fraction.scale ≤ multiplier.bits`
  -- via the `LE Fraction` instance and `one_bits`.
  have h_scale : Fraction.scale ≤ multiplier.bits := by
    have hh : Fraction.one.bits ≤ multiplier.bits := h
    rwa [Fraction.one_bits] at hh
  have h1 : balance principal multiplier n * Fraction.scale
            ≤ balance principal multiplier n * multiplier.bits :=
    Nat.mul_le_mul_left _ h_scale
  have h2 : balance principal multiplier n * Fraction.scale / Fraction.scale
            ≤ balance principal multiplier n * multiplier.bits / Fraction.scale :=
    Nat.div_le_div_right h1
  rwa [Nat.mul_div_cancel _ Fraction.scale_pos] at h2

/-- **Multi-step monotonicity.** With `multiplier ≥ Fraction.one`, the
balance is monotone non-decreasing across any range of periods. -/
theorem balance_monotone (principal : Nat) (multiplier : Fraction)
    (h : Fraction.one ≤ multiplier) {n m : Nat} (hnm : n ≤ m) :
    balance principal multiplier n ≤ balance principal multiplier m := by
  induction hnm with
  | refl       => exact Nat.le_refl _
  | step _ ih  => exact Nat.le_trans ih (balance_succ_ge principal multiplier h _)

/-- The balance never drops below the principal (given `multiplier ≥ 1`). -/
theorem balance_ge_principal (principal : Nat) (multiplier : Fraction)
    (h : Fraction.one ≤ multiplier) (n : Nat) :
    principal ≤ balance principal multiplier n := by
  have h_mono := balance_monotone principal multiplier h (Nat.zero_le n)
  -- balance _ _ 0 = principal
  simpa using h_mono

/-! ## Composition into `MonotoneSequence`

The headline composition move: a `(principal, multiplier ≥ 1)` pair
becomes a `MonotoneSequence`, which automatically inherits the two
generic theorems proved in `Solanalib.Finance.MonotoneSequence`:

* `MonotoneSequence.apply_zero_le`  — value at any step ≥ value at step 0.
* `MonotoneSequence.apply_le_of_le` — value-at-later ≥ value-at-earlier.

Construction discharges the single `monotone` obligation via
`balance_monotone`. No new math; pure composition. -/

/-- Bundle a compounding configuration into a `MonotoneSequence`. -/
def toMonotoneSequence (principal : Nat) (multiplier : Fraction)
    (h : Fraction.one ≤ multiplier) : MonotoneSequence where
  apply := balance principal multiplier
  monotone := balance_monotone principal multiplier h

end Solanalib.Finance.CompoundInterest
