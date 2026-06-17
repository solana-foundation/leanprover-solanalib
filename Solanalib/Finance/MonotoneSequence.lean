/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Init

/-!
# MonotoneSequence: unbounded discrete monotone growth

A bundled structure for a function `Nat → Nat` that is monotone
non-decreasing — the canonical shape for *unbounded* discrete-time
processes that only ever increase (compound interest, accrued fees,
cumulative supply, slot counters that never roll back).

Companion to `WindowedDecay` and `GrowthCurve`:

* `WindowedDecay`   — bounded, windowed, monotone *down* in time.
* `GrowthCurve`     — bounded, windowed, monotone *up* in time.
* `MonotoneSequence` — **unbounded, no window**, monotone up.

Compound interest is the headline example: balance after `n` periods
never decreases as `n` grows, and there's no a-priori upper bound.

## Main definitions

* `MonotoneSequence` — the bundled structure.
* `MonotoneSequence.apply_zero_le` — generic projection: every value
  is at least the value at step 0.
* `MonotoneSequence.apply_le_of_le` — monotonicity in a tidier form
  for downstream use.

These are inherited by every constructor (e.g.
`CompoundInterest.toMonotoneSequence`) without re-proof.
-/

namespace Solanalib.Finance

/-- An unbounded monotone-non-decreasing sequence of `Nat`s.

Construct via a domain-specific helper (e.g.
`CompoundInterest.toMonotoneSequence`). The single `monotone`
obligation is what every consumer needs in order to reason
about "value at later step ≥ value at earlier step". -/
structure MonotoneSequence where
  /-- The sequence's value at step `n`. -/
  apply : Nat → Nat
  /-- The sequence is monotone non-decreasing. -/
  monotone : ∀ {n m : Nat}, n ≤ m → apply n ≤ apply m

namespace MonotoneSequence

/-- **Inherited:** every term of the sequence is at least the initial
term. Direct corollary of monotonicity from step 0. -/
theorem apply_zero_le (s : MonotoneSequence) (n : Nat) :
    s.apply 0 ≤ s.apply n :=
  s.monotone (Nat.zero_le _)

/-- **Inherited:** explicit form of monotonicity, useful when you have
named indices `n` and `m` rather than an order hypothesis. -/
theorem apply_le_of_le (s : MonotoneSequence) {n m : Nat} (h : n ≤ m) :
    s.apply n ≤ s.apply m :=
  s.monotone h

end MonotoneSequence

end Solanalib.Finance
