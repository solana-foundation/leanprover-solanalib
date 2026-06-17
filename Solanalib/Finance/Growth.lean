/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Finance.Decay

/-!
# GrowthCurve: the windowed dual of `WindowedDecay`

A function `Nat → Nat` that grows from `0` at `tBegin` to `peak` at
`tEnd`, monotone non-decreasing within the window. Same architectural
pattern as `WindowedDecay` — bundled structure with embedded proofs —
but applied to the dual shape.

This module exists to **demonstrate that the bundled-structure pattern
composes across dual domains.** Every `WindowedDecay` has a
complementary `GrowthCurve` via the bridge constructor below; future
"natively growing" shapes (linear vesting written as a primitive
rather than via complement, capped compound interest in a fixed
window, etc.) become first-class `GrowthCurve` instances by providing
their own `toGrowthCurve` constructor.

Unbounded growth shapes (e.g. open-ended compound interest with no
maturity) are *not* `GrowthCurve` — they need a separate
`MonotoneSequence`-style abstraction, which is future work documented
in the project README.

## Main definitions

* `GrowthCurve` — the bundled function + monotone-growth proofs.
* `WindowedDecay.toComplementaryGrowthCurve` — the canonical bridge:
  any decay's complement is a growth.

## Main statements

The four defining properties live in the structure. The constructor
proves them, so consumers get them by projection.
-/

namespace Solanalib.Finance

/-- A function `Nat → Nat` that grows from `0` at `tBegin` to `peak` at
`tEnd`, monotone non-decreasing within the window. The four defining
properties are bundled in (compare `WindowedDecay`).

Construct via a domain-specific helper (e.g.
`WindowedDecay.toComplementaryGrowthCurve`). -/
structure GrowthCurve where
  /-- Start of the growth window. -/
  tBegin : Nat
  /-- End of the growth window (inclusive: `apply tEnd = peak`). -/
  tEnd : Nat
  /-- Peak value, reached at `tEnd`. -/
  peak : Nat
  /-- The growth function. -/
  apply : Nat → Nat
  /-- The growth never exceeds `peak`. -/
  bounded : ∀ t, apply t ≤ peak
  /-- At the start of a non-degenerate window, the value is zero. -/
  at_begin : tBegin < tEnd → apply tBegin = 0
  /-- At the end of the window, the value equals `peak`. -/
  at_end : apply tEnd = peak
  /-- Within the window, the value is monotone non-decreasing in time. -/
  monotone_in_window : ∀ {t₁ t₂ : Nat},
    tBegin ≤ t₁ → t₁ ≤ t₂ → t₂ < tEnd → apply t₁ ≤ apply t₂

namespace WindowedDecay

/-- **The canonical bridge:** every `WindowedDecay` `d` induces a
`GrowthCurve` via `t ↦ d.peak - d.apply t`. This is the "vesting" view
of a decay (claimable balance = total − remaining lock).

All four `GrowthCurve` properties are inherited mechanically from the
corresponding `WindowedDecay` properties — this is the architectural
demonstration that bundled structures compose across dual domains. -/
def toComplementaryGrowthCurve (d : WindowedDecay) : GrowthCurve where
  tBegin             := d.tBegin
  tEnd               := d.tEnd
  peak               := d.peak
  apply              := fun t => d.peak - d.apply t
  bounded            := fun _ => Nat.sub_le _ _
  at_begin           := fun h => by simp [d.at_begin h]
  at_end             := by simp [d.at_end]
  monotone_in_window := fun h_begin h_order h_end =>
    Nat.sub_le_sub_left (d.antitone_in_window h_begin h_order h_end) _

end WindowedDecay

end Solanalib.Finance
