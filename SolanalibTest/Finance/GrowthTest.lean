/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Finance.Growth
import Solanalib.Finance.LinearDecay

/-!
# Regression tests for `Solanalib.Finance.GrowthCurve`

The architectural goal of this module is to demonstrate that the
bundled-structure pattern (introduced for `WindowedDecay`) composes
across dual domains. These tests pin that:

1. A `WindowedDecay` constructed from `LinearDecay` can be converted to
   a `GrowthCurve` via `toComplementaryGrowthCurve` with no extra
   proof obligations on the caller.
2. The resulting `GrowthCurve`'s four embedded properties evaluate
   correctly on concrete inputs.
-/

namespace SolanalibTest.Finance.Growth

open Solanalib.Finance

/-- A concrete linear-decay bundle: peak 10000, window [0, 1000). -/
def example_decay : WindowedDecay :=
  LinearDecay.toWindowedDecay 0 1000 10000

/-- The induced GrowthCurve: vesting from 0 at t=0 to 10000 at t=1000. -/
def example_growth : GrowthCurve :=
  example_decay.toComplementaryGrowthCurve

/-- At the start of the window, the growth value is zero. -/
example : example_growth.apply 0 = 0 :=
  example_growth.at_begin (by decide)

/-- At the end of the window, the growth value equals the peak. -/
example : example_growth.apply 1000 = 10000 :=
  example_growth.at_end

/-- The growth value never exceeds the peak. -/
example (t : Nat) : example_growth.apply t ≤ 10000 :=
  example_growth.bounded t

/-- Inside the window, the growth value is monotone non-decreasing. -/
example : example_growth.apply 250 ≤ example_growth.apply 750 :=
  example_growth.monotone_in_window (by decide) (by decide) (by decide)

/-- Concrete: halfway through the window, the growth value is half the peak. -/
example : example_growth.apply 500 = 5000 := by decide

end SolanalibTest.Finance.Growth
