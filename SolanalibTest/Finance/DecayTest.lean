/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Finance.LinearDecay

/-!
# Regression tests for `Solanalib.Finance.WindowedDecay`

Pins the bundled-structure abstraction. The first time a generic
`WindowedDecay.complementary_*` theorem applies to a value constructed
via `LinearDecay.toWindowedDecay` *without re-proof* validates the
architectural pattern.
-/

namespace SolanalibTest.Finance.Decay

open Solanalib.Finance

/-- A concrete linear-decay bundle. -/
def example_decay : WindowedDecay :=
  LinearDecay.toWindowedDecay 0 1000 10000

/-- The bundled `apply` reduces to the underlying `LinearDecay.value`. -/
example : example_decay.apply 500 =
    LinearDecay.value 0 500 1000 10000 := rfl

/-- Generic `complementary` at the start of the window is zero. The
proof is the *inherited* `WindowedDecay.complementary_at_begin`,
applied to our `example_decay`. No LinearDecay-specific reasoning. -/
example : example_decay.complementary 0 = 0 :=
  example_decay.complementary_at_begin (by decide)

/-- At the end, complementary equals the peak. -/
example : example_decay.complementary 1000 = 10000 :=
  example_decay.complementary_at_end

/-- Bounded by peak — for any time `t`. -/
example (t : Nat) : example_decay.complementary t ≤ 10000 :=
  example_decay.complementary_le_peak t

/-- Monotone non-decreasing inside the window. -/
example : example_decay.complementary 250
            ≤ example_decay.complementary 750 :=
  example_decay.complementary_monotone_in_window
    (by decide) (by decide) (by decide)

/-- Halfway through the window, the complementary value is half of peak. -/
example : example_decay.complementary 500 = 5000 := by decide

end SolanalibTest.Finance.Decay
