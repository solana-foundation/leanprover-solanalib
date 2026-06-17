/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Finance.LinearDecay

/-!
# Regression tests for `Solanalib.Finance.Decay`

The typeclass abstraction pays for itself the first time a generic
`Decay` theorem applies to a concrete instance without re-proof. These
tests pin that contract:

* A `LinearDecay.Params` value carries a `Decay` instance.
* The four generic `Decay.complementary_*` theorems instantiated on it
  give the *correct* vesting-shape statements — without re-deriving
  them from `LinearDecay`'s primitives.
-/

namespace SolanalibTest.Finance.Decay

open Solanalib.Finance

/-- A concrete linear-decay configuration. -/
def example_params : LinearDecay.Params := ⟨0, 1000, 10000⟩

/-- The instance is found by typeclass resolution. -/
example : Decay LinearDecay.Params := inferInstance

/-- Generic `Decay.apply` reduces to `LinearDecay.value` on a `Params`. -/
example : Decay.apply example_params 500 =
    LinearDecay.value 0 500 1000 10000 := rfl

/-- Generic `complementary` at the start of the window is zero. Caught
by the inherited theorem; we don't redo the math. -/
example : Decay.complementary example_params 0 = 0 :=
  Decay.complementary_at_begin example_params (by decide)

/-- Generic `complementary` at the end equals the peak. -/
example : Decay.complementary example_params 1000 = 10000 :=
  Decay.complementary_at_end example_params

/-- Generic `complementary` is bounded by the peak. -/
example (t : Nat) : Decay.complementary example_params t ≤ 10000 :=
  Decay.complementary_le_peak example_params t

/-- Generic `complementary` is monotone (non-decreasing) inside the
window. The proof is `Decay.complementary_monotone_in_window`, applied
without any LinearDecay-specific lemma. -/
example : Decay.complementary example_params 250
            ≤ Decay.complementary example_params 750 :=
  Decay.complementary_monotone_in_window example_params
    (by decide) (by decide) (by decide)

/-- Concrete: halfway through the window, the complementary value is
half of peak — matching the underlying linear formula. -/
example : Decay.complementary example_params 500 = 5000 := by decide

end SolanalibTest.Finance.Decay
