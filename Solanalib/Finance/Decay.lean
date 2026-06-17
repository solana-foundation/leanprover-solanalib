/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Init

/-!
# WindowedDecay: a bundled structure for peak-to-zero windowed decay

A function-with-proofs bundle: every value of `WindowedDecay`
*is* a function `Nat → Nat` that decays from `peak` at `tBegin` to `0`
at `tEnd`, non-increasing in time within the window. The four
defining properties are embedded in the structure, so to construct a
`WindowedDecay` you have to discharge all four obligations up front;
in return, every consumer gets them for free.

This follows Mathlib's pattern (`OrderHom`, `MulHom`, `RingHom`,
`LinearMap` — all bundled structures of function + proofs). Rather than
typeclass-based abstraction (where instance resolution finds the proofs
indirectly), the bundled approach makes the bundle a first-class value
and avoids the implicit-argument elaboration footguns that typeclasses
sometimes hit.

Concrete decay shapes (linear, exponential, piecewise, …) construct a
`WindowedDecay` value via a `toWindowedDecay` helper. Generic theorems
proved here apply automatically to every such construction.

## Main definitions

* `WindowedDecay` — the bundled function + proofs.
* `WindowedDecay.complementary` — the dual "vesting" shape:
  `peak − apply t`.

## Main statements

Generic theorems about *any* `WindowedDecay` value:

* `WindowedDecay.complementary_le_peak`             — bounded by peak.
* `WindowedDecay.complementary_at_begin`            — equals zero at `tBegin`.
* `WindowedDecay.complementary_at_end`              — equals peak at `tEnd`.
* `WindowedDecay.complementary_monotone_in_window`  — non-decreasing in the
                                                      window.

Each of these is the dual ("sign-flipped") form of the corresponding
embedded `WindowedDecay` property.
-/

namespace Solanalib.Finance

/-- A function `Nat → Nat` that decays from `peak` at `tBegin` to `0` at
`tEnd`, non-increasing within the window. The four defining properties
are bundled in.

Construct via a domain-specific helper (e.g.
`LinearDecay.toWindowedDecay`), not directly — direct construction
requires discharging all four proof obligations and is rarely the
right thing. -/
structure WindowedDecay where
  /-- Start of the decay window. -/
  tBegin : Nat
  /-- End of the decay window (exclusive). -/
  tEnd : Nat
  /-- Peak value at the start. -/
  peak : Nat
  /-- The decay function itself. -/
  apply : Nat → Nat
  /-- The decay is bounded above by `peak`. -/
  bounded : ∀ t, apply t ≤ peak
  /-- At the start of a non-degenerate window, the value is `peak`. -/
  at_begin : tBegin < tEnd → apply tBegin = peak
  /-- At or after the end of the window, the value is zero. -/
  at_end : apply tEnd = 0
  /-- Within the window, the value is antitone (non-increasing) in time. -/
  antitone_in_window : ∀ {t₁ t₂ : Nat},
    tBegin ≤ t₁ → t₁ ≤ t₂ → t₂ < tEnd → apply t₂ ≤ apply t₁

namespace WindowedDecay

/-- The complementary "vesting" shape: at time `t`, `peak − apply t`.

Starts at zero, grows to the peak by the end of the window. -/
def complementary (d : WindowedDecay) (t : Nat) : Nat :=
  d.peak - d.apply t

/-- **Inherited:** the complementary shape is bounded above by the peak. -/
theorem complementary_le_peak (d : WindowedDecay) (t : Nat) :
    d.complementary t ≤ d.peak := Nat.sub_le _ _

/-- **Inherited:** at the start of the window, the complementary shape is zero. -/
theorem complementary_at_begin (d : WindowedDecay) (h : d.tBegin < d.tEnd) :
    d.complementary d.tBegin = 0 := by
  unfold complementary
  rw [d.at_begin h]
  exact Nat.sub_self _

/-- **Inherited:** at the end of the window, the complementary shape equals the peak. -/
theorem complementary_at_end (d : WindowedDecay) :
    d.complementary d.tEnd = d.peak := by
  unfold complementary
  rw [d.at_end]
  exact Nat.sub_zero _

/-- **Inherited:** within the window, the complementary shape is monotone
(non-decreasing) in time. Sign-flip of `antitone_in_window` via
`Nat.sub_le_sub_left`. -/
theorem complementary_monotone_in_window (d : WindowedDecay)
    {t₁ t₂ : Nat} (h_begin : d.tBegin ≤ t₁) (h_order : t₁ ≤ t₂)
    (h_end : t₂ < d.tEnd) :
    d.complementary t₁ ≤ d.complementary t₂ :=
  Nat.sub_le_sub_left (d.antitone_in_window h_begin h_order h_end) _

end WindowedDecay

end Solanalib.Finance
