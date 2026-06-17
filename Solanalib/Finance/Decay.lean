/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Init

/-!
# Decay: the abstract shape of a peak-to-zero windowed quantity

A typeclass capturing what it means to be a "decaying function" — any
quantity that has a defined window `[tBegin, tEnd)`, a configured peak,
equals `peak` at `tBegin`, equals `0` at `tEnd`, and is non-increasing
in time within the window.

Concrete instances include `LinearDecay.Params` (uniform decay). Future
instances might include exponential decay, step decay, custom curves
fed from on-chain data. The four `Decay`-inherited theorems apply to
every instance — that's the abstraction win.

## Main definitions

* `Decay` — the typeclass.
* `Decay.complementary` — the "vesting" shape: `peak − apply`.

## Main statements

Generic theorems about *any* `Decay` instance:

* `Decay.complementary_le_peak`             — bounded above.
* `Decay.complementary_at_begin`            — starts at zero.
* `Decay.complementary_at_end`              — finishes at the peak.
* `Decay.complementary_monotone_in_window`  — grows monotonically in
                                              time within the window.

These are *inherited* by every concrete decay type without re-proof.
-/

namespace Solanalib.Finance

/-- Abstract typeclass for functions that decay from `peak` to zero
across a window `[tBegin, tEnd)`, non-increasing within the window. -/
class Decay (T : Type) where
  /-- The value of the decay at time `t`. -/
  apply : T → Nat → Nat
  /-- The start of the decay window. -/
  tBegin : T → Nat
  /-- The end of the decay window. -/
  tEnd : T → Nat
  /-- The peak value at the start of the window. -/
  peak : T → Nat
  /-- The decay is bounded above by its peak. -/
  bounded : ∀ x : T, ∀ t, apply x t ≤ peak x
  /-- At the start of the window, the value is the peak. -/
  at_begin : ∀ x : T, tBegin x < tEnd x → apply x (tBegin x) = peak x
  /-- At or after the end of the window, the value is zero. -/
  at_end : ∀ x : T, apply x (tEnd x) = 0
  /-- Within the window, the value is antitone (non-increasing) in time. -/
  antitone_in_window : ∀ x : T, ∀ {t₁ t₂ : Nat},
    tBegin x ≤ t₁ → t₁ ≤ t₂ → t₂ < tEnd x → apply x t₂ ≤ apply x t₁

namespace Decay

/-- The complementary "vesting" shape: at time `t`, this is `peak − apply x t`.

Starts at zero, grows to the peak at the end of the window. -/
def complementary {T : Type} [Decay T] (x : T) (t : Nat) : Nat :=
  Decay.peak x - Decay.apply x t

/-- **Inherited:** the complementary shape is bounded above by the peak. -/
theorem complementary_le_peak {T : Type} [Decay T] (x : T) (t : Nat) :
    complementary x t ≤ Decay.peak x := Nat.sub_le _ _

/-- **Inherited:** at the start of the window, the complementary shape
is zero. -/
theorem complementary_at_begin {T : Type} [Decay T] (x : T)
    (h : Decay.tBegin x < Decay.tEnd x) :
    complementary x (Decay.tBegin x) = 0 := by
  unfold complementary
  rw [Decay.at_begin x h]
  exact Nat.sub_self _

/-- **Inherited:** at the end of the window, the complementary shape
equals the peak. -/
theorem complementary_at_end {T : Type} [Decay T] (x : T) :
    complementary x (Decay.tEnd x) = Decay.peak x := by
  unfold complementary
  rw [Decay.at_end x]
  exact Nat.sub_zero _

/-- **Inherited:** within the window, the complementary shape is
monotone (non-decreasing) in time.

This is the "sign-flip" theorem — `apply` is antitone, so its
complement `peak − apply` is monotone. Falls straight out of
`Decay.antitone_in_window` via `Nat.sub_le_sub_left`. -/
theorem complementary_monotone_in_window {T : Type} [Decay T] (x : T)
    {t₁ t₂ : Nat} (h_begin : Decay.tBegin x ≤ t₁) (h_order : t₁ ≤ t₂)
    (h_end : t₂ < Decay.tEnd x) :
    complementary x t₁ ≤ complementary x t₂ :=
  Nat.sub_le_sub_left (Decay.antitone_in_window x h_begin h_order h_end) _

end Decay

end Solanalib.Finance
