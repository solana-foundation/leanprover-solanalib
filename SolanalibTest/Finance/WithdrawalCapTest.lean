/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Finance.WithdrawalCap

/-!
# Regression tests for `Solanalib.Finance.WithdrawalCap`

Concrete end-to-end sanity checks for each branch of `tryAdd`:

* **Disabled cap** (intervalSeconds = 0) — no-op, no state change.
* **Mid-window happy path** — accumulator grows.
* **Mid-window cap reached** — rejection, no state change.
* **Window-elapsed reset** — accumulator resets to `amount`.

Each scenario also pins the relevant theorem (invariant preservation,
interval-reset idempotence) applied to the concrete instance.
-/

namespace SolanalibTest.Finance.WithdrawalCap

open Solanalib Solanalib.Finance

/-- A fresh, enabled cap: 1000 lamports per 60-second window, empty. -/
def fresh : WithdrawalCap :=
  { capacity        := 1000
    intervalSeconds := 60
    current         := 0
    windowStart     := 0 }

/-- A disabled cap (intervalSeconds = 0). -/
def disabled : WithdrawalCap :=
  { capacity        := 1000
    intervalSeconds := 0
    current         := 500    -- non-zero current is fine when disabled
    windowStart     := 0 }

/-- The fresh cap satisfies the invariant. -/
example : WithdrawalCap.Invariant fresh := by decide

/-! ## Disabled cap: tryAdd is a no-op -/

example :
    disabled.tryAdd 999 100 = WithdrawalCap.TryAdd.ok disabled := rfl

/-! ## Mid-window happy path -/

/-- Add 200 lamports at t=30s (mid-window). Cap accepts; current → 200. -/
example :
    fresh.tryAdd 200 30 =
      WithdrawalCap.TryAdd.ok
        { capacity := 1000, intervalSeconds := 60, current := 200, windowStart := 0 } := by
  decide

/-! ## Mid-window cap-reached -/

/-- Try to add 1001 to an empty 1000-cap → rejected. -/
example : fresh.tryAdd 1001 30 = WithdrawalCap.TryAdd.capReached := by
  decide

/-- Theorem-level: an over-cap mid-window add is rejected by P3. -/
example :
    fresh.tryAdd 1001 30 = WithdrawalCap.TryAdd.capReached := by
  apply WithdrawalCap.tryAdd_rejects_over_cap_midwindow
  · decide
  · -- ¬ IsElapsed at now=30 (windowStart=0, intervalSeconds=60, so elapsed needs now ≥ 60).
    unfold WithdrawalCap.IsElapsed; decide
  · -- 0 + 1001 > 1000.
    decide

/-! ## Window-elapsed reset -/

/-- A cap that's been mostly used. -/
def nearlyFull : WithdrawalCap :=
  { capacity := 1000, intervalSeconds := 60, current := 900, windowStart := 0 }

/-- `nearlyFull` satisfies the invariant: 900 ≤ 1000. -/
example : WithdrawalCap.Invariant nearlyFull := by decide

/-- At t=120 (well past one window of 60s), the cap accepts 500 — the
previous `current` is wiped to 0 and the add succeeds. -/
example :
    nearlyFull.tryAdd 500 120 =
      WithdrawalCap.TryAdd.ok
        { capacity := 1000, intervalSeconds := 60, current := 500, windowStart := 120 } := by
  decide

/-- Theorem-level: the reset zeroed `current` and set `windowStart`
to `now`. -/
example
    {c' : WithdrawalCap}
    (h_ok : nearlyFull.tryAdd 500 120 = WithdrawalCap.TryAdd.ok c') :
    c'.current = 500 ∧ c'.windowStart = 120 :=
  WithdrawalCap.interval_reset_idempotent nearlyFull 500 120
    (by decide) (by unfold WithdrawalCap.IsElapsed; decide) (by decide) h_ok

end SolanalibTest.Finance.WithdrawalCap
