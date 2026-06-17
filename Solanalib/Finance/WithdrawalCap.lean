/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Primitives.Lamports
import Solanalib.Primitives.Time

/-!
# WithdrawalCap: a stateful sliding-window rate limiter

The first **stateful** primitive in Solanalib. Where `WindowedDecay` /
`GrowthCurve` / `MonotoneSequence` describe pure functions of time,
`WithdrawalCap` describes a *resource* that mutates: an accumulator
tracking how much has been withdrawn in the current time window, plus
the window-start timestamp that resets on interval elapse.

This is the per-reserve last line of defence against drain attacks in
lending protocols.

## Bug classes the theorems catch

| Theorem | Bug class |
|---|---|
| `remaining_le_capacity` | Saturating-arithmetic underflow on the remaining calculation |
| `tryAdd_preserves_invariant` | `current` escaping above `capacity` after a successful add |
| `tryAdd_rejects_over_cap` | Off-by-one on the boundary check |
| `interval_reset_idempotent` | First add of a new interval forgetting to zero the accumulator |

## Design notes

- Invariant `current ≤ capacity` is *not* embedded in the structure;
  it's a `Prop`-valued predicate preserved by `tryAdd`. Keeps the
  structure a plain record (no proof obligation at construction).
- Time arithmetic happens at the `.toNat` level via the `Timestamp`
  bridge — UInt64 subtraction would underflow if a caller passed
  `now < windowStart`; the `.toNat` form truncates to 0, which yields
  "not elapsed" — the safe default.
- `intervalSeconds = 0` models a *disabled* cap — `tryAdd` is a no-op
  returning `ok c` unchanged. Matches Kamino's on-chain behaviour.
-/

namespace Solanalib.Finance

/-- A per-reserve withdrawal cap. `intervalSeconds = 0` disables the cap. -/
structure WithdrawalCap where
  /-- Maximum lamports addable per window. -/
  capacity : Lamports
  /-- Window length in seconds. `0` disables the cap. -/
  intervalSeconds : UInt64
  /-- Lamports added so far in the current window. -/
  current : Lamports
  /-- Wall-clock timestamp when the current window started. -/
  windowStart : Timestamp
  deriving Repr, DecidableEq

namespace WithdrawalCap

/-- The invariant a well-formed `WithdrawalCap` should satisfy. -/
def Invariant (c : WithdrawalCap) : Prop :=
  c.current ≤ c.capacity

instance (c : WithdrawalCap) : Decidable (Invariant c) := by
  unfold Invariant; exact inferInstance

/-- Has the current window elapsed at time `now`? Computed at the
`.toNat` level so the comparison cannot underflow. -/
def IsElapsed (c : WithdrawalCap) (now : Timestamp) : Prop :=
  c.windowStart.toNat + c.intervalSeconds.toNat ≤ now.toNat

instance (c : WithdrawalCap) (now : Timestamp) : Decidable (c.IsElapsed now) := by
  unfold IsElapsed; exact inferInstance

/-- The maximum amount that can still be added in the current window.

When disabled, returns the largest representable `Lamports` (so callers
treating `remaining` as a hint won't refuse a valid add). When the
window has elapsed, returns the full `capacity`. Otherwise returns
`capacity − current`. -/
def remaining (c : WithdrawalCap) (now : Timestamp) : Lamports :=
  if c.intervalSeconds.toNat = 0 then
    UInt64.ofNat (UInt64.size - 1)
  else if c.IsElapsed now then
    c.capacity
  else
    c.capacity - c.current

/-- The result of attempting to add to the cap. -/
inductive TryAdd
  /-- Success: the post-operation cap state. -/
  | ok (c' : WithdrawalCap)
  /-- The add would have exceeded the cap; no state change. -/
  | capReached
  deriving Repr, DecidableEq

/-- Try to add `amount` lamports to the cap at time `now`.

Three branches:

1. **Disabled** (`intervalSeconds = 0`): no-op, return `ok c`.
2. **Window elapsed**: reset to a fresh window and check whether
   `amount` alone exceeds `capacity`.
3. **Mid-window**: check whether `current + amount` exceeds
   `capacity`. -/
def tryAdd (c : WithdrawalCap) (amount : Lamports) (now : Timestamp) : TryAdd :=
  if c.intervalSeconds.toNat = 0 then
    TryAdd.ok c
  else if c.IsElapsed now then
    if amount.toNat ≤ c.capacity.toNat then
      TryAdd.ok { c with current := amount, windowStart := now }
    else
      TryAdd.capReached
  else
    if c.current.toNat + amount.toNat ≤ c.capacity.toNat then
      TryAdd.ok { c with current := c.current + amount }
    else
      TryAdd.capReached

/-! ## Theorems -/

/-- **P1 — Bounded remaining.** When the cap is enabled and the
invariant holds, `remaining` never exceeds `capacity`. -/
theorem remaining_le_capacity (c : WithdrawalCap) (now : Timestamp)
    (h_inv : Invariant c) (h_enabled : c.intervalSeconds.toNat ≠ 0) :
    c.remaining now ≤ c.capacity := by
  unfold remaining
  simp [h_enabled]
  by_cases h : c.IsElapsed now
  · simp [h]                              -- elapsed: remaining = capacity
  · simp [h]                              -- mid-window: capacity − current ≤ capacity
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h_inv]
    exact Nat.sub_le _ _

/-- **P2 — `tryAdd` preserves the invariant.** -/
theorem tryAdd_preserves_invariant
    (c : WithdrawalCap) (amount : Lamports) (now : Timestamp)
    (h_inv : Invariant c)
    {c' : WithdrawalCap}
    (h_ok : c.tryAdd amount now = TryAdd.ok c') :
    Invariant c' := by
  unfold tryAdd at h_ok
  unfold Invariant
  by_cases h_disabled : c.intervalSeconds.toNat = 0
  · simp [h_disabled] at h_ok
    rw [← h_ok]; exact h_inv
  · simp [h_disabled] at h_ok
    by_cases h_elapsed : c.IsElapsed now
    · simp [h_elapsed] at h_ok
      by_cases h_fits : amount.toNat ≤ c.capacity.toNat
      · simp [h_fits] at h_ok
        rw [← h_ok]
        -- Goal: amount ≤ capacity (UInt64). From h_fits via le_iff_toNat_le.
        rwa [UInt64.le_iff_toNat_le]
      · simp [h_fits] at h_ok
    · simp [h_elapsed] at h_ok
      by_cases h_fits : c.current.toNat + amount.toNat ≤ c.capacity.toNat
      · simp [h_fits] at h_ok
        rw [← h_ok]
        -- Goal: c.current + amount ≤ c.capacity (UInt64).
        rw [UInt64.le_iff_toNat_le]
        have h_cap_lt : c.capacity.toNat < UInt64.size := c.capacity.toNat_lt
        have h_sum_lt : c.current.toNat + amount.toNat < UInt64.size :=
          Nat.lt_of_le_of_lt h_fits h_cap_lt
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt h_sum_lt]
        exact h_fits
      · simp [h_fits] at h_ok

/-- **P3 — `tryAdd` rejects over-cap requests in mid-window.** -/
theorem tryAdd_rejects_over_cap_midwindow
    (c : WithdrawalCap) (amount : Lamports) (now : Timestamp)
    (h_enabled : c.intervalSeconds.toNat ≠ 0)
    (h_not_elapsed : ¬ c.IsElapsed now)
    (h_over : c.current.toNat + amount.toNat > c.capacity.toNat) :
    c.tryAdd amount now = TryAdd.capReached := by
  unfold tryAdd
  simp [h_enabled, h_not_elapsed]
  exact h_over

/-- **P3' — `tryAdd` rejects over-cap requests at interval reset.**
After a window elapses, an add still rejects if `amount` alone
exceeds `capacity`. -/
theorem tryAdd_rejects_over_cap_at_reset
    (c : WithdrawalCap) (amount : Lamports) (now : Timestamp)
    (h_enabled : c.intervalSeconds.toNat ≠ 0)
    (h_elapsed : c.IsElapsed now)
    (h_over : amount.toNat > c.capacity.toNat) :
    c.tryAdd amount now = TryAdd.capReached := by
  unfold tryAdd
  simp [h_enabled, h_elapsed]
  exact h_over

/-- **P4 — Interval-reset idempotence.** After the window elapses,
a successful add zeroes the previous accumulator and starts a fresh
window: `c'.current = amount` and `c'.windowStart = now`. -/
theorem interval_reset_idempotent
    (c : WithdrawalCap) (amount : Lamports) (now : Timestamp)
    (h_enabled : c.intervalSeconds.toNat ≠ 0)
    (h_elapsed : c.IsElapsed now)
    (h_fits : amount.toNat ≤ c.capacity.toNat)
    {c' : WithdrawalCap}
    (h_ok : c.tryAdd amount now = TryAdd.ok c') :
    c'.current = amount ∧ c'.windowStart = now := by
  unfold tryAdd at h_ok
  simp [h_enabled, h_elapsed, h_fits] at h_ok
  rw [← h_ok]
  exact ⟨rfl, rfl⟩

end WithdrawalCap

end Solanalib.Finance
