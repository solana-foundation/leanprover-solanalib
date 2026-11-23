/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Mathlib.Tactic.Ring
import Solanalib.Init

/-!
# Limbs: wide integers stored as little-endian `u64` words

Rust has no native integer wider than 128 bits, so Solana programs that need
256-bit intermediates (`mul_div` of two `u128` values, precise AMM math, …)
use a fixed array of `u64` limbs, least significant first — the layout of
`[u64; 4]` in the `uint` crate's `U256` and similar types. This module
gives the numeric value of such an array and the inverse encoding.

## Main definitions

* `Solanalib.Numeric.limbsValue` — value of a little-endian `u64` limb list.
* `Solanalib.Numeric.toLimbs` — the `k`-limb encoding of a number, modulo `2^(64 k)`.
* `Solanalib.Numeric.u256Value` — value of a `[u64; 4]`.

## Main statements

* `limbsValue_lt` — `k` limbs hold a value below `2^(64 k)`.
* `limbsValue_append` — concatenating limb lists is a shifted sum.
* `limbsValue_toLimbs` — encoding then decoding reduces modulo `2^(64 k)`.
* `u256Value_eq` — the explicit four-limb formula, `u256Value_lt` — its bound.
-/

namespace Solanalib.Numeric

/-- The value of a little-endian list of `u64` limbs. -/
def limbsValue : List UInt64 → Nat
  | [] => 0
  | limb :: rest => limb.toNat + 2 ^ 64 * limbsValue rest

/-- The `count` least significant `u64` limbs of `n`, least significant first. -/
def toLimbs : Nat → Nat → List UInt64
  | 0, _ => []
  | count + 1, n => UInt64.ofNat n :: toLimbs count (n / 2 ^ 64)

/-- The value of a `[u64; 4]` stored least significant limb first. -/
def u256Value (limbs : Vector UInt64 4) : Nat := limbsValue limbs.toList

@[simp]
theorem limbsValue_nil : limbsValue [] = 0 := rfl

@[simp]
theorem limbsValue_cons (limb : UInt64) (rest : List UInt64) :
    limbsValue (limb :: rest) = limb.toNat + 2 ^ 64 * limbsValue rest := rfl

/-- A list of `k` limbs holds a value below `2^(64 k)`. -/
theorem limbsValue_lt (limbs : List UInt64) : limbsValue limbs < 2 ^ (64 * limbs.length) := by
  induction limbs with
  | nil => simp
  | cons limb rest ih =>
    have hlimb := limb.toNat_lt
    rw [limbsValue_cons, List.length_cons, Nat.mul_succ, Nat.pow_add]
    have : 2 ^ 64 * limbsValue rest + 2 ^ 64 ≤ 2 ^ 64 * 2 ^ (64 * rest.length) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    rw [Nat.mul_comm (2 ^ (64 * rest.length))]
    omega

/-- Concatenation places the second list above the first. -/
theorem limbsValue_append (low high : List UInt64) :
    limbsValue (low ++ high) = limbsValue low + 2 ^ (64 * low.length) * limbsValue high := by
  induction low with
  | nil => simp
  | cons limb rest ih =>
    simp only [List.cons_append, limbsValue_cons, ih, List.length_cons]
    ring

@[simp]
theorem length_toLimbs (count n : Nat) : (toLimbs count n).length = count := by
  induction count generalizing n with
  | zero => rfl
  | succ count ih => simp [toLimbs, ih]

/-- Decoding the `count`-limb encoding of `n` recovers `n` modulo `2^(64 count)`. -/
theorem limbsValue_toLimbs (count n : Nat) :
    limbsValue (toLimbs count n) = n % 2 ^ (64 * count) := by
  induction count generalizing n with
  | zero => simp [toLimbs, Nat.mod_one]
  | succ count ih =>
    rw [toLimbs, limbsValue_cons, ih, UInt64.toNat_ofNat', Nat.mul_succ, Nat.pow_add,
      Nat.mul_comm (2 ^ (64 * count)), Nat.mod_mul]

/-- An in-range number survives the encoding round trip. -/
theorem limbsValue_toLimbs_of_lt {count n : Nat} (h : n < 2 ^ (64 * count)) :
    limbsValue (toLimbs count n) = n := by
  rw [limbsValue_toLimbs, Nat.mod_eq_of_lt h]

/-- The explicit four-limb formula for a `[u64; 4]`. -/
theorem u256Value_eq (limbs : Vector UInt64 4) :
    u256Value limbs = limbs[0].toNat + 2 ^ 64 * limbs[1].toNat + 2 ^ 128 * limbs[2].toNat +
      2 ^ 192 * limbs[3].toNat := by
  obtain ⟨⟨list⟩, hsize⟩ := limbs
  match list, hsize with
  | [a, b, c, d], _ =>
    simp only [u256Value, Vector.toList_mk, limbsValue_cons, limbsValue_nil]
    simp [Vector.getElem_mk]
    ring

/-- A `[u64; 4]` holds a value below `2^256`. -/
theorem u256Value_lt (limbs : Vector UInt64 4) : u256Value limbs < 2 ^ 256 := by
  have := limbsValue_lt limbs.toList
  rwa [Vector.length_toList] at this

end Solanalib.Numeric
