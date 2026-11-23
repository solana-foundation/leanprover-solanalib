/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Mathlib.Order.MinMax
import Solanalib.Init

/-!
# Checked: Rust integer arithmetic semantics at the spec layer

Solana programs perform their arithmetic on fixed-width Rust integers
(`u64`, `u128`, `i64`, `i128`, …) through `checked_*`, `saturating_*` and
`wrapping_*` operations. This module describes those operations on
unbounded `Nat` / `Int` values, parameterised by the bit width, so that
specifications can say *exactly* when an on-chain computation fails or
clamps while proofs stay in `omega`-friendly arithmetic.

`checked_*` returns `none` precisely where the Rust method returns `None`;
`saturating_*` clamps to the representable range; `wrapping_*` reduces
modulo `2^bits`. Bridge lemmas connect the unsigned models at width 64
to Lean's `UInt64` operations.

## Main definitions

* `Solanalib.Numeric.UnsignedFits`, `Solanalib.Numeric.SignedFits` — range predicates.
* `checkedAdd`, `checkedSub`, `checkedMul`, `checkedDiv` — unsigned `checked_*`.
* `saturatingAdd`, `saturatingSub`, `saturatingMul` — unsigned `saturating_*`.
* `wrappingAdd`, `wrappingMul` — unsigned `wrapping_*`.
* `signedMin`, `signedMax`, `saturate`, `checkedAddSigned`, `checkedSubSigned`,
  `checkedMulSigned` — the signed counterparts.

## Main statements

* `checkedAdd_eq_some_iff` (and `Sub`, `Mul`, `Div`, signed variants) — exact failure conditions.
* `saturatingAdd_lt`, `saturatingMul_lt`, `saturate_fits` — saturation stays in range.
* `checkedAdd_uint64`, `checkedSub_uint64`, `checkedMul_uint64`, `wrappingAdd_uint64` —
  agreement with `UInt64` arithmetic.
-/

namespace Solanalib.Numeric

/-! ## Unsigned integers -/

/-- `n` is representable as a `bits`-wide unsigned integer. -/
def UnsignedFits (bits n : Nat) : Prop := n < 2 ^ bits

instance (bits n : Nat) : Decidable (UnsignedFits bits n) := by
  unfold UnsignedFits; exact inferInstance

/-- `checked_add` on `bits`-wide unsigned integers. -/
def checkedAdd (bits a b : Nat) : Option Nat :=
  if a + b < 2 ^ bits then some (a + b) else none

/-- `checked_sub` on unsigned integers: fails exactly on underflow. -/
def checkedSub (a b : Nat) : Option Nat :=
  if b ≤ a then some (a - b) else none

/-- `checked_mul` on `bits`-wide unsigned integers. -/
def checkedMul (bits a b : Nat) : Option Nat :=
  if a * b < 2 ^ bits then some (a * b) else none

/-- `checked_div` on unsigned integers: fails exactly on division by zero. -/
def checkedDiv (a b : Nat) : Option Nat :=
  if b = 0 then none else some (a / b)

/-- `saturating_add` on `bits`-wide unsigned integers. -/
def saturatingAdd (bits a b : Nat) : Nat := min (a + b) (2 ^ bits - 1)

/-- `saturating_sub` on unsigned integers: truncated subtraction. -/
def saturatingSub (a b : Nat) : Nat := a - b

/-- `saturating_mul` on `bits`-wide unsigned integers. -/
def saturatingMul (bits a b : Nat) : Nat := min (a * b) (2 ^ bits - 1)

/-- `wrapping_add` on `bits`-wide unsigned integers. -/
def wrappingAdd (bits a b : Nat) : Nat := (a + b) % 2 ^ bits

/-- `wrapping_mul` on `bits`-wide unsigned integers. -/
def wrappingMul (bits a b : Nat) : Nat := a * b % 2 ^ bits

theorem checkedAdd_eq_some_iff {bits a b c : Nat} :
    checkedAdd bits a b = some c ↔ UnsignedFits bits (a + b) ∧ c = a + b := by
  unfold checkedAdd UnsignedFits
  split <;> simp_all [eq_comm]

theorem checkedAdd_eq_none_iff {bits a b : Nat} :
    checkedAdd bits a b = none ↔ ¬UnsignedFits bits (a + b) := by
  unfold checkedAdd UnsignedFits
  split <;> simp_all

theorem checkedSub_eq_some_iff {a b c : Nat} :
    checkedSub a b = some c ↔ b ≤ a ∧ c = a - b := by
  unfold checkedSub
  split <;> simp_all [eq_comm]

theorem checkedSub_eq_none_iff {a b : Nat} : checkedSub a b = none ↔ a < b := by
  unfold checkedSub
  split <;> simp_all

theorem checkedMul_eq_some_iff {bits a b c : Nat} :
    checkedMul bits a b = some c ↔ UnsignedFits bits (a * b) ∧ c = a * b := by
  unfold checkedMul UnsignedFits
  split <;> simp_all [eq_comm]

theorem checkedMul_eq_none_iff {bits a b : Nat} :
    checkedMul bits a b = none ↔ ¬UnsignedFits bits (a * b) := by
  unfold checkedMul UnsignedFits
  split <;> simp_all

theorem checkedDiv_eq_some_iff {a b c : Nat} :
    checkedDiv a b = some c ↔ b ≠ 0 ∧ c = a / b := by
  unfold checkedDiv
  split <;> simp_all [eq_comm]

theorem checkedDiv_eq_none_iff {a b : Nat} : checkedDiv a b = none ↔ b = 0 := by
  unfold checkedDiv
  split <;> simp_all

/-- A successful checked result is representable whenever the inputs are. -/
theorem checkedSub_fits {bits a b c : Nat} (ha : UnsignedFits bits a)
    (h : checkedSub a b = some c) : UnsignedFits bits c := by
  rw [checkedSub_eq_some_iff] at h
  unfold UnsignedFits at *
  omega

theorem saturatingAdd_lt (bits a b : Nat) : saturatingAdd bits a b < 2 ^ bits := by
  have := Nat.one_le_two_pow (n := bits)
  unfold saturatingAdd
  omega

theorem saturatingMul_lt (bits a b : Nat) : saturatingMul bits a b < 2 ^ bits := by
  have := Nat.one_le_two_pow (n := bits)
  unfold saturatingMul
  omega

theorem saturatingAdd_eq_of_fits {bits a b : Nat} (h : UnsignedFits bits (a + b)) :
    saturatingAdd bits a b = a + b := by
  unfold saturatingAdd UnsignedFits at *
  omega

theorem saturatingMul_eq_of_fits {bits a b : Nat} (h : UnsignedFits bits (a * b)) :
    saturatingMul bits a b = a * b := by
  unfold saturatingMul UnsignedFits at *
  omega

theorem wrappingAdd_eq_of_fits {bits a b : Nat} (h : UnsignedFits bits (a + b)) :
    wrappingAdd bits a b = a + b :=
  Nat.mod_eq_of_lt h

theorem wrappingAdd_lt (bits a b : Nat) : wrappingAdd bits a b < 2 ^ bits :=
  Nat.mod_lt _ (Nat.two_pow_pos bits)

theorem wrappingMul_lt (bits a b : Nat) : wrappingMul bits a b < 2 ^ bits :=
  Nat.mod_lt _ (Nat.two_pow_pos bits)

/-! ## Agreement with `UInt64` -/

/-- A successful 64-bit `checkedAdd` is `UInt64` addition. -/
theorem checkedAdd_uint64 {a b : UInt64} {c : Nat} (h : checkedAdd 64 a.toNat b.toNat = some c) :
    (a + b).toNat = c := by
  rw [checkedAdd_eq_some_iff, UnsignedFits] at h
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h.1, h.2]

/-- A successful `checkedSub` on `UInt64` values is `UInt64` subtraction. -/
theorem checkedSub_uint64 {a b : UInt64} {c : Nat} (h : checkedSub a.toNat b.toNat = some c) :
    (a - b).toNat = c := by
  rw [checkedSub_eq_some_iff] at h
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h.1), h.2]

/-- A successful 64-bit `checkedMul` is `UInt64` multiplication. -/
theorem checkedMul_uint64 {a b : UInt64} {c : Nat} (h : checkedMul 64 a.toNat b.toNat = some c) :
    (a * b).toNat = c := by
  rw [checkedMul_eq_some_iff, UnsignedFits] at h
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt h.1, h.2]

/-- 64-bit `wrappingAdd` is `UInt64` addition. -/
theorem wrappingAdd_uint64 (a b : UInt64) : wrappingAdd 64 a.toNat b.toNat = (a + b).toNat := by
  rw [UInt64.toNat_add, wrappingAdd]

/-- 64-bit `wrappingMul` is `UInt64` multiplication. -/
theorem wrappingMul_uint64 (a b : UInt64) : wrappingMul 64 a.toNat b.toNat = (a * b).toNat := by
  rw [UInt64.toNat_mul, wrappingMul]

/-! ## Signed integers -/

/-- The least `bits`-wide signed integer, `-2^(bits-1)` (e.g. `i64::MIN`). -/
def signedMin (bits : Nat) : Int := -2 ^ (bits - 1)

/-- The greatest `bits`-wide signed integer, `2^(bits-1) - 1` (e.g. `i64::MAX`). -/
def signedMax (bits : Nat) : Int := 2 ^ (bits - 1) - 1

/-- `x` is representable as a `bits`-wide signed integer. -/
def SignedFits (bits : Nat) (x : Int) : Prop := signedMin bits ≤ x ∧ x ≤ signedMax bits

instance (bits : Nat) (x : Int) : Decidable (SignedFits bits x) := by
  unfold SignedFits; exact inferInstance

/-- Clamp `x` into the `bits`-wide signed range, the result of the signed
`saturating_*` operations. -/
def saturate (bits : Nat) (x : Int) : Int := max (signedMin bits) (min (signedMax bits) x)

/-- `checked_add` on `bits`-wide signed integers. -/
def checkedAddSigned (bits : Nat) (a b : Int) : Option Int :=
  if SignedFits bits (a + b) then some (a + b) else none

/-- `checked_sub` on `bits`-wide signed integers. -/
def checkedSubSigned (bits : Nat) (a b : Int) : Option Int :=
  if SignedFits bits (a - b) then some (a - b) else none

/-- `checked_mul` on `bits`-wide signed integers. -/
def checkedMulSigned (bits : Nat) (a b : Int) : Option Int :=
  if SignedFits bits (a * b) then some (a * b) else none

theorem signedMin_le_signedMax (bits : Nat) : signedMin bits ≤ signedMax bits := by
  have : (0 : Int) < 2 ^ (bits - 1) := Int.pow_pos (by decide)
  unfold signedMin signedMax
  omega

theorem checkedAddSigned_eq_some_iff {bits : Nat} {a b c : Int} :
    checkedAddSigned bits a b = some c ↔ SignedFits bits (a + b) ∧ c = a + b := by
  unfold checkedAddSigned
  split <;> simp_all [eq_comm]

theorem checkedSubSigned_eq_some_iff {bits : Nat} {a b c : Int} :
    checkedSubSigned bits a b = some c ↔ SignedFits bits (a - b) ∧ c = a - b := by
  unfold checkedSubSigned
  split <;> simp_all [eq_comm]

theorem checkedMulSigned_eq_some_iff {bits : Nat} {a b c : Int} :
    checkedMulSigned bits a b = some c ↔ SignedFits bits (a * b) ∧ c = a * b := by
  unfold checkedMulSigned
  split <;> simp_all [eq_comm]

/-- Saturation always produces a representable value. -/
theorem saturate_fits (bits : Nat) (x : Int) : SignedFits bits (saturate bits x) := by
  have := signedMin_le_signedMax bits
  unfold SignedFits saturate
  omega

/-- Saturation leaves representable values unchanged. -/
theorem saturate_eq_self {bits : Nat} {x : Int} (h : SignedFits bits x) : saturate bits x = x := by
  unfold SignedFits saturate at *
  omega

/-- Saturation is monotone: clamping preserves the order of its inputs. -/
theorem saturate_mono (bits : Nat) {x y : Int} (h : x ≤ y) : saturate bits x ≤ saturate bits y := by
  unfold saturate
  omega

end Solanalib.Numeric
