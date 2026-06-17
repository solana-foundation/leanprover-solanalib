/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Init

/-!
# Fraction: Q68.60 fixed-point numbers for Solana finance

A fixed-point number with 60 fractional bits, modelled here at the
**spec layer** with an unbounded `Nat` underlying representation
(so `omega` works without ceremony). A future `Fraction128` companion
will refine this to the `u128`-bounded on-chain shape used by Kamino
and other DeFi protocols (Kamino's `U68F60`).

A `Fraction` `f` represents the real number `f.bits / 2^60`.

This module is **Layer 1** in the long-term Solanalib stack: a numeric
foundation that every domain primitive (interest curves, exchange
rates, slippage, vesting fractions, …) sits on top of. The conscious
choice to use `Nat` rather than `u128` at this layer follows the
seL4 / CompCert pattern — prove mathematical properties on the
abstract model, refine to the bounded representation separately.

## Main definitions

* `Fraction` — a fixed-point number, conceptually `bits / 2^60`.
* `Fraction.zero`, `Fraction.one` — the additive and multiplicative units.
* `Fraction.fromNat` / `Fraction.toFloor` — integer/fraction conversions.
* `Fraction.add`, `Fraction.mul` — arithmetic at the fixed-point scale.

## Main statements (this commit)

A minimal kit:

* `add_zero`, `zero_add`, `add_comm` — `Fraction.add` is a commutative monoid.
* `mul_one`, `one_mul` — `Fraction.one` is the multiplicative identity.

Multiplication is *approximately* associative — the truncating division
by `scale` after each multiplication introduces a rounding error of at
most one ULP. A bound on that error is deferred to a follow-up file.

## Conventions

The "scale" exponent (60) is exposed as `Fraction.scaleBits` so future
refinements that need a different precision (e.g. Q.32, Q.96) can be
parameterised cleanly.
-/

namespace Solanalib

/-- A fixed-point number with `scaleBits` fractional bits, where
`scaleBits = 60` to match the `U68F60` convention common in Solana DeFi.

`Fraction.mk b` represents the real number `b / 2^60`. -/
@[ext]
structure Fraction where
  /-- The underlying integer encoding: `bits = realValue * 2^60`. -/
  bits : Nat
  deriving Repr, DecidableEq

namespace Fraction

/-- The number of fractional bits in the representation. -/
def scaleBits : Nat := 60

/-- The scale factor: `2^scaleBits = 2^60`. Every operation that
preserves the fixed-point invariant divides intermediate products by
this constant. -/
def scale : Nat := 2 ^ scaleBits

/-- `scale > 0` — useful for division-cancellation lemmas. -/
theorem scale_pos : 0 < scale := Nat.pow_pos (by decide : 0 < 2)

/-- The additive identity. -/
def zero : Fraction := ⟨0⟩

/-- The multiplicative identity: encoding of `1.0`. -/
def one : Fraction := ⟨scale⟩

/-- Convert an integer `n` to its fixed-point encoding `n * 2^60`. -/
def fromNat (n : Nat) : Fraction := ⟨n * scale⟩

/-- Project a fraction to its integer floor: `bits / 2^60`. -/
def toFloor (f : Fraction) : Nat := f.bits / scale

/-- Addition: just sum the bits. The fixed-point scale is preserved
because both operands share it. -/
def add (a b : Fraction) : Fraction := ⟨a.bits + b.bits⟩

/-- Multiplication: `(a.bits * b.bits) / scale`. The division corrects
the doubled scale that would otherwise result from `bits * bits`.
This operation truncates — see the file docstring on associativity. -/
def mul (a b : Fraction) : Fraction := ⟨a.bits * b.bits / scale⟩

/-! ## Theorems -/

@[simp] theorem add_bits (a b : Fraction) : (a.add b).bits = a.bits + b.bits := rfl
@[simp] theorem mul_bits (a b : Fraction) : (a.mul b).bits = a.bits * b.bits / scale := rfl
@[simp] theorem zero_bits : zero.bits = 0 := rfl
@[simp] theorem one_bits : one.bits = scale := rfl

theorem add_zero (a : Fraction) : a.add zero = a := by
  ext; simp

theorem zero_add (a : Fraction) : zero.add a = a := by
  ext; simp

theorem add_comm (a b : Fraction) : a.add b = b.add a := by
  ext; simp [Nat.add_comm]

theorem mul_one (a : Fraction) : a.mul one = a := by
  ext
  show a.bits * one.bits / scale = a.bits
  rw [one_bits, Nat.mul_div_cancel _ scale_pos]

theorem one_mul (a : Fraction) : one.mul a = a := by
  ext
  show one.bits * a.bits / scale = a.bits
  rw [one_bits, Nat.mul_comm, Nat.mul_div_cancel _ scale_pos]

end Fraction
end Solanalib
