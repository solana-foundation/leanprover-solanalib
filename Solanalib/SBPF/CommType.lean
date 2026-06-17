/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Init

/-!
# SBPF.CommType — machine words for the sBPF ISA

Fixed-width machine words underpinning the Solana eBPF (sBPF) semantics, ported
from the OOPSLA 2025 Isabelle/HOL formalisation (`rBPFCommType.thy`, Yuan et al.,
*A Complete Formal Semantics of eBPF ISA for Solana*).

Every width is modelled as `BitVec n`: a bit container with no inherent
signedness. Signed vs. unsigned behaviour is a property of the *operation*
(`BitVec.sdiv` / `.smod` / `.sshiftRight` vs `/` / `%` / `>>>`), exactly as on
real hardware — so a single representation serves both the `word` and `sword`
roles of the source theory.

## Main definitions
* `Solanalib.SBPF.U4` … `U128` — the machine-word widths.
* `Solanalib.SBPF.u8ListOfU64` and friends — little-endian byte serialisation.
* `Solanalib.SBPF.u64OfU8List` and friends — the parsing inverse.
-/

namespace Solanalib.SBPF

/-- 4-bit word — the register-index field of an encoded instruction. -/
abbrev U4 := BitVec 4
/-- 8-bit word — a byte. -/
abbrev U8 := BitVec 8
/-- 16-bit word — the instruction offset field. -/
abbrev U16 := BitVec 16
/-- 32-bit word — the instruction immediate field. -/
abbrev U32 := BitVec 32
/-- 64-bit word — the register width. -/
abbrev U64 := BitVec 64
/-- 128-bit word — wide-multiply results. -/
abbrev U128 := BitVec 128

/-- Smallest signed 8-bit value (`-128`), as raw bits. -/
def i8Min : U8 := 0x80
/-- Largest signed 8-bit value (`127`). -/
def i8Max : U8 := 0x7F
/-- Largest unsigned 8-bit value (`255`). -/
def u8Max : U8 := 0xFF
/-- Smallest signed 32-bit value, as raw bits. -/
def i32Min : U32 := 0x80000000
/-- Largest signed 32-bit value. -/
def i32Max : U32 := 0x7FFFFFFF
/-- Largest unsigned 32-bit value. -/
def u32Max : U32 := 0xFFFFFFFF
/-- Smallest signed 64-bit value, as raw bits. -/
def i64Min : U64 := 0x8000000000000000
/-- Largest signed 64-bit value. -/
def i64Max : U64 := 0x7FFFFFFFFFFFFFFF
/-- Largest unsigned 64-bit value. -/
def u64Max : U64 := 0xFFFFFFFFFFFFFFFF

/-- A byte encoding of a boolean: `1` for `true`, `0` for `false`. -/
def u8OfBool (b : Bool) : U8 := if b then 1 else 0

/-- Little-endian bytes of a 16-bit word. -/
def u8ListOfU16 (i : U16) : List U8 :=
  [(i.setWidth 8), ((i >>> 8).setWidth 8)]

/-- Little-endian bytes of a 32-bit word. -/
def u8ListOfU32 (i : U32) : List U8 :=
  [ (i.setWidth 8), ((i >>> 8).setWidth 8),
    ((i >>> 16).setWidth 8), ((i >>> 24).setWidth 8) ]

/-- Little-endian bytes of a 64-bit word. -/
def u8ListOfU64 (i : U64) : List U8 :=
  [ (i.setWidth 8), ((i >>> 8).setWidth 8),
    ((i >>> 16).setWidth 8), ((i >>> 24).setWidth 8),
    ((i >>> 32).setWidth 8), ((i >>> 40).setWidth 8),
    ((i >>> 48).setWidth 8), ((i >>> 56).setWidth 8) ]

/-- Reassemble a little-endian 2-byte list into a 16-bit word. -/
def u16OfU8List : List U8 → Option U16
  | [b0, b1] => some ((b0.setWidth 16) ||| ((b1.setWidth 16) <<< 8))
  | _ => none

/-- Reassemble a little-endian 4-byte list into a 32-bit word. -/
def u32OfU8List : List U8 → Option U32
  | [b0, b1, b2, b3] =>
      some <|
        (b0.setWidth 32) |||
        ((b1.setWidth 32) <<< 8) |||
        ((b2.setWidth 32) <<< 16) |||
        ((b3.setWidth 32) <<< 24)
  | _ => none

/-- Reassemble a little-endian 8-byte list into a 64-bit word. -/
def u64OfU8List : List U8 → Option U64
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
      some <|
        (b0.setWidth 64) |||
        ((b1.setWidth 64) <<< 8) |||
        ((b2.setWidth 64) <<< 16) |||
        ((b3.setWidth 64) <<< 24) |||
        ((b4.setWidth 64) <<< 32) |||
        ((b5.setWidth 64) <<< 40) |||
        ((b6.setWidth 64) <<< 48) |||
        ((b7.setWidth 64) <<< 56)
  | _ => none

end Solanalib.SBPF
