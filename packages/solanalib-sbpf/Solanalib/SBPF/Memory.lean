/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.CommType
import Solanalib.SBPF.Value

/-!
# SBPF.Memory — the sBPF memory model

Byte-addressable memory, access widths, and the load / store operations of the
sBPF semantics, ported from `Mem.thy`. Memory is a partial map from 64-bit
address to byte; loads and stores are little-endian and operate at one of four
access widths.

## Main definitions
* `Solanalib.SBPF.MemoryChunk` — access width (`m8` … `m64`).
* `Solanalib.SBPF.Mem` — the byte-addressable address space.
* `Solanalib.SBPF.loadv` — read a `Val` of a given width (`none` if unmapped).
* `Solanalib.SBPF.storev` — write a `Val`, returning the updated memory.
* `Solanalib.SBPF.chunkSize` — the number of bytes an access width covers.

## Main statements
* `Solanalib.SBPF.loadv_storev_same` — a load reads back what a store at the
  same address and width wrote.
* `Solanalib.SBPF.loadv_storev_disjoint` — a store leaves a load from a
  disjoint range unchanged.
-/

namespace Solanalib.SBPF

/-- Access width for a memory operation (the source theory's `memory_chunk`). -/
inductive MemoryChunk
  | m8
  | m16
  | m32
  | m64
  deriving DecidableEq, Repr

/-- Byte-addressable memory: a partial map from 64-bit address to byte.

Modelled as a total function into `Option U8` (`none` = unmapped), matching the
source theory's `(u64, u8) map`. -/
abbrev Mem := U64 → Option U8

/-- The empty address space — every byte unmapped. -/
def initMem : Mem := fun _ => none

/-- The width of a chunk, as a 64-bit value (`vlong_of_memory_chunk`). -/
def vlongOfMemoryChunk : MemoryChunk → Val
  | .m8 => .vlong 8
  | .m16 => .vlong 16
  | .m32 => .vlong 32
  | .m64 => .vlong 64

/-- Tag a 64-bit word as the value of the given access width, truncating to the
width (`memory_chunk_value_of_u64`). -/
def memoryChunkValueOfU64 (mc : MemoryChunk) (v : U64) : Val :=
  match mc with
  | .m8 => .vbyte (v.setWidth 8)
  | .m16 => .vshort (v.setWidth 16)
  | .m32 => .vint (v.setWidth 32)
  | .m64 => .vlong v

/-- Read a value of the given width at `addr`, little-endian. Yields `none` if
any byte in the accessed range is unmapped. -/
def loadv (mc : MemoryChunk) (m : Mem) (addr : U64) : Option Val :=
  match mc with
  | .m8 => (m addr).map fun b0 => Val.vbyte b0
  | .m16 => do
      let b0 ← m addr
      let b1 ← m (addr + 1)
      pure (Val.vshort ((b0.setWidth 16) ||| ((b1.setWidth 16) <<< 8)))
  | .m32 => do
      let b0 ← m addr
      let b1 ← m (addr + 1)
      let b2 ← m (addr + 2)
      let b3 ← m (addr + 3)
      pure (Val.vint
        ((b0.setWidth 32) ||| ((b1.setWidth 32) <<< 8) |||
         ((b2.setWidth 32) <<< 16) ||| ((b3.setWidth 32) <<< 24)))
  | .m64 => do
      let b0 ← m addr
      let b1 ← m (addr + 1)
      let b2 ← m (addr + 2)
      let b3 ← m (addr + 3)
      let b4 ← m (addr + 4)
      let b5 ← m (addr + 5)
      let b6 ← m (addr + 6)
      let b7 ← m (addr + 7)
      pure (Val.vlong
        ((b0.setWidth 64) ||| ((b1.setWidth 64) <<< 8) |||
         ((b2.setWidth 64) <<< 16) ||| ((b3.setWidth 64) <<< 24) |||
         ((b4.setWidth 64) <<< 32) ||| ((b5.setWidth 64) <<< 40) |||
         ((b6.setWidth 64) <<< 48) ||| ((b7.setWidth 64) <<< 56)))

/-- Write a value of the given width at `addr`, little-endian. Yields `none` if
the value's tag does not match the access width. -/
def storev (mc : MemoryChunk) (m : Mem) (addr : U64) (v : Val) : Option Mem :=
  match mc, v with
  | .m8, .vbyte n => some fun i => if i = addr then some n else m i
  | .m16, .vshort n =>
      match u8ListOfU16 n with
      | [b0, b1] =>
          some fun i =>
            if i = addr then some b0
            else if i = addr + 1 then some b1
            else m i
      | _ => none
  | .m32, .vint n =>
      match u8ListOfU32 n with
      | [b0, b1, b2, b3] =>
          some fun i =>
            if i = addr then some b0
            else if i = addr + 1 then some b1
            else if i = addr + 2 then some b2
            else if i = addr + 3 then some b3
            else m i
      | _ => none
  | .m64, .vlong n =>
      match u8ListOfU64 n with
      | [b0, b1, b2, b3, b4, b5, b6, b7] =>
          some fun i =>
            if i = addr then some b0
            else if i = addr + 1 then some b1
            else if i = addr + 2 then some b2
            else if i = addr + 3 then some b3
            else if i = addr + 4 then some b4
            else if i = addr + 5 then some b5
            else if i = addr + 6 then some b6
            else if i = addr + 7 then some b7
            else m i
      | _ => none
  | _, _ => none

/-- The number of bytes an access width covers. -/
def chunkSize : MemoryChunk → U64
  | .m8 => 1
  | .m16 => 2
  | .m32 => 4
  | .m64 => 8

/-- A load reads back what a store at the same address and width wrote. -/
theorem loadv_storev_same {mc : MemoryChunk} {m m' : Mem} {a : U64} {v : Val}
    (h : storev mc m a v = some m') : loadv mc m' a = some v := by
  cases mc <;> cases v <;> simp [storev, u8ListOfU16, u8ListOfU32, u8ListOfU64] at h <;>
    subst h <;> simp [loadv] <;> ext i hi <;>
    simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight] <;>
    rw [← BitVec.getLsbD_eq_getElem] <;>
    rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
      (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ 56 ≤ i) with
      h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h <;>
    simp (disch := omega) [decide_eq_true, decide_eq_false, Nat.add_sub_cancel']

/-- A store at `a` leaves a load at `b` unchanged when the two byte ranges are
disjoint. Distances are taken modulo `2^64`, so ranges that wrap around the
address space are covered without overflow side conditions. -/
theorem loadv_storev_disjoint {ms ml : MemoryChunk} {m m' : Mem} {a b : U64} {v : Val}
    (h : storev ms m a v = some m') (hab : chunkSize ms ≤ b - a)
    (hba : chunkSize ml ≤ a - b) : loadv ml m' b = loadv ml m b := by
  have hs : chunkSize ms ≤ 8 := by cases ms <;> decide
  have hl : chunkSize ml ≤ 8 := by cases ml <;> decide
  have hs0 : 0 < chunkSize ms := by cases ms <;> decide
  have hl0 : 0 < chunkSize ml := by cases ml <;> decide
  have key : ∀ i j : U64, i < chunkSize ms → j < chunkSize ml → (b + j = a + i) = False := by
    intro i j hi hj
    simp only [eq_iff_iff, iff_false]
    intro e
    bv_omega
  have key0 : ∀ j : U64, j < chunkSize ml → (b + j = a) = False := fun j hj => by
    simpa using key 0 j hs0 hj
  have key1 : ∀ i : U64, i < chunkSize ms → (b = a + i) = False := fun i hi => by
    simpa using key i 0 hi hl0
  have key2 : (b = a) = False := by simpa using key0 0 hl0
  cases ms <;> cases v <;> simp [storev, u8ListOfU16, u8ListOfU32, u8ListOfU64] at h <;>
    subst h <;> cases ml <;> simp (disch := decide) [loadv, key, key0, key1, key2]

end Solanalib.SBPF
