/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.CommType
import Solanalib.SBPF.Memory

/-!
# SBPF.Syntax — the sBPF instruction set

Abstract syntax of the Solana eBPF (sBPF) instruction set, ported from
`rBPFSyntax.thy`. The headline type is `Solanalib.SBPF.BpfInstruction`, the
22-constructor algebraic representation of a decoded instruction, together with
the register, operand, operation, condition, and version enumerations it uses.

## Main definitions
* `Solanalib.SBPF.BpfIReg` — the eleven integer registers `BR0` … `BR10`.
* `Solanalib.SBPF.SndOp` — an instruction's second operand (immediate or register).
* `Solanalib.SBPF.BpfInstruction` — a decoded sBPF instruction.
* `Solanalib.SBPF.BpfIReg.toU4` / `ofU4` — the register ↔ 4-bit-field bridge.
-/

namespace Solanalib.SBPF

/-- The eleven sBPF integer registers. `BR10` is the read-only frame pointer. -/
inductive BpfIReg
  | br0 | br1 | br2 | br3 | br4 | br5 | br6 | br7 | br8 | br9 | br10
  deriving DecidableEq, Repr

/-- An instruction's second operand: an immediate or a source register. -/
inductive SndOp
  | imm (i : U32)
  | reg (r : BpfIReg)
  deriving DecidableEq, Repr

/-- Operand width selector for ALU operations. -/
inductive Arch
  | a32
  | a64
  deriving DecidableEq, Repr

/-- The width, in bits, selected by an `Arch`. -/
def Arch.bits : Arch → Nat
  | .a32 => 32
  | .a64 => 64

/-- Branch condition for a conditional jump. The `s`-prefixed variants are the
signed comparisons. -/
inductive Condition
  | eq | gt | ge | lt | le | sEt | ne | sGt | sGe | sLt | sLe
  deriving DecidableEq, Repr

/-- Core ALU binary operations (shared by the 32- and 64-bit ALU classes). -/
inductive Binop
  | add | sub | mul | div | or | and | lsh | rsh | mod | xor | mov | arsh
  deriving DecidableEq, Repr

/-- Product/quotient/remainder operations (the sBPF `PQR` class). -/
inductive Pqrop
  | lmul | udiv | urem | sdiv | srem
  deriving DecidableEq, Repr

/-- High-half multiply operations (the sBPF `PQR2` class). -/
inductive Pqrop2
  | uhmul | shmul
  deriving DecidableEq, Repr

/-- Byte-swap / load width selector (the source theory's `chunk`). -/
inductive Chunk
  | byte | halfWord | sWord | dWord
  deriving DecidableEq, Repr

/-- sBPF bytecode version. `v1` is the legacy format; `v2` is current. -/
inductive SBPFV
  | v1
  | v2
  deriving DecidableEq, Repr

/-- A decoded sBPF instruction. Constructors mirror `rBPFSyntax.thy`'s
`bpf_instruction`; immediate fields are `U32`, offsets `U16`, interpreted signed
where the semantics requires it. -/
inductive BpfInstruction
  /-- Load a 64-bit immediate (assembled from two 32-bit halves). -/
  | ld_imm (dst : BpfIReg) (immLo immHi : U32)
  /-- Load from memory: `dst := mem[src + off]` at width `chunk`. -/
  | ldx (chunk : MemoryChunk) (dst src : BpfIReg) (off : U16)
  /-- Store to memory: `mem[dst + off] := src` at width `chunk`. -/
  | st (chunk : MemoryChunk) (dst : BpfIReg) (src : SndOp) (off : U16)
  /-- Add an immediate to the stack pointer. -/
  | add_stk (imm : U32)
  /-- 32-bit ALU operation. -/
  | alu (op : Binop) (dst : BpfIReg) (src : SndOp)
  /-- 32-bit register negation. -/
  | neg32_reg (dst : BpfIReg)
  /-- Little-endian byte swap. -/
  | le (dst : BpfIReg) (imm : U32)
  /-- Big-endian byte swap. -/
  | be (dst : BpfIReg) (imm : U32)
  /-- 64-bit ALU operation. -/
  | alu64 (op : Binop) (dst : BpfIReg) (src : SndOp)
  /-- 64-bit register negation. -/
  | neg64_reg (dst : BpfIReg)
  /-- OR a high-order 32-bit immediate into `dst` (`v2` only). -/
  | hor64_imm (dst : BpfIReg) (imm : U32)
  /-- 32-bit product/quotient/remainder operation. -/
  | pqr (op : Pqrop) (dst : BpfIReg) (src : SndOp)
  /-- 64-bit product/quotient/remainder operation. -/
  | pqr64 (op : Pqrop) (dst : BpfIReg) (src : SndOp)
  /-- High-half multiply operation. -/
  | pqr2 (op : Pqrop2) (dst : BpfIReg) (src : SndOp)
  /-- Unconditional jump by `off`. -/
  | ja (off : U16)
  /-- Conditional jump by `off` when `cond` holds between `r` and `src`. -/
  | jump (cond : Condition) (r : BpfIReg) (src : SndOp) (off : U16)
  /-- Call the function whose address is held in register `src`. -/
  | call_reg (src : BpfIReg) (imm : U32)
  /-- Call the function identified by immediate `imm`. -/
  | call_imm (src : BpfIReg) (imm : U32)
  /-- Return from the current frame, or halt at call depth 0. -/
  | exit
  deriving DecidableEq, Repr

/-- A program in assembly form: a list of decoded instructions. -/
abbrev EbpfAsm := List BpfInstruction

/-- A program in binary form: a flat list of bytes. -/
abbrev BpfBin := List U8

/-- The 4-bit register-index field for a register. -/
def BpfIReg.toU4 : BpfIReg → U4
  | .br0 => 0 | .br1 => 1 | .br2 => 2 | .br3 => 3
  | .br4 => 4 | .br5 => 5 | .br6 => 6 | .br7 => 7
  | .br8 => 8 | .br9 => 9 | .br10 => 10

/-- Decode a 4-bit register-index field, rejecting out-of-range values. -/
def BpfIReg.ofU4 (d : U4) : Option BpfIReg :=
  if d = 0 then some .br0
  else if d = 1 then some .br1
  else if d = 2 then some .br2
  else if d = 3 then some .br3
  else if d = 4 then some .br4
  else if d = 5 then some .br5
  else if d = 6 then some .br6
  else if d = 7 then some .br7
  else if d = 8 then some .br8
  else if d = 9 then some .br9
  else if d = 10 then some .br10
  else none

end Solanalib.SBPF
