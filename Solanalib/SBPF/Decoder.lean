/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.CommType
import Solanalib.SBPF.Syntax

/-!
# SBPF.Decoder — sBPF bytecode decoding

Decoding of binary sBPF into the abstract `BpfInstruction` syntax, ported from
`rBPFDecoder.thy`. `decode` maps a single opcode + operand fields to an
instruction; `findInstr` slices the 8- (or 16-) byte instruction out of a byte
list at a given program counter and decodes it.

## Main definitions
* `Solanalib.SBPF.decode` — decode one instruction from its fields.
* `Solanalib.SBPF.findInstr` — locate and decode the instruction at a PC.
-/

namespace Solanalib.SBPF

/-- The size of an encoded instruction slot, in bytes. -/
def insnSize : Nat := 8

/-- Decode a single sBPF instruction from its opcode and operand fields
(`rbpf_decoder`). Both register fields must name a valid register (`0`–`10`),
except the `0x07` stack-pointer form which uses the sentinel destination `11`. -/
def decode (opc : U8) (dv sv : U4) (off : U16) (imm : U32) : Option BpfInstruction :=
  if opc = 0x07 then
    if dv = 11 then some (.add_stk imm)
    else match BpfIReg.ofU4 dv with
      | none => none
      | some dst => some (.alu64 .add dst (.imm imm))
  else
    match BpfIReg.ofU4 dv, BpfIReg.ofU4 sv with
    | some dst, some src =>
      -- Load / store
      if opc = 0x71 then some (.ldx .m8 dst src off)
      else if opc = 0x69 then some (.ldx .m16 dst src off)
      else if opc = 0x61 then some (.ldx .m32 dst src off)
      else if opc = 0x79 then some (.ldx .m64 dst src off)
      else if opc = 0x72 then some (.st .m8 dst (.imm imm) off)
      else if opc = 0x6a then some (.st .m16 dst (.imm imm) off)
      else if opc = 0x62 then some (.st .m32 dst (.imm imm) off)
      else if opc = 0x7a then some (.st .m64 dst (.imm imm) off)
      else if opc = 0x73 then some (.st .m8 dst (.reg src) off)
      else if opc = 0x6b then some (.st .m16 dst (.reg src) off)
      else if opc = 0x63 then some (.st .m32 dst (.reg src) off)
      else if opc = 0x7b then some (.st .m64 dst (.reg src) off)
      -- 32-bit ALU
      else if opc = 0x04 then some (.alu .add dst (.imm imm))
      else if opc = 0x0c then some (.alu .add dst (.reg src))
      else if opc = 0x14 then some (.alu .sub dst (.imm imm))
      else if opc = 0x1c then some (.alu .sub dst (.reg src))
      else if opc = 0x24 then some (.alu .mul dst (.imm imm))
      else if opc = 0x2c then some (.alu .mul dst (.reg src))
      else if opc = 0x34 then some (.alu .div dst (.imm imm))
      else if opc = 0x3c then some (.alu .div dst (.reg src))
      else if opc = 0x44 then some (.alu .or dst (.imm imm))
      else if opc = 0x4c then some (.alu .or dst (.reg src))
      else if opc = 0x54 then some (.alu .and dst (.imm imm))
      else if opc = 0x5c then some (.alu .and dst (.reg src))
      else if opc = 0x64 then some (.alu .lsh dst (.imm imm))
      else if opc = 0x6c then some (.alu .lsh dst (.reg src))
      else if opc = 0x74 then some (.alu .rsh dst (.imm imm))
      else if opc = 0x7c then some (.alu .rsh dst (.reg src))
      else if opc = 0x84 then some (.neg32_reg dst)
      else if opc = 0x94 then some (.alu .mod dst (.imm imm))
      else if opc = 0x9c then some (.alu .mod dst (.reg src))
      else if opc = 0xa4 then some (.alu .xor dst (.imm imm))
      else if opc = 0xac then some (.alu .xor dst (.reg src))
      else if opc = 0xb4 then some (.alu .mov dst (.imm imm))
      else if opc = 0xbc then some (.alu .mov dst (.reg src))
      else if opc = 0xc4 then some (.alu .arsh dst (.imm imm))
      else if opc = 0xcc then some (.alu .arsh dst (.reg src))
      else if opc = 0xd4 then some (.le dst imm)
      else if opc = 0xdc then some (.be dst imm)
      -- 64-bit ALU
      else if opc = 0x0f then some (.alu64 .add dst (.reg src))
      else if opc = 0x17 then some (.alu64 .sub dst (.imm imm))
      else if opc = 0x1f then some (.alu64 .sub dst (.reg src))
      else if opc = 0x27 then some (.alu64 .mul dst (.imm imm))
      else if opc = 0x2f then some (.alu64 .mul dst (.reg src))
      else if opc = 0x37 then some (.alu64 .div dst (.imm imm))
      else if opc = 0x3f then some (.alu64 .div dst (.reg src))
      else if opc = 0x47 then some (.alu64 .or dst (.imm imm))
      else if opc = 0x4f then some (.alu64 .or dst (.reg src))
      else if opc = 0x57 then some (.alu64 .and dst (.imm imm))
      else if opc = 0x5f then some (.alu64 .and dst (.reg src))
      else if opc = 0x67 then some (.alu64 .lsh dst (.imm imm))
      else if opc = 0x6f then some (.alu64 .lsh dst (.reg src))
      else if opc = 0x77 then some (.alu64 .rsh dst (.imm imm))
      else if opc = 0x7f then some (.alu64 .rsh dst (.reg src))
      else if opc = 0x87 then some (.neg64_reg dst)
      else if opc = 0x97 then some (.alu64 .mod dst (.imm imm))
      else if opc = 0x9f then some (.alu64 .mod dst (.reg src))
      else if opc = 0xa7 then some (.alu64 .xor dst (.imm imm))
      else if opc = 0xaf then some (.alu64 .xor dst (.reg src))
      else if opc = 0xb7 then some (.alu64 .mov dst (.imm imm))
      else if opc = 0xbf then some (.alu64 .mov dst (.reg src))
      else if opc = 0xc7 then some (.alu64 .arsh dst (.imm imm))
      else if opc = 0xcf then some (.alu64 .arsh dst (.reg src))
      else if opc = 0xf7 then some (.hor64_imm dst imm)
      -- Product / quotient / remainder
      else if opc = 0x86 then some (.pqr .lmul dst (.imm imm))
      else if opc = 0x8e then some (.pqr .lmul dst (.reg src))
      else if opc = 0x96 then some (.pqr64 .lmul dst (.imm imm))
      else if opc = 0x9e then some (.pqr64 .lmul dst (.reg src))
      else if opc = 0x36 then some (.pqr2 .uhmul dst (.imm imm))
      else if opc = 0x3e then some (.pqr2 .uhmul dst (.reg src))
      else if opc = 0xb6 then some (.pqr2 .shmul dst (.imm imm))
      else if opc = 0xbe then some (.pqr2 .shmul dst (.reg src))
      else if opc = 0x46 then some (.pqr .udiv dst (.imm imm))
      else if opc = 0x4e then some (.pqr .udiv dst (.reg src))
      else if opc = 0x56 then some (.pqr64 .udiv dst (.imm imm))
      else if opc = 0x5e then some (.pqr64 .udiv dst (.reg src))
      else if opc = 0x66 then some (.pqr .urem dst (.imm imm))
      else if opc = 0x6e then some (.pqr .urem dst (.reg src))
      else if opc = 0x76 then some (.pqr64 .urem dst (.imm imm))
      else if opc = 0x7e then some (.pqr64 .urem dst (.reg src))
      else if opc = 0xc6 then some (.pqr .sdiv dst (.imm imm))
      else if opc = 0xce then some (.pqr .sdiv dst (.reg src))
      else if opc = 0xd6 then some (.pqr64 .sdiv dst (.imm imm))
      else if opc = 0xde then some (.pqr64 .sdiv dst (.reg src))
      else if opc = 0xe6 then some (.pqr .srem dst (.imm imm))
      else if opc = 0xee then some (.pqr .srem dst (.reg src))
      else if opc = 0xf6 then some (.pqr64 .srem dst (.imm imm))
      else if opc = 0xfe then some (.pqr64 .srem dst (.reg src))
      -- Jumps
      else if opc = 0x05 then some (.ja off)
      else if opc = 0x15 then some (.jump .eq dst (.imm imm) off)
      else if opc = 0x1d then some (.jump .eq dst (.reg src) off)
      else if opc = 0x25 then some (.jump .gt dst (.imm imm) off)
      else if opc = 0x2d then some (.jump .gt dst (.reg src) off)
      else if opc = 0x35 then some (.jump .ge dst (.imm imm) off)
      else if opc = 0x3d then some (.jump .ge dst (.reg src) off)
      else if opc = 0xa5 then some (.jump .lt dst (.imm imm) off)
      else if opc = 0xad then some (.jump .lt dst (.reg src) off)
      else if opc = 0xb5 then some (.jump .le dst (.imm imm) off)
      else if opc = 0xbd then some (.jump .le dst (.reg src) off)
      else if opc = 0x45 then some (.jump .sEt dst (.imm imm) off)
      else if opc = 0x4d then some (.jump .sEt dst (.reg src) off)
      else if opc = 0x55 then some (.jump .ne dst (.imm imm) off)
      else if opc = 0x5d then some (.jump .ne dst (.reg src) off)
      else if opc = 0x65 then some (.jump .sGt dst (.imm imm) off)
      else if opc = 0x6d then some (.jump .sGt dst (.reg src) off)
      else if opc = 0x75 then some (.jump .sGe dst (.imm imm) off)
      else if opc = 0x7d then some (.jump .sGe dst (.reg src) off)
      else if opc = 0xc5 then some (.jump .sLt dst (.imm imm) off)
      else if opc = 0xcd then some (.jump .sLt dst (.reg src) off)
      else if opc = 0xd5 then some (.jump .sLe dst (.imm imm) off)
      else if opc = 0xdd then some (.jump .sLe dst (.reg src) off)
      -- Calls / exit
      else if opc = 0x8d then some (.call_reg src imm)
      else if opc = 0x85 then some (.call_imm src imm)
      else if opc = 0x95 then some .exit
      else none
    | _, _ => none

/-- Little-endian `U16` from two bytes of a byte list at offset `i`. -/
private def le16 (l : BpfBin) (i : Nat) : U16 :=
  ((l.getD i 0).setWidth 16) ||| (((l.getD (i + 1) 0).setWidth 16) <<< 8)

/-- Little-endian `U32` from four bytes of a byte list at offset `i`. -/
private def le32 (l : BpfBin) (i : Nat) : U32 :=
  ((l.getD i 0).setWidth 32) |||
  (((l.getD (i + 1) 0).setWidth 32) <<< 8) |||
  (((l.getD (i + 2) 0).setWidth 32) <<< 16) |||
  (((l.getD (i + 3) 0).setWidth 32) <<< 24)

/-- Locate and decode the instruction at program counter `pc` in byte list `l`
(`bpf_find_instr`). Handles the 16-byte `0x18` load-immediate form. -/
def findInstr (pc : Nat) (l : BpfBin) : Option BpfInstruction :=
  let npc := pc * insnSize
  if l.length < npc + 8 then none
  else
    let op := l.getD npc 0
    let reg := l.getD (npc + 1) 0
    let dst := reg.setWidth 4
    let src := (reg >>> 4).setWidth 4
    let off := le16 l (npc + 2)
    let imm := le32 l (npc + 4)
    if op = 0x18 then
      if l.length < npc + 16 then none
      else
        let imm2 := le32 l (npc + 12)
        (BpfIReg.ofU4 dst).map fun dstR => .ld_imm dstR imm imm2
    else decode op dst src off imm

end Solanalib.SBPF
