/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.Decoder

/-!
# Regression tests for `Solanalib.SBPF.Decoder`

Pins decoding of representative opcodes and the byte-slicing of `findInstr`,
including the 16-byte `0x18` load-immediate form and the `0x07` stack-pointer
special case (the worked example from `rBPFDecoder.thy`).
-/

namespace SolanalibTest.SBPF.Decoder

open Solanalib.SBPF

/-! ## `decode` — single instructions -/

/-- `0x95` is `exit`. -/
example : decode 0x95 0 0 0 0 = some .exit := by decide

/-- `0x0f` is the 64-bit register add. -/
example : decode 0x0f 1 2 0 0 = some (.alu64 .add .br1 (.reg .br2)) := by decide

/-- `0x07` with destination sentinel `11` is the stack-pointer add. -/
example : decode 0x07 11 0 0 0x2a = some (.addStk 0x2a) := by decide

/-- `0x07` with a real destination is the 64-bit immediate add. -/
example : decode 0x07 3 0 0 0x2a = some (.alu64 .add .br3 (.imm 0x2a)) := by decide

/-- An out-of-range destination register decodes to nothing. -/
example : decode 0x04 12 0 0 0 = none := by decide

/-! ## `findInstr` — byte slicing -/

/-- The `rBPFDecoder.thy` worked example: `0x07` / reg `0x0B` ⇒ `addStk`,
with the immediate read little-endian from bytes 4–7. -/
example :
    findInstr 0 [0x07, 0x0B, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04]
      = some (.addStk 0x04030201) := by decide

/-- A 64-bit register add, with `dst`/`src` unpacked from the register byte. -/
example :
    findInstr 0 [0x0f, 0x21, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
      = some (.alu64 .add .br1 (.reg .br2)) := by decide

/-- The 16-byte `0x18` load-immediate, assembling the two immediate halves. -/
example :
    findInstr 0
      [0x18, 0x01, 0x00, 0x00, 0x0a, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00, 0x0b, 0x00, 0x00, 0x00]
      = some (.ldImm .br1 0x0a 0x0b) := by decide

/-- Too few bytes for a full instruction ⇒ no decode. -/
example : (findInstr 0 [0x95, 0x00]).isNone := by decide

end SolanalibTest.SBPF.Decoder
