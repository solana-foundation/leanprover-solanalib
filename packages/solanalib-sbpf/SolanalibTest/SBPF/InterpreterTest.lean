/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.Interpreter

/-!
# Regression tests for `Solanalib.SBPF.Interpreter`

End-to-end execution of small hand-assembled sBPF programs through `bpfInterp`,
pinning the final `BPF_Success` return value. Exercises 64-bit move/add, the
32-bit sign-extending add quirk, and a taken conditional branch.
-/

namespace SolanalibTest.SBPF.Interpreter

open Solanalib.SBPF

/-- Run a byte program from the initial state and project the success value. -/
def run (prog : BpfBin) : Option U64 :=
  match bpfInterp 64 prog (initBpfState initRegMap initMem 64 .v2) true 0x100000000 with
  | .success v => some v
  | _ => none

/-! ## Basic arithmetic -/

/-- `mov64 r0, 5; exit` returns `5`. -/
theorem mov64_imm_returned : run [0xb7, 0x00, 0, 0, 5, 0, 0, 0,
               0x95, 0, 0, 0, 0, 0, 0, 0] = some 5 := by decide +kernel

/-- `mov64 r0, 5; add64 r0, 3; exit` returns `8`. -/
theorem add64_imm_added :
    run [0xb7, 0x00, 0, 0, 5, 0, 0, 0,
         0x07, 0x00, 0, 0, 3, 0, 0, 0,
         0x95, 0, 0, 0, 0, 0, 0, 0] = some 8 := by decide +kernel

/-- `mov64 r0, 7; mov64 r1, 2; sub64 r0, r1; exit` returns `5` (register
subtraction is `dst - src` in both versions). -/
theorem sub64_reg_dst_minus_src :
    run [0xb7, 0x00, 0, 0, 7, 0, 0, 0,
         0xb7, 0x01, 0, 0, 2, 0, 0, 0,
         0x1f, 0x10, 0, 0, 0, 0, 0, 0,
         0x95, 0, 0, 0, 0, 0, 0, 0] = some 5 := by decide +kernel

/-- sBPF `v2` quirk: `sub` with an *immediate* computes `imm - dst`, not
`dst - imm`. `mov64 r0, 10; sub64 r0, 3; exit` yields `3 - 10` (wrapped), not
`7`. -/
theorem sub64_imm_v2_imm_minus_dst :
    run [0xb7, 0x00, 0, 0, 10, 0, 0, 0,
         0x17, 0x00, 0, 0, 3, 0, 0, 0,
         0x95, 0, 0, 0, 0, 0, 0, 0] = some ((3 : U64) - 10) := by decide +kernel

/-! ## Control flow -/

/-- `mov64 r0,1; mov64 r1,1; jeq r0,r1,+1; mov64 r0,99; exit` takes the branch,
skipping the `mov r0, 99`, so it returns `1`. -/
theorem jeq_taken_skips_next :
    run [0xb7, 0x00, 0, 0, 1, 0, 0, 0,
         0xb7, 0x01, 0, 0, 1, 0, 0, 0,
         0x1d, 0x10, 1, 0, 0, 0, 0, 0,
         0xb7, 0x00, 0, 0, 99, 0, 0, 0,
         0x95, 0, 0, 0, 0, 0, 0, 0] = some 1 := by decide +kernel

/-- The same program with `r1 = 2` does not branch, so it returns `99`. -/
theorem jeq_not_taken_falls_through :
    run [0xb7, 0x00, 0, 0, 1, 0, 0, 0,
         0xb7, 0x01, 0, 0, 2, 0, 0, 0,
         0x1d, 0x10, 1, 0, 0, 0, 0, 0,
         0xb7, 0x00, 0, 0, 99, 0, 0, 0,
         0x95, 0, 0, 0, 0, 0, 0, 0] = some 99 := by decide +kernel

/-! ## 32-bit sign extension

`add32 r0, 0x80000000` lands a value with bit 31 set, which is sign-extended
into the upper word — so `r0 = 0xFFFFFFFF80000000`. -/
theorem add32_imm_sign_extended :
    run [0xb7, 0x00, 0, 0, 0, 0, 0, 0,
         0x04, 0x00, 0, 0, 0x00, 0x00, 0x00, 0x80,
         0x95, 0, 0, 0, 0, 0, 0, 0] = some 0xFFFFFFFF80000000 := by decide +kernel

end SolanalibTest.SBPF.Interpreter
