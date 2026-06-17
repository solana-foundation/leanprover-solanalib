/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.Interpreter
import Std.Tactic.BVDecide

/-!
# SBPF.Verifier — static checks and the step-safety theorem

The instruction-level part of the Solana verifier, ported from `verifier.thy`,
and the safety property it guarantees (`VerifierSafety.thy`, Lemma 6.4): an
instruction the verifier accepts never drives `step` into the `err` state (the
"malformed instruction" outcome the verifier exists to exclude).

`verifyInstr` models the Err-relevant content of `verify_one`: the version
gating (e.g. `addStk`/`pqr` are `v2`-only, `neg`/`le` are `v1`-only) and the
non-zero-divisor checks. The byte-level checks of `verify_one`
(`check_load_dw`, `check_jmp_offset`, `check_registers`) concern other safety
properties (in-bounds jumps, register ranges) that do not affect Err-freedom and
are omitted here.

## Main definitions
* `Solanalib.SBPF.verifyInstr` — the instruction-level verifier.

## Main statements
* `Solanalib.SBPF.step_ne_err` — verified instruction ⇒ `step ≠ err`.
-/

namespace Solanalib.SBPF

/-! ## The verifier -/

/-- A division/remainder immediate operand must be non-zero. -/
def checkImmNonzero (sop : SndOp) : Bool :=
  match sop with
  | .imm i => i != 0
  | .reg _ => true

/-- Version/divisor checks for an ALU op (`mul`/`div`/`mod` are `v1`-only;
`div`/`mod` immediates must be non-zero). -/
def verifyAlu (bop : Binop) (sop : SndOp) (isV1 : Bool) : Bool :=
  match bop with
  | .mul => isV1
  | .div => isV1 && checkImmNonzero sop
  | .mod => isV1 && checkImmNonzero sop
  | _ => true

/-- Divisor checks for a PQR op (`div`/`rem` immediates must be non-zero). -/
def verifyPqr (pop : Pqrop) (sop : SndOp) : Bool :=
  match pop with
  | .lmul => true
  | .udiv => checkImmNonzero sop
  | .urem => checkImmNonzero sop
  | .sdiv => checkImmNonzero sop
  | .srem => checkImmNonzero sop

/-- The instruction-level verifier (`verify_one`, Err-relevant content). -/
def verifyInstr (ins : BpfInstruction) (sv : SBPFV) : Bool :=
  let isV1 := match sv with | .v1 => true | .v2 => false
  match ins with
  | .ldImm _ _ _ => isV1
  | .ldx _ _ _ _ => true
  | .st _ _ _ _ => true
  | .addStk _ => !isV1
  | .alu bop _ sop => verifyAlu bop sop isV1
  | .neg32Reg _ => isV1
  | .le _ i => isV1 && (i == 16 || i == 32 || i == 64)
  | .be _ i => i == 16 || i == 32 || i == 64
  | .alu64 bop _ sop => verifyAlu bop sop isV1
  | .neg64Reg _ => isV1
  | .hor64Imm _ _ => !isV1
  | .pqr pop _ sop => !isV1 && verifyPqr pop sop
  | .pqr64 pop _ sop => !isV1 && verifyPqr pop sop
  | .pqr2 _ _ _ => !isV1
  | .ja _ => true
  | .jump _ _ _ _ => true
  | .callReg _ _ => true
  | .callImm _ _ => true
  | .exit => true

/-! ## Supporting lemmas -/

@[simp] theorem sndOp32_imm (i : U32) (rs : RegMap) : sndOp32 (.imm i) rs = i := rfl

@[simp] theorem sndOp64_imm (i : U32) (rs : RegMap) :
    sndOp64 (.imm i) rs = i.signExtend 64 := rfl

/-- Sign-extending to 64 bits is zero exactly when the source is. -/
@[simp] theorem signExtend64_eq_zero (i : U32) : i.signExtend 64 = 0 ↔ i = 0 := by
  bv_decide

/-- A non-`nok` ALU result keeps `step` out of the `err` state. -/
theorem stepRegOutcome_ne_err {o : RegOutcome} {pc : U64} {m : Mem} {ss : StackState}
    {sv : SBPFV} {fm : FuncMap} {cur remain : U64} (h : o ≠ .nok) :
    stepRegOutcome o pc m ss sv fm cur remain ≠ .err := by
  cases o with
  | nok => exact absurd rfl h
  | okn => simp [stepRegOutcome]
  | oks rs' => simp [stepRegOutcome]

/-- The 32-bit ALU never faults to `err` on a verified instruction. -/
theorem evalAlu32_ne_nok {bop : Binop} {dst : BpfIReg} {sop : SndOp} {rs : RegMap}
    {isV1 : Bool} (h : verifyAlu bop sop isV1 = true) :
    evalAlu32 bop dst sop rs isV1 ≠ .nok := by
  cases bop <;> cases sop <;>
    simp_all [evalAlu32, verifyAlu, checkImmNonzero, bne_iff_ne] <;>
    (repeat' split) <;> simp_all

/-- The 64-bit ALU never faults to `err` on a verified instruction. -/
theorem evalAlu64_ne_nok {bop : Binop} {dst : BpfIReg} {sop : SndOp} {rs : RegMap}
    {isV1 : Bool} (h : verifyAlu bop sop isV1 = true) :
    evalAlu64 bop dst sop rs isV1 ≠ .nok := by
  cases bop <;> cases sop <;>
    simp_all [evalAlu64, verifyAlu, checkImmNonzero, bne_iff_ne] <;>
    (repeat' split) <;> (first | bv_decide | simp_all)

/-- The 32-bit PQR never faults to `err` on a verified instruction. -/
theorem evalPqr32_ne_nok {pop : Pqrop} {dst : BpfIReg} {sop : SndOp} {rs : RegMap}
    {isV1 : Bool} (h : verifyPqr pop sop = true) :
    evalPqr32 pop dst sop rs isV1 ≠ .nok := by
  cases pop <;> cases sop <;>
    simp_all [evalPqr32, verifyPqr, checkImmNonzero, pqrDivResult, bne_iff_ne] <;>
    (repeat' split) <;> simp_all

/-- The 64-bit PQR never faults to `err` on a verified instruction. -/
theorem evalPqr64_ne_nok {pop : Pqrop} {dst : BpfIReg} {sop : SndOp} {rs : RegMap}
    {isV1 : Bool} (h : verifyPqr pop sop = true) :
    evalPqr64 pop dst sop rs isV1 ≠ .nok := by
  cases pop <;> cases sop <;>
    simp_all [evalPqr64, verifyPqr, checkImmNonzero, pqrDivResult, bne_iff_ne] <;>
    (repeat' split) <;> (first | bv_decide | simp_all)

/-! ## Safety -/

/-- **Verifier step-safety** (Lemma 6.4): if `verifyInstr` accepts an
instruction, then `step` on it never returns the `err` state. -/
theorem step_ne_err {ins : BpfInstruction} {sv : SBPFV} (h : verifyInstr ins sv = true)
    (pc : U64) (rs : RegMap) (m : Mem) (ss : StackState) (fm : FuncMap)
    (gaps : Bool) (vmAddr cur remain : U64) :
    step pc ins rs m ss sv fm gaps vmAddr cur remain ≠ .err := by
  cases ins with
  | ldImm dst i1 i2 => simp [step]
  | ldx chk d s off => simp only [step]; cases evalLoad chk d s off rs m <;> simp
  | st chk d sop off => simp only [step]; cases evalStore chk d sop off rs m <;> simp
  | addStk i =>
      simp only [step, verifyInstr] at *
      cases sv <;> simp_all [evalAdd64ImmR10]
  | alu bop d sop =>
      simp only [step]
      exact stepRegOutcome_ne_err (evalAlu32_ne_nok h)
  | neg32Reg d =>
      simp only [step]
      refine stepRegOutcome_ne_err ?_
      unfold evalNeg32; split <;> simp
  | le d imm =>
      simp only [step]
      refine stepRegOutcome_ne_err ?_
      unfold evalLe
      (repeat' split) <;>
        simp [u16OfU8List, u8ListOfU16, u32OfU8List, u8ListOfU32, u64OfU8List, u8ListOfU64]
  | be d imm =>
      simp only [step]
      refine stepRegOutcome_ne_err ?_
      unfold evalBe
      (repeat' split) <;>
        simp [u16OfU8List, u8ListOfU16, u32OfU8List, u8ListOfU32, u64OfU8List, u8ListOfU64]
  | alu64 bop d sop =>
      simp only [step]
      exact stepRegOutcome_ne_err (evalAlu64_ne_nok h)
  | neg64Reg d =>
      simp only [step]
      refine stepRegOutcome_ne_err ?_
      unfold evalNeg64; split <;> simp
  | hor64Imm d imm =>
      simp only [step]
      refine stepRegOutcome_ne_err ?_
      unfold evalHor64; split <;> simp
  | pqr pop d sop =>
      simp only [step]
      refine stepRegOutcome_ne_err (evalPqr32_ne_nok ?_)
      simp only [verifyInstr, Bool.and_eq_true] at h; exact h.2
  | pqr64 pop d sop =>
      simp only [step]
      refine stepRegOutcome_ne_err (evalPqr64_ne_nok ?_)
      simp only [verifyInstr, Bool.and_eq_true] at h; exact h.2
  | pqr2 pop d sop =>
      simp only [step]
      refine stepRegOutcome_ne_err ?_
      unfold evalPqr64_2; (repeat' split) <;> simp
  | ja off => simp [step]
  | jump cond r sop off => simp only [step]; split <;> simp
  | callReg s i =>
      simp only [step]
      rcases evalCallReg s i rs ss _ pc gaps vmAddr with _ | ⟨pc', rs', ss'⟩ <;> simp
  | callImm s i =>
      simp only [step]
      rcases evalCallImm pc s i rs ss _ fm gaps with _ | ⟨pc', rs', ss'⟩ <;> simp
  | exit =>
      simp only [step]
      split <;> (try split) <;> simp

end Solanalib.SBPF
