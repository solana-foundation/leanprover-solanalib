/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.Decoder
import Solanalib.SBPF.State

/-!
# SBPF.Interpreter — the small-step sBPF semantics

The operational semantics of the Solana eBPF interpreter, ported from
`Interpreter.thy`: the per-class evaluators (`evalAlu32`/`64`, `evalPqr*`,
`evalJmp`, `evalLoad`/`Store`, the call/exit frame machinery), the single-step
function `step`, and the fuel-bounded driver `bpfInterp`.

Registers are raw `U64`; signed behaviour is expressed with `BitVec`'s signed
operations (`sdiv`/`srem`/`slt`/`sshiftRight`) and sign-extension, faithful to
the source theory. Note the sBPF-specific quirk (Challenge 1 of the paper): the
32-bit `ADD`/`SUB`/`MUL` results are *sign-extended* into the 64-bit register,
whereas the logical/shift results are zero-extended.

## Main definitions
* `Solanalib.SBPF.step` — execute one instruction, yielding a `BpfState`.
* `Solanalib.SBPF.bpfInterp` — run the program under a fuel bound.
-/

namespace Solanalib.SBPF

/-! ## Operand evaluation -/

/-- The second operand as a 32-bit value: immediate verbatim, or the low 32
bits of the source register (`eval_snd_op_{i,u}32` — same bits either way). -/
def sndOp32 (sop : SndOp) (rs : RegMap) : U32 :=
  match sop with
  | .imm i => i
  | .reg r => (rs r).setWidth 32

/-- The second operand as a 64-bit value: a sign-extended immediate, or the
source register verbatim (`eval_snd_op_{i,u}64` — same bits either way). -/
def sndOp64 (sop : SndOp) (rs : RegMap) : U64 :=
  match sop with
  | .imm i => i.signExtend 64
  | .reg r => rs r

/-! ## ALU -/

/-- 32-bit ALU (`eval_alu32`). Add/sub/mul sign-extend the 32-bit result;
the rest zero-extend. `mul`/`div`/`mod` are `v1`-only. -/
def evalAlu32 (bop : Binop) (dst : BpfIReg) (sop : SndOp) (rs : RegMap)
    (isV1 : Bool) : RegOutcome :=
  let dv : U32 := (rs dst).setWidth 32
  let sv : U32 := sndOp32 sop rs
  match bop with
  | .add => .oks (setReg rs dst ((dv + sv).signExtend 64))
  | .sub =>
      match sop with
      | .reg _ => .oks (setReg rs dst ((dv - sv).signExtend 64))
      | .imm _ =>
          if isV1 then .oks (setReg rs dst ((dv - sv).signExtend 64))
          else .oks (setReg rs dst ((sv - dv).signExtend 64))
  | .mul => if isV1 then .oks (setReg rs dst ((dv * sv).signExtend 64)) else .okn
  | .div =>
      if isV1 then
        if sv = 0 then (match sop with | .imm _ => .nok | .reg _ => .okn)
        else .oks (setReg rs dst ((dv / sv).setWidth 64))
      else .okn
  | .or => .oks (setReg rs dst ((dv ||| sv).setWidth 64))
  | .and => .oks (setReg rs dst ((dv &&& sv).setWidth 64))
  | .mod =>
      if isV1 then
        if sv = 0 then (match sop with | .imm _ => .nok | .reg _ => .okn)
        else .oks (setReg rs dst ((dv % sv).setWidth 64))
      else .okn
  | .xor => .oks (setReg rs dst ((dv ^^^ sv).setWidth 64))
  | .mov => .oks (setReg rs dst (sv.setWidth 64))
  | .lsh => .oks (setReg rs dst ((dv <<< (sv &&& 31).toNat).setWidth 64))
  | .rsh => .oks (setReg rs dst ((dv >>> (sv &&& 31).toNat).setWidth 64))
  | .arsh => .oks (setReg rs dst ((dv.sshiftRight (sv &&& 31).toNat).setWidth 64))

/-- 64-bit ALU (`eval_alu64`). `mul`/`div`/`mod` are `v1`-only; the shift amount
is masked to 6 bits. -/
def evalAlu64 (bop : Binop) (dst : BpfIReg) (sop : SndOp) (rs : RegMap)
    (isV1 : Bool) : RegOutcome :=
  let dv : U64 := rs dst
  let sv : U64 := sndOp64 sop rs
  let shAmt : Nat := (sndOp32 sop rs &&& 63).toNat
  match bop with
  | .add => .oks (setReg rs dst (dv + sv))
  | .sub =>
      match sop with
      | .reg _ => .oks (setReg rs dst (dv - sv))
      | .imm _ =>
          if isV1 then .oks (setReg rs dst (dv - sv))
          else .oks (setReg rs dst (sv - dv))
  | .mul => if isV1 then .oks (setReg rs dst (dv * sv)) else .okn
  | .div =>
      if isV1 then
        if sv = 0 then (match sop with | .imm _ => .nok | .reg _ => .okn)
        else .oks (setReg rs dst (dv / sv))
      else .okn
  | .or => .oks (setReg rs dst (dv ||| sv))
  | .and => .oks (setReg rs dst (dv &&& sv))
  | .mod =>
      if isV1 then
        if sv = 0 then (match sop with | .imm _ => .nok | .reg _ => .okn)
        else .oks (setReg rs dst (dv % sv))
      else .okn
  | .xor => .oks (setReg rs dst (dv ^^^ sv))
  | .mov => .oks (setReg rs dst sv)
  | .lsh => .oks (setReg rs dst (dv <<< shAmt))
  | .rsh => .oks (setReg rs dst (dv >>> shAmt))
  | .arsh => .oks (setReg rs dst (dv.sshiftRight shAmt))

/-- Add a (sign-extended) immediate to the stack pointer (`eval_add64_imm_R10`).
`v2`-only. -/
def evalAdd64ImmR10 (i : U32) (ss : StackState) (isV1 : Bool) : Option StackState :=
  if isV1 then none
  else some { ss with stackPointer := ss.stackPointer + i.signExtend 64 }

/-- 32-bit negate (`eval_neg32`). `v1`-only. -/
def evalNeg32 (dst : BpfIReg) (rs : RegMap) (isV1 : Bool) : RegOutcome :=
  if isV1 then .oks (setReg rs dst ((- (rs dst).setWidth 32).setWidth 64)) else .okn

/-- 64-bit negate (`eval_neg64`). `v1`-only. -/
def evalNeg64 (dst : BpfIReg) (rs : RegMap) (isV1 : Bool) : RegOutcome :=
  if isV1 then .oks (setReg rs dst (- rs dst)) else .okn

/-- Little-endian byte swap / truncation (`eval_le`). `v1`-only. -/
def evalLe (dst : BpfIReg) (imm : U32) (rs : RegMap) (isV1 : Bool) : RegOutcome :=
  if isV1 then
    let dv := rs dst
    if imm = 16 then
      match u16OfU8List (u8ListOfU16 (dv.setWidth 16)) with
      | some v => .oks (setReg rs dst (v.setWidth 64))
      | none => .okn
    else if imm = 32 then
      match u32OfU8List (u8ListOfU32 (dv.setWidth 32)) with
      | some v => .oks (setReg rs dst (v.setWidth 64))
      | none => .okn
    else if imm = 64 then
      match u64OfU8List (u8ListOfU64 dv) with
      | some v => .oks (setReg rs dst v)
      | none => .okn
    else .okn
  else .okn

/-- Big-endian byte swap (`eval_be`): reverse the bytes before reassembly.
`v1`-only. -/
def evalBe (dst : BpfIReg) (imm : U32) (rs : RegMap) (isV1 : Bool) : RegOutcome :=
  if isV1 then
    let dv := rs dst
    if imm = 16 then
      match u16OfU8List (u8ListOfU16 (dv.setWidth 16)).reverse with
      | some v => .oks (setReg rs dst (v.setWidth 64))
      | none => .okn
    else if imm = 32 then
      match u32OfU8List (u8ListOfU32 (dv.setWidth 32)).reverse with
      | some v => .oks (setReg rs dst (v.setWidth 64))
      | none => .okn
    else if imm = 64 then
      match u64OfU8List (u8ListOfU64 dv).reverse with
      | some v => .oks (setReg rs dst v)
      | none => .okn
    else .okn
  else .okn

/-- OR a high-order 32-bit immediate into the top half of `dst` (`eval_hor64`).
`v2`-only. -/
def evalHor64 (dst : BpfIReg) (imm : U32) (rs : RegMap) (isV1 : Bool) : RegOutcome :=
  if isV1 then .okn
  else .oks (setReg rs dst ((rs dst) ||| (imm.setWidth 64 <<< 32)))

/-! ## PQR (product / quotient / remainder) -/

/-- A division/remainder guard: zero divisor faults as `nok` for an immediate
operand (verifier should reject) and `okn` for a register operand. -/
def pqrDivResult (sop : SndOp) (rs' : RegMap) (zero : Bool) : RegOutcome :=
  if zero then (match sop with | .imm _ => .nok | .reg _ => .okn) else .oks rs'

/-- 32-bit PQR (`eval_pqr32`). `v2`-only. -/
def evalPqr32 (pop : Pqrop) (dst : BpfIReg) (sop : SndOp) (rs : RegMap)
    (isV1 : Bool) : RegOutcome :=
  if isV1 then .okn
  else
    let dv : U32 := (rs dst).setWidth 32
    let sv : U32 := sndOp32 sop rs
    match pop with
    | .lmul => .oks (setReg rs dst ((dv * sv).setWidth 64))
    | .sdiv => pqrDivResult sop (setReg rs dst ((dv.sdiv sv).setWidth 64)) (sv = 0)
    | .srem => pqrDivResult sop (setReg rs dst ((dv.srem sv).setWidth 64)) (sv = 0)
    | .udiv => pqrDivResult sop (setReg rs dst ((dv / sv).setWidth 64)) (sv = 0)
    | .urem => pqrDivResult sop (setReg rs dst ((dv % sv).setWidth 64)) (sv = 0)

/-- 64-bit PQR (`eval_pqr64`). `v2`-only. -/
def evalPqr64 (pop : Pqrop) (dst : BpfIReg) (sop : SndOp) (rs : RegMap)
    (isV1 : Bool) : RegOutcome :=
  if isV1 then .okn
  else
    let dv : U64 := rs dst
    let sv : U64 := sndOp64 sop rs
    match pop with
    | .lmul => .oks (setReg rs dst (dv * sv))
    | .udiv => pqrDivResult sop (setReg rs dst (dv / sv)) (sv = 0)
    | .urem => pqrDivResult sop (setReg rs dst (dv % sv)) (sv = 0)
    | .sdiv => pqrDivResult sop (setReg rs dst (dv.sdiv sv)) (sv = 0)
    | .srem => pqrDivResult sop (setReg rs dst (dv.srem sv)) (sv = 0)

/-- High-half multiply (`eval_pqr64_2`). `v2`-only.

The standard high-multiply semantics: widen both operands to 128 bits (zero-
extend for `uhmul`, sign-extend for `shmul`), multiply, and take the high 64
bits. (`Interpreter.thy`'s `eval_pqr64_2` appears to mis-source its signed
operand from `dst`; we implement the intended semantics and let differential
testing against the reference VM adjudicate.) -/
def evalPqr64_2 (pop : Pqrop2) (dst : BpfIReg) (sop : SndOp) (rs : RegMap)
    (isV1 : Bool) : RegOutcome :=
  if isV1 then .okn
  else
    match pop with
    | .uhmul =>
        let p := (rs dst).setWidth 128 * (sndOp64 sop rs).setWidth 128
        .oks (setReg rs dst ((p >>> 64).setWidth 64))
    | .shmul =>
        let p := (rs dst).signExtend 128 * (sndOp64 sop rs).signExtend 128
        .oks (setReg rs dst ((p >>> 64).setWidth 64))

/-! ## Memory -/

/-- Store the second operand at `dst + off` (`eval_store`). -/
def evalStore (chk : MemoryChunk) (dst : BpfIReg) (sop : SndOp) (off : U16)
    (rs : RegMap) (m : Mem) : Option Mem :=
  storev chk m (rs dst + off.signExtend 64) (memoryChunkValueOfU64 chk (sndOp64 sop rs))

/-- Load from `src + off` into `dst`, zero-extending narrow loads (`eval_load`). -/
def evalLoad (chk : MemoryChunk) (dst src : BpfIReg) (off : U16)
    (rs : RegMap) (m : Mem) : Option RegMap :=
  match loadv chk m (rs src + off.signExtend 64) with
  | none => none
  | some .vundef => none
  | some (.vlong v) => some (setReg rs dst v)
  | some (.vint v) => some (setReg rs dst (v.setWidth 64))
  | some (.vshort v) => some (setReg rs dst (v.setWidth 64))
  | some (.vbyte v) => some (setReg rs dst (v.setWidth 64))

/-- Load a 64-bit immediate assembled from two halves (`eval_load_imm`). -/
def evalLoadImm (dst : BpfIReg) (imm1 imm2 : U32) (rs : RegMap) : RegMap :=
  setReg rs dst ((imm1.setWidth 64 &&& 0xffffffff) ||| (imm2.setWidth 64 <<< 32))

/-! ## Jump -/

/-- Evaluate a branch condition (`eval_jmp`). -/
def evalJmp (cond : Condition) (dst : BpfIReg) (sop : SndOp) (rs : RegMap) : Bool :=
  let udv : U64 := rs dst
  let usv : U64 := sndOp64 sop rs
  match cond with
  | .eq => udv == usv
  | .gt => usv.ult udv
  | .ge => usv.ule udv
  | .lt => udv.ult usv
  | .le => udv.ule usv
  | .sEt => (udv &&& usv) != 0
  | .ne => udv != usv
  | .sGt => usv.slt udv
  | .sGe => usv.sle udv
  | .sLt => udv.slt usv
  | .sLe => udv.sle usv

/-! ## Call / exit -/

/-- A default (empty) call frame, used as a total-access fallback. -/
private def emptyFrame : CallFrame :=
  { callerSavedRegisters := [], framePointer := 0, targetPc := 0 }

/-- Push a new call frame, saving `BR6`–`BR9` and the frame pointer
(`push_frame`). Returns `none` (with `rs` unchanged) when the call stack is
full. -/
def pushFrame (rs : RegMap) (ss : StackState) (isV1 : Bool) (pc : U64)
    (gaps : Bool) : Option StackState × RegMap :=
  let frame : CallFrame :=
    { callerSavedRegisters := [rs .br6, rs .br7, rs .br8, rs .br9],
      framePointer := rs .br10, targetPc := pc + 1 }
  let depth' := ss.callDepth + 1
  if depth' = maxCallDepth then (none, rs)
  else
    let sp' :=
      if isV1 then
        (if gaps then ss.stackPointer + stackFrameSize * 2 else ss.stackPointer + stackFrameSize)
      else ss.stackPointer
    let frames' := ss.callFrames.set ss.callDepth.toNat frame
    (some { callDepth := depth', stackPointer := sp', callFrames := frames' },
     setReg rs .br10 sp')

/-- Call the function whose address is in a register (`eval_callReg`). -/
def evalCallReg (src : BpfIReg) (imm : U32) (rs : RegMap) (ss : StackState)
    (isV1 : Bool) (pc : U64) (gaps : Bool) (programVmAddr : U64) :
    Option (U64 × RegMap × StackState) :=
  match BpfIReg.ofU4 (imm.setWidth 4) with
  | none => none
  | some iv =>
    let pc1 := if isV1 then rs iv else rs src
    match pushFrame rs ss isV1 pc gaps with
    | (none, _) => none
    | (some ss', rs') =>
        if pc1.ult programVmAddr then none
        else some ((pc1 - programVmAddr) / BitVec.ofNat 64 insnSize, rs', ss')

/-- Call the function identified by an immediate, via the registry when the
source register is `BR0` (`eval_callImm`). -/
def evalCallImm (pc : U64) (src : BpfIReg) (imm : U32) (rs : RegMap)
    (ss : StackState) (isV1 : Bool) (fm : FuncMap) (gaps : Bool) :
    Option (U64 × RegMap × StackState) :=
  match (if src = .br0 then getFunctionRegistry imm fm else some (imm.setWidth 64)) with
  | none => none
  | some npc =>
    match pushFrame rs ss isV1 pc gaps with
    | (none, _) => none
    | (some ss', rs') => some (npc, rs', ss')

/-- The frame to return into (`pop_frame`). -/
def popFrame (ss : StackState) : CallFrame :=
  ss.callFrames.getD (ss.callDepth - 1).toNat emptyFrame

/-- Return from the current frame, restoring saved registers (`eval_exit`). -/
def evalExit (rs : RegMap) (ss : StackState) (isV1 : Bool) :
    U64 × RegMap × StackState :=
  let frame := popFrame ss
  let rs' :=
    setReg (setReg (setReg (setReg (setReg rs
      .br10 frame.framePointer)
      .br9 (frame.callerSavedRegisters.getD 3 0))
      .br8 (frame.callerSavedRegisters.getD 2 0))
      .br7 (frame.callerSavedRegisters.getD 1 0))
      .br6 (frame.callerSavedRegisters.getD 0 0)
  let sp' := if isV1 then ss.stackPointer - 2 * stackFrameSize else ss.stackPointer
  (frame.targetPc, rs',
   { callDepth := ss.callDepth - 1, stackPointer := sp', callFrames := ss.callFrames.dropLast })

/-! ## Step -/

/-- Lift an ALU-style `RegOutcome` into the post-state of a `pc + 1` step. -/
def stepRegOutcome (o : RegOutcome) (pc : U64) (m : Mem) (ss : StackState)
    (sv : SBPFV) (fm : FuncMap) (curCu remainCu : U64) : BpfState :=
  match o with
  | .nok => .err
  | .okn => .eflag
  | .oks rs' => .ok (pc + 1) rs' m ss sv fm (curCu + 1) remainCu

/-- Execute a single instruction (`step`). -/
def step (pc : U64) (ins : BpfInstruction) (rs : RegMap) (m : Mem) (ss : StackState)
    (sv : SBPFV) (fm : FuncMap) (gaps : Bool) (programVmAddr : U64)
    (curCu remainCu : U64) : BpfState :=
  let isV1 := match sv with | .v1 => true | .v2 => false
  let next (rs' : RegMap) : BpfState := .ok (pc + 1) rs' m ss sv fm (curCu + 1) remainCu
  match ins with
  | .alu bop d sop => stepRegOutcome (evalAlu32 bop d sop rs isV1) pc m ss sv fm curCu remainCu
  | .alu64 bop d sop => stepRegOutcome (evalAlu64 bop d sop rs isV1) pc m ss sv fm curCu remainCu
  | .le dst imm => stepRegOutcome (evalLe dst imm rs isV1) pc m ss sv fm curCu remainCu
  | .be dst imm => stepRegOutcome (evalBe dst imm rs isV1) pc m ss sv fm curCu remainCu
  | .neg32Reg dst => stepRegOutcome (evalNeg32 dst rs isV1) pc m ss sv fm curCu remainCu
  | .neg64Reg dst => stepRegOutcome (evalNeg64 dst rs isV1) pc m ss sv fm curCu remainCu
  | .hor64Imm dst imm => stepRegOutcome (evalHor64 dst imm rs isV1) pc m ss sv fm curCu remainCu
  | .pqr pop dst sop => stepRegOutcome (evalPqr32 pop dst sop rs isV1) pc m ss sv fm curCu remainCu
  | .pqr64 pop dst sop =>
      stepRegOutcome (evalPqr64 pop dst sop rs isV1) pc m ss sv fm curCu remainCu
  | .pqr2 pop dst sop =>
      stepRegOutcome (evalPqr64_2 pop dst sop rs isV1) pc m ss sv fm curCu remainCu
  | .addStk i =>
      match evalAdd64ImmR10 i ss isV1 with
      | none => .err
      | some ss' => .ok (pc + 1) rs m ss' sv fm (curCu + 1) remainCu
  | .ldx chk dst src off =>
      match evalLoad chk dst src off rs m with
      | none => .eflag
      | some rs' => next rs'
  | .st chk dst sop off =>
      match evalStore chk dst sop off rs m with
      | none => .eflag
      | some m' => .ok (pc + 1) rs m' ss sv fm (curCu + 1) remainCu
  | .ldImm dst imm1 imm2 =>
      .ok (pc + 2) (evalLoadImm dst imm1 imm2 rs) m ss sv fm (curCu + 1) remainCu
  | .ja off => .ok (pc + off.signExtend 64 + 1) rs m ss sv fm (curCu + 1) remainCu
  | .jump cond r sop off =>
      if evalJmp cond r sop rs then
        .ok (pc + off.signExtend 64 + 1) rs m ss sv fm (curCu + 1) remainCu
      else .ok (pc + 1) rs m ss sv fm (curCu + 1) remainCu
  | .callImm src imm =>
      match evalCallImm pc src imm rs ss isV1 fm gaps with
      | none => .eflag
      | some (pc', rs', ss') => .ok pc' rs' m ss' sv fm (curCu + 1) remainCu
  | .callReg src imm =>
      match evalCallReg src imm rs ss isV1 pc gaps programVmAddr with
      | none => .eflag
      | some (pc', rs', ss') => .ok pc' rs' m ss' sv fm (curCu + 1) remainCu
  | .exit =>
      if ss.callDepth = 0 then
        if curCu.toNat > remainCu.toNat then .eflag else .success (rs .br0)
      else
        let (pc', rs', ss') := evalExit rs ss isV1
        .ok pc' rs' m ss' sv fm (curCu + 1) remainCu

/-- Run the program under a fuel bound (`bpf_interp`). Each step is gated on PC
being in range and fuel remaining; exhaustion or an out-of-range PC yields a
fault. -/
def bpfInterp : Nat → BpfBin → BpfState → Bool → U64 → BpfState
  | 0, _, _, _, _ => .eflag
  | n + 1, prog, st, gaps, vmAddr =>
    match st with
    | .eflag => .eflag
    | .err => .err
    | .success v => .success v
    | .ok pc rs m ss sv fm curCu remainCu =>
      if insnSize * pc.toNat < prog.length then
        if curCu.toNat ≥ remainCu.toNat then .eflag
        else
          match findInstr pc.toNat prog with
          | none => .eflag
          | some ins =>
            bpfInterp n prog
              (step pc ins rs m ss sv fm gaps vmAddr curCu remainCu) gaps vmAddr
      else .eflag

end Solanalib.SBPF
