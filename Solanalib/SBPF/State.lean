/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.Memory
import Solanalib.SBPF.Syntax

/-!
# SBPF.State — interpreter state

The machine state of the sBPF interpreter, ported from `vm_state.thy`,
`vm.thy`, `ebpf.thy`, and the state section of `Interpreter.thy`. This module
defines the register file, the call-frame stack, the function registry, the
small-step result type, the VM constants, and the initial state.

## Main definitions
* `Solanalib.SBPF.RegMap` — the eleven 64-bit registers as a function.
* `Solanalib.SBPF.StackState` — the call-frame stack.
* `Solanalib.SBPF.BpfState` — the small-step result (`ok` / `success` / `eflag` / `err`).
* `Solanalib.SBPF.RegOutcome` — an ALU step result (`oks` / `okn` / `nok`).
-/

namespace Solanalib.SBPF

/-! ## VM constants -/

/-- Number of scratch (caller-saved) registers, `BR6`–`BR9`. -/
def scratchRegs : Nat := 4

/-- Base virtual address of the VM stack region. -/
def mmStackStart : U64 := 0x200000000

/-- Base virtual address of the program input region. -/
def mmInputStart : U64 := 0x400000000

/-- Maximum nested call depth. -/
def maxCallDepth : U64 := 64

/-- Size of a single stack frame, in bytes. -/
def stackFrameSize : U64 := 4096

/-! ## Registers -/

/-- The register file: each of the eleven registers holds a 64-bit word. -/
abbrev RegMap := BpfIReg → U64

/-- Read a register (`eval_reg`). -/
def evalReg (dst : BpfIReg) (rs : RegMap) : U64 := rs dst

/-- Functional register update: `rs` with `r` set to `v`. -/
def setReg (rs : RegMap) (r : BpfIReg) (v : U64) : RegMap :=
  fun r' => if r' = r then v else rs r'

/-- The all-zero register file (`init_reg_map`). -/
def initRegMap : RegMap := fun _ => 0

/-! ## Call frames and the stack -/

/-- A saved call frame: the caller's scratch registers, frame pointer, and the
program counter to return to (`vm_state.thy`'s `CallFrame`). -/
@[ext]
structure CallFrame where
  /-- The caller-saved registers `BR6`–`BR9`, in order. -/
  callerSavedRegisters : List U64
  /-- The caller's frame pointer (`BR10`). -/
  framePointer : U64
  /-- The program counter to resume at on return. -/
  targetPc : U64
  deriving Repr, DecidableEq

/-- The call-frame stack: current depth, stack pointer, and saved frames. -/
@[ext]
structure StackState where
  /-- The current nesting depth of function calls. -/
  callDepth : U64
  /-- The current stack pointer. -/
  stackPointer : U64
  /-- The saved call frames, innermost last. -/
  callFrames : List CallFrame
  deriving Repr, DecidableEq

/-- The initial stack: depth 0, stack pointer at the top of the region, and
`maxCallDepth` default frames preallocated (`init_stack_state`). -/
def initStackState : StackState where
  callDepth := 0
  stackPointer := mmStackStart + stackFrameSize * maxCallDepth
  callFrames :=
    List.replicate maxCallDepth.toNat
      { callerSavedRegisters := [], framePointer := 0, targetPc := 0 }

/-! ## Function registry -/

/-- The function registry: a partial map from a 32-bit key to a target address
(`ebpf.thy`'s `func_map`). -/
abbrev FuncMap := U32 → Option U64

/-- The empty function registry (`init_func_map`). -/
def initFuncMap : FuncMap := fun _ => none

/-- Look up a function address by key (`get_function_registry`). -/
def getFunctionRegistry (key : U32) (fm : FuncMap) : Option U64 := fm key

/-! ## Step results -/

/-- The small-step result (`bpf_state`).

* `ok pc rs m ss sv fm curCu remainCu` — a normal post-state.
* `success v` — the program returned `v`.
* `eflag` — a runtime fault (out-of-bounds, fuel exhaustion, …).
* `err` — a malformed instruction the verifier should have rejected. -/
inductive BpfState
  | ok (pc : U64) (rs : RegMap) (m : Mem) (ss : StackState)
      (sv : SBPFV) (fm : FuncMap) (curCu remainCu : U64)
  | success (v : U64)
  | eflag
  | err

/-- The result of an ALU-style evaluation (`'a option2`, specialised to the
register file): `oks` carries the updated registers, `okn` signals a runtime
fault (`EFlag`), `nok` a malformed instruction (`Err`). -/
inductive RegOutcome
  | nok
  | okn
  | oks (rs : RegMap)

/-- The initial machine state: PC 0, `BR10` pointing at the top of the stack,
memory `m`, version `v`, empty registry, and `n` units of fuel
(`init_bpf_state`). -/
def initBpfState (rs : RegMap) (m : Mem) (n : U64) (v : SBPFV) : BpfState :=
  .ok 0
    (setReg rs .br10 (mmStackStart + stackFrameSize * maxCallDepth))
    m initStackState v initFuncMap 0 n

end Solanalib.SBPF
