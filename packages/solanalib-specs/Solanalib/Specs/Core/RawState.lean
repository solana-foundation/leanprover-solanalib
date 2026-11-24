/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.RawRuntime

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.RawState

open RawRuntime

/-- The three typed syscall destinations in this source binding. -/
inductive Sysvar where
  | clock | rent | epochSchedule
  deriving DecidableEq, Repr

/-- The exact existing runtime request identifier. -/
def Sysvar.typed : Sysvar → Solanalib.Runtime.TypedSysvar
  | .clock => .clock
  | .rent => .rent
  | .epochSchedule => .epochSchedule

/-- Native `repr(C)` destination size, including zeroed padding. -/
def Sysvar.width : Sysvar → Nat
  | .clock | .epochSchedule => 40
  | .rent => 24

/-- The bytes of the runtime for the typed getter; this is not its bincode account encoding. -/
def Sysvar.bytes (which : Sysvar) (sysvars : Solanalib.Runtime.Sysvars) : Solanalib.Runtime.Bytes :=
  match which with
  | .clock => sysvars.clock.encode
  | .rent => sysvars.rent.reprC
  | .epochSchedule => sysvars.epochSchedule.reprC

/-- Every field is encoded to its fixed native width, independently of numeric interpretation. -/
theorem Sysvar.bytes_length (which : Sysvar) (sysvars : Solanalib.Runtime.Sysvars) :
    (which.bytes sysvars).length = which.width := by
  cases which <;> simp [Sysvar.bytes, Sysvar.width, Solanalib.Runtime.Clock.encode,
    Solanalib.Runtime.i64le,
    Solanalib.Runtime.u64le, Solanalib.Runtime.RentSysvar.reprC,
      Solanalib.Runtime.EpochSchedule.reprC]

/-- Preserve the ABI of the runtime, destination restriction and alignment checks in their order. -/
def typedStep (which : Sysvar) : Step Nat := fun index before dst =>
  invoke index before (.getSysvarTyped which.typed dst)

/-- The admissible runtime address conditions. A separate binding to the Rust implementation must
exclude VM-unaligned pointers; VM and translated-host alignment are distinct obligations. -/
def typedAccepted (index : Index) (dst : Nat) : Prop :=
  (index.world.prof.release != .agave_3_1_12 && index.context.abi == .v0) = false ∧
    (index.world.prof.features.pointerChecks && decide (Solanalib.Runtime.MM_INPUT_START ≤ dst)) =
      false ∧
    (index.context.abi == .v1 && dst % 8 != 0) = false

/-- A typed getter request returns zero, exact pending output bytes and unchanged request-phase
state. -/
theorem typed_returned_iff (which : Sysvar) (index : Index) (before after :
  Solanalib.Runtime.InvState)
    (dst : Nat) (answer : Solanalib.Runtime.SysAns) :
    typedStep which index before dst = .ok (answer, after) ↔
      typedAccepted index dst ∧ answer = ⟨0, [which.bytes index.world.sysvars]⟩ ∧ after = before :=
        by
  cases which <;>
    simp only [typedStep, invoke, Solanalib.Runtime.SysReq.registered, Bool.cond_true,
      Solanalib.Runtime.sysStep,
      Sysvar.typed, Solanalib.Runtime.TypedSysvar.sizeAlign, Solanalib.Runtime.TypedSysvar.value,
        typedAccepted,
      Sysvar.bytes]
  all_goals
    by_cases first : (index.world.prof.release != .agave_3_1_12 && index.context.abi == .v0) = true
      <;>
      by_cases second : (index.world.prof.features.pointerChecks && decide
        (Solanalib.Runtime.MM_INPUT_START ≤ dst)) = true <;>
      by_cases third : (index.context.abi == .v1 && dst % 8 != 0) = true <;>
      simp [first, second, third, eq_comm]

/-- Stack height is the number of active instruction frames. It reads no source memory. -/
def stackStep : Step Unit := fun index before _ => invoke index before .getStackHeight

/-- The complete result of the stack-height request. -/
theorem stack_result (index : Index) (before : Solanalib.Runtime.InvState) :
    stackStep index before () = .ok (⟨before.ts.stack.length, []⟩, before) := rfl

/-- The setter carries ordered bytes, including empty data which clears the previous bytes. -/
def setReturnStep : Step Solanalib.Runtime.Bytes := fun index before bytes =>
  invoke index before (.setReturnData bytes)

/-- The setter tags the bytes with the current caller, and changes no other invocation field. -/
theorem setReturn_result (index : Index) (before : Solanalib.Runtime.InvState) (bytes :
  Solanalib.Runtime.Bytes) :
    setReturnStep index before bytes =
      if Solanalib.Runtime.MAX_RETURN_DATA < bytes.length then .error .ProgramFailedToComplete
      else .ok (.ok0, { before with ts := { before.ts with
        returnData := (before.ts.key index.context.frame.programIdx, bytes) } }) := rfl

/-- The register arguments of the return-data reader are retained for the output-overlap check. -/
structure ReturnArgs where
  capacity : Nat
  dataDst : Nat
  programDst : Nat
  deriving Repr

/-- Only the truncated prefix is copied. The returned register still contains the full length. -/
def ReturnArgs.copied (args : ReturnArgs) (before : Solanalib.Runtime.InvState) : Nat :=
  min args.capacity before.ts.returnData.2.length

/-- A zero copied length skips both output translations and the overlap check. -/
def getReturnStep : Step ReturnArgs := fun index before args =>
  invoke index before (.getReturnData args.capacity args.dataDst args.programDst)

/-- Exact pending data/program output protocol, before source stores, including the zero-copy path.
-/
theorem getReturn_result (index : Index) (before : Solanalib.Runtime.InvState) (args : ReturnArgs) :
    getReturnStep index before args =
      if 0 < args.copied before then
        if !Solanalib.Runtime.nonOverlapping args.dataDst (args.copied before) args.programDst 32
          then
          .error .ProgramFailedToComplete
        else .ok (⟨before.ts.returnData.2.length,
          [before.ts.returnData.2.take (args.copied before), before.ts.returnData.1.bytes]⟩, before)
      else .ok (⟨before.ts.returnData.2.length, []⟩, before) := rfl

/-- Zero capacity reports the stored length without touching either destination. -/
theorem getReturn_zero_capacity (index : Index) (before : Solanalib.Runtime.InvState) (dst pid :
  Nat) :
    getReturnStep index before ⟨0, dst, pid⟩ =
      .ok (⟨before.ts.returnData.2.length, []⟩, before) := by
  rw [getReturn_result]
  simp [ReturnArgs.copied]

/-- Every ordinary get result reports the full stored length and writes the exact truncated
prefix and program identity precisely when at least one byte is copied. -/
theorem getReturn_shape (index : Index) (before after : Solanalib.Runtime.InvState) (args :
  ReturnArgs)
    (answer : Solanalib.Runtime.SysAns) (result : getReturnStep index before args = .ok (answer,
      after)) :
    answer.r0 = before.ts.returnData.2.length ∧ after = before ∧
      answer.out = if 0 < args.copied before then
        [before.ts.returnData.2.take (args.copied before), before.ts.returnData.1.bytes] else [] :=
          by
  rw [getReturn_result] at result
  split at result
  · next nonempty =>
    split at result
    · cases result
    · cases result
      exact ⟨rfl, rfl, (ite_eq_left nonempty).symm⟩
  · next empty =>
    cases result
    exact ⟨rfl, rfl, (ite_eq_right empty).symm⟩

/-- A successful set followed by a zero-capacity get observes the complete length of that set. -/
theorem set_get_length (index : Index) (before : Solanalib.Runtime.InvState) (bytes :
  Solanalib.Runtime.Bytes)
    (within : bytes.length ≤ Solanalib.Runtime.MAX_RETURN_DATA) (dst pid : Nat) :
    ∃ after, setReturnStep index before bytes = .ok (.ok0, after) ∧
      getReturnStep index after ⟨0, dst, pid⟩ = .ok (⟨bytes.length, []⟩, after) := by
  refine ⟨{ before with ts := { before.ts with
    returnData := (before.ts.key index.context.frame.programIdx, bytes) } }, ?_, ?_⟩
  · rw [setReturn_result, ite_eq_right (Nat.not_lt_of_ge within)]
  · exact getReturn_zero_capacity index _ dst pid

end Solanalib.Specs.Core.RawState
