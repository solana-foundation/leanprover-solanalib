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

namespace Solanalib.Specs.Core.RawMemory

open RawRuntime

/-- The bytes read from `src`; the length of the syscall is their length. -/
structure CopyArgs where
  dst : Nat
  src : Nat
  bytes : Solanalib.Runtime.Bytes
  deriving Repr

/-- The VM-range overlap check happens before either pointer is translated. -/
def CopyArgs.overlap (args : CopyArgs) : Bool :=
  0 < args.bytes.length && !Solanalib.Runtime.nonOverlapping args.dst args.bytes.length args.src
    args.bytes.length

/-- The request checks raw VM overlap and supplies captured source bytes as pending output.
The source binding must compose these bytes with the output store, including any change to the
actual input buffer. -/
def copyStep : Step CopyArgs := fun index before args =>
  match invoke index before (.memcpy args.dst args.src args.bytes.length) with
  | .error error => .error error
  | .ok (_, after) => .ok (⟨0, [args.bytes]⟩, after)

/-- A `u8` fill value and the exact destination length. -/
structure SetArgs where
  byte : UInt8
  count : Nat
  deriving Repr

/-- `sol_memset_` is the byte-fill operation of the runtime. There is no separate `SysReq`
constructor;
its request result supplies the repeated output bytes and preserves the request-phase state.
The source binding must compose the output store with the actual invocation state. -/
def setStep : Step SetArgs := fun _ before args =>
  .ok (⟨0, [List.replicate args.count args.byte]⟩, before)

/-- The complete successful copy request result, with unchanged request-phase fields. -/
theorem copy_returned_iff (index : Index) (before after : Solanalib.Runtime.InvState) (args :
  CopyArgs)
    (answer : Solanalib.Runtime.SysAns) :
    copyStep index before args = .ok (answer, after) ↔
      args.overlap = false ∧ answer = ⟨0, [args.bytes]⟩ ∧ after = before := by
  unfold copyStep invoke
  simp only [Solanalib.Runtime.SysReq.registered, Bool.cond_true, Solanalib.Runtime.sysStep]
  change (match (if args.overlap then .error .ProgramFailedToComplete else
      .ok (Solanalib.Runtime.SysAns.ok0, before) : Result) with
    | .error error => .error error
    | .ok (_, after) => .ok (⟨0, [args.bytes]⟩, after) : Result) = _ ↔ _
  cases args.overlap <;> simp [eq_comm]

/-- Overlapping nonempty VM ranges terminate before any copy. -/
theorem copy_overlap (index : Index) (before : Solanalib.Runtime.InvState) (args : CopyArgs)
    (overlap : args.overlap = true) : copyStep index before args = .error .ProgramFailedToComplete
      := by
  unfold copyStep invoke
  simp only [Solanalib.Runtime.SysReq.registered, Bool.cond_true, Solanalib.Runtime.sysStep]
  change (match (if args.overlap then .error .ProgramFailedToComplete else
      .ok (Solanalib.Runtime.SysAns.ok0, before) : Result) with
    | .error error => .error error
    | .ok (_, after) => .ok (⟨0, [args.bytes]⟩, after) : Result) = _
  simp [overlap]

/-- Zero length is accepted even when the two addresses are identical. -/
theorem copy_empty (index : Index) (before : Solanalib.Runtime.InvState) (dst src : Nat) :
    copyStep index before ⟨dst, src, []⟩ = .ok (⟨0, [[]]⟩, before) := by
  exact (copy_returned_iff index before before ⟨dst, src, []⟩ _).mpr ⟨rfl, rfl, rfl⟩

/-- Every fill request supplies exactly `count` copies, with unchanged request-phase state. -/
theorem set_returned_iff (index : Index) (before after : Solanalib.Runtime.InvState) (args :
  SetArgs)
    (answer : Solanalib.Runtime.SysAns) :
    setStep index before args = .ok (answer, after) ↔
      answer = ⟨0, [List.replicate args.count args.byte]⟩ ∧ after = before := by
  simp [setStep, eq_comm]

end Solanalib.Specs.Core.RawMemory
