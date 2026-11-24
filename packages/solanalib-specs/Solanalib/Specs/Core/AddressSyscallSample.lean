/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressSyscallFamily

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Address.Syscall

/-- Concrete consistency witnesses; these are not executions of cryptography,
runtime syscalls, or a Rust implementation. -/
def sampleTypes : Types := ⟨Nat, Nat, Nat⟩

def sampleInputs : PdaInputs := ⟨[[], [7, 0, 9], []], .zero⟩

def sampleReply : PdaReply := ⟨0, some .zero, 254⟩

def sampleSyscall : Callback.Run Nat PdaRequest PdaReply Nat Nat :=
  fun before _ outcome => outcome = .returned sampleReply (before + 7)

def samplePanic : Callback.Run Nat SearchPanic Empty Nat Nat :=
  fun before _ outcome => outcome = .unwound 91 (before + 11)

def sampleTryCall : TryCall sampleTypes := ⟨sampleInputs, sampleSyscall⟩

def sampleFindCall : FindCall sampleTypes := ⟨sampleTryCall, samplePanic⟩

/-- The actual sample reply supplies its address on every successful exit. -/
theorem sample_initialized (before : Nat) (inputs : PdaInputs) :
    SuccessInitialized sampleSyscall before inputs := by
  intro reply after called _
  cases called
  exact ⟨.zero, rfl⟩

theorem sampleTry_execution :
    tryFamilyRun sampleTypes (3 : Nat) sampleTryCall (.returned (some (.zero, 254)) (10 : Nat)) :=
      by
  apply tryRun_returned sampleSyscall 3 10 sampleInputs sampleReply _ rfl
  exact ⟨.zero, rfl, rfl⟩

theorem sampleFind_execution :
    findFamilyRun sampleTypes (3 : Nat) sampleFindCall (.returned (.zero, 254) (10 : Nat)) :=
  ⟨.returned (some (.zero, 254)) (10 : Nat), sampleTry_execution, rfl⟩

def sampleCurveCall : CurveCall sampleTypes :=
  ⟨.zero, fun (before : Nat) _ outcome => outcome = .returned 0 (before + 5)⟩

theorem sampleCurve_execution :
    curveFamilyRun sampleTypes (3 : Nat) sampleCurveCall (.returned true (8 : Nat)) :=
  ⟨.returned (0 : UInt64) (8 : Nat), rfl, rfl⟩

end Solanalib.Specs.Core.Address.Syscall
