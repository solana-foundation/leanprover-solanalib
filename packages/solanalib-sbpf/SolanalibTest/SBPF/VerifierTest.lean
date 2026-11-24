/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.Verifier

/-!
# Regression tests for `Solanalib.SBPF.Verifier`

Pins the accept/reject decisions of `verifyInstr` (version gating, non-zero
divisors) and demonstrates the step-safety theorem on a concrete instruction.
-/

namespace SolanalibTest.SBPF.Verifier

open Solanalib.SBPF

/-! ## Accept / reject -/

/-- A `v1` division by a non-zero immediate is accepted. -/
example : verifyInstr (.alu .div .br0 (.imm 5)) .v1 = true := by decide

/-- A `v1` division by a zero immediate is rejected. -/
example : verifyInstr (.alu .div .br0 (.imm 0)) .v1 = false := by decide

/-- `addStk` is rejected on `v1` and accepted on `v2`. -/
example : verifyInstr (.addStk 8) .v1 = false := by decide
example : verifyInstr (.addStk 8) .v2 = true := by decide

/-- A 64-bit signed remainder by a zero immediate is rejected (`v2`). -/
example : verifyInstr (.pqr64 .srem .br1 (.imm 0)) .v2 = false := by decide

/-! ## Safety -/

/-- The step-safety theorem applied: a verified instruction never faults to
`err`. -/
example (pc : U64) (rs : RegMap) (m : Mem) (ss : StackState) (fm : FuncMap)
    (gaps : Bool) (vmAddr cur remain : U64) :
    step pc (.alu .div .br0 (.imm 5)) rs m ss .v1 fm gaps vmAddr cur remain ≠ .err :=
  step_ne_err (by decide) pc rs m ss fm gaps vmAddr cur remain

end SolanalibTest.SBPF.Verifier
