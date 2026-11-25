/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.Verifier

/-!
# Regression tests for `Solanalib.SBPF.Verifier`

Pins the accept/reject decisions of `verifyInstr` (version gating, non-zero
divisors), applies the step-safety theorem to a concrete instruction, and shows
that each rejected instruction can step to `err`.
-/

namespace SolanalibTest.SBPF.Verifier

open Solanalib.SBPF

/-! ## Accept / reject -/

/-- A `v1` division by a non-zero immediate is accepted. -/
theorem div_imm_nonzero_v1_accepted : verifyInstr (.alu .div .br0 (.imm 5)) .v1 = true := by decide

/-- A `v1` division by a zero immediate is rejected. -/
theorem div_imm_zero_v1_rejected : verifyInstr (.alu .div .br0 (.imm 0)) .v1 = false := by decide

/-- `addStk` is rejected on `v1` and accepted on `v2`. -/
theorem add_stk_v1_rejected : verifyInstr (.addStk 8) .v1 = false := by decide
theorem add_stk_v2_accepted : verifyInstr (.addStk 8) .v2 = true := by decide

/-- A 64-bit signed remainder by a zero immediate is rejected (`v2`). -/
theorem srem64_imm_zero_v2_rejected :
    verifyInstr (.pqr64 .srem .br1 (.imm 0)) .v2 = false := by decide

/-! ## Safety -/

/-- The step-safety theorem applied: a verified instruction never faults to
`err`. -/
theorem verified_div_never_errs (pc : U64) (rs : RegMap) (m : Mem) (ss : StackState) (fm : FuncMap)
    (gaps : Bool) (vmAddr cur remain : U64) :
    step pc (.alu .div .br0 (.imm 5)) rs m ss .v1 fm gaps vmAddr cur remain ≠ .err :=
  step_ne_err (by decide) pc rs m ss fm gaps vmAddr cur remain

/-! ## Negative controls

Each instruction rejected above steps to `err` from the initial state, so
`step_ne_err` needs its verifier premise. These show one faulting state per
rejection, not that every rejected instruction faults in every state. -/

/-- A `v1` division by a zero immediate steps to `err`. -/
theorem div_imm_zero_v1_errs :
    step 0 (.alu .div .br0 (.imm 0)) initRegMap initMem initStackState .v1 initFuncMap true
      0x100000000 0 8 = .err := rfl

/-- `addStk` on `v1` steps to `err`. -/
theorem add_stk_v1_errs :
    step 0 (.addStk 8) initRegMap initMem initStackState .v1 initFuncMap true
      0x100000000 0 8 = .err := rfl

/-- A `v2` 64-bit signed remainder by a zero immediate steps to `err`. -/
theorem srem64_imm_zero_v2_errs :
    step 0 (.pqr64 .srem .br1 (.imm 0)) initRegMap initMem initStackState .v2 initFuncMap true
      0x100000000 0 8 = .err := rfl

end SolanalibTest.SBPF.Verifier
