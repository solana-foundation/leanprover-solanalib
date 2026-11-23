/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.RawState
public import Solanalib.Specs.Core.RawRuntimeSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.solana_program.instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime

/-- The Solana64 branch forwards the stack-height syscall and casts the u64 result to usize. Its
source binding must establish the Rust calling convention and 64-bit result representation; the
host stub branch is not selected. -/
def get_stack_height_contract : Family := family RawState.stackStep
/-- Reference for the selected branch. -/
def get_stack_height_run : FamilyRun get_stack_height_contract := run RawState.stackStep
/-- The complete runtime contract is retained by the forwarding wrapper. -/
theorem get_stack_height_reference : FamilyReference get_stack_height_contract get_stack_height_run
  := reference RawState.stackStep
/-- Closed consistency sample. -/
def get_stack_height_sample : get_stack_height_contract.Index := Sample.index
/-- A successful nonempty invocation at the registered sample. -/
theorem get_stack_height_has_execution : FamilyHasExecution get_stack_height_contract
  get_stack_height_run get_stack_height_sample :=
  ⟨Sample.state, (), .returned ⟨1, []⟩ (Sample.state), trivial, rfl⟩
/-- The precondition of the sample is satisfiable. -/
theorem get_stack_height_satisfiable : FamilySatisfiable get_stack_height_contract
  get_stack_height_sample :=
  get_stack_height_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.solana_program.instruction
