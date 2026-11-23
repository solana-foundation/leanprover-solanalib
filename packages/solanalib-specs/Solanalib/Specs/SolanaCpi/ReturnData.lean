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

namespace Solanalib.Specs.SolanaCpi

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime

/-- The Solana64 branch passes the borrowed bytes and their length to the return-data syscall. Its
source binding must establish the Rust slice representation; the host no-op branch is not selected.
-/
def set_return_data_contract : Family := family RawState.setReturnStep
/-- Reference for the selected branch. -/
def set_return_data_run : FamilyRun set_return_data_contract := run RawState.setReturnStep
/-- The complete runtime contract is retained by the forwarding wrapper. -/
theorem set_return_data_reference : FamilyReference set_return_data_contract set_return_data_run :=
  reference RawState.setReturnStep
/-- Closed consistency sample. -/
def set_return_data_sample : set_return_data_contract.Index := Sample.index
/-- A successful nonempty invocation at the registered sample. -/
theorem set_return_data_has_execution : FamilyHasExecution set_return_data_contract
  set_return_data_run set_return_data_sample :=
  ⟨Sample.state, [4, 5], .returned .ok0 ({ Sample.state with ts := { Sample.state.ts with
    returnData := (Sample.state.ts.key Sample.context.frame.programIdx, [4, 5]) } }), trivial, rfl⟩
/-- The precondition of the sample is satisfiable. -/
theorem set_return_data_satisfiable : FamilySatisfiable set_return_data_contract
  set_return_data_sample :=
  set_return_data_has_execution.satisfiable

end Solanalib.Specs.SolanaCpi
