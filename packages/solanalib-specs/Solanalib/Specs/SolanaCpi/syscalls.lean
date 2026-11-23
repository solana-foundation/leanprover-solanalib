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

/-! The raw return-data declaration defined by solana-cpi. Its exact 2.2.1
source and dynamic-dispatch build profile remain in the capability catalog. -/

namespace Solanalib.Specs.SolanaCpi.syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime

/-- Complete request/output contract for `sol_get_return_data`. -/
def sol_get_return_data_contract : Family := family RawState.getReturnStep
/-- The unchanged runtime operation as the mathematical reference. -/
def sol_get_return_data_run : FamilyRun sol_get_return_data_contract := run RawState.getReturnStep
/-- Correctness at every fixed runtime invocation. -/
theorem sol_get_return_data_reference : FamilyReference sol_get_return_data_contract
  sol_get_return_data_run :=
  reference RawState.getReturnStep
/-- A closed, nonempty runtime interpretation. -/
def sol_get_return_data_sample : sol_get_return_data_contract.Index := Sample.index
/-- A concrete successful execution, including output bytes and the after-state. -/
theorem sol_get_return_data_has_execution :
    FamilyHasExecution sol_get_return_data_contract sol_get_return_data_run
      sol_get_return_data_sample :=
  ⟨Sample.state, ⟨1, 256, 512⟩, .returned ⟨2, [[2], (Solanalib.Runtime.Pubkey.ofNat 9).bytes]⟩
    (Sample.state), trivial, rfl⟩
/-- The successful execution witnesses satisfiable admission. -/
theorem sol_get_return_data_satisfiable : FamilySatisfiable sol_get_return_data_contract
  sol_get_return_data_sample :=
  sol_get_return_data_has_execution.satisfiable

end Solanalib.Specs.SolanaCpi.syscalls
