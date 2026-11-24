/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.RawMemory
public import Solanalib.Specs.Core.RawAddress
public import Solanalib.Specs.Core.RawState
public import Solanalib.Specs.Core.RawRuntimeSample
public import Solanalib.Specs.Core.RawSyscall

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.syscalls.definitions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime

def sol_memcpy__contract : Family := family RawMemory.copyStep
/-- The unchanged runtime operation as the mathematical reference. -/
def sol_memcpy__run : FamilyRun sol_memcpy__contract := run RawMemory.copyStep
/-- Correctness at every fixed runtime invocation. -/
theorem sol_memcpy__reference : FamilyReference sol_memcpy__contract sol_memcpy__run :=
  reference RawMemory.copyStep
/-- A closed, nonempty runtime interpretation. -/
def sol_memcpy__sample : sol_memcpy__contract.Index := Sample.index
/-- A concrete successful execution, including output bytes and the after-state. -/
theorem sol_memcpy__has_execution :
    FamilyHasExecution sol_memcpy__contract sol_memcpy__run sol_memcpy__sample :=
  ⟨Sample.state, ⟨256, 512, [1, 2, 3]⟩, .returned ⟨0, [[1, 2, 3]]⟩ (Sample.state), trivial, rfl⟩
/-- The successful execution witnesses satisfiable admission. -/
theorem sol_memcpy__satisfiable : FamilySatisfiable sol_memcpy__contract sol_memcpy__sample :=
  sol_memcpy__has_execution.satisfiable

/-- Complete request/output contract for `sol_memset_`. -/
def sol_memset__contract : Family := family RawMemory.setStep
/-- The unchanged runtime operation as the mathematical reference. -/
def sol_memset__run : FamilyRun sol_memset__contract := run RawMemory.setStep
/-- Correctness at every fixed runtime invocation. -/
theorem sol_memset__reference : FamilyReference sol_memset__contract sol_memset__run :=
  reference RawMemory.setStep
/-- A closed, nonempty runtime interpretation. -/
def sol_memset__sample : sol_memset__contract.Index := Sample.index
/-- A concrete successful execution, including output bytes and the after-state. -/
theorem sol_memset__has_execution :
    FamilyHasExecution sol_memset__contract sol_memset__run sol_memset__sample :=
  ⟨Sample.state, ⟨42, 3⟩, .returned ⟨0, [[42, 42, 42]]⟩ (Sample.state), trivial, rfl⟩
/-- The successful execution witnesses satisfiable admission. -/
theorem sol_memset__satisfiable : FamilySatisfiable sol_memset__contract sol_memset__sample :=
  sol_memset__has_execution.satisfiable

/-- Complete request/output contract for `sol_create_program_address`. -/
def sol_create_program_address_contract : Family := family RawAddress.createStep
/-- The unchanged runtime operation as the mathematical reference. -/
def sol_create_program_address_run : FamilyRun sol_create_program_address_contract := run
  RawAddress.createStep
/-- Correctness at every fixed runtime invocation. -/
theorem sol_create_program_address_reference : FamilyReference sol_create_program_address_contract
  sol_create_program_address_run :=
  reference RawAddress.createStep
/-- A closed, nonempty runtime interpretation. -/
def sol_create_program_address_sample : sol_create_program_address_contract.Index := Sample.index
/-- A concrete successful execution, including output bytes and the after-state. -/
theorem sol_create_program_address_has_execution :
    FamilyHasExecution sol_create_program_address_contract sol_create_program_address_run
      sol_create_program_address_sample :=
  ⟨Sample.state, ⟨[[1], [], [2, 3]], Solanalib.Runtime.Pubkey.zero⟩, .returned ⟨0,
    [(Solanalib.Runtime.Pubkey.ofBytes (List.replicate 32 7)).bytes]⟩ (Sample.state), trivial, rfl⟩
/-- The successful execution witnesses satisfiable admission. -/
theorem sol_create_program_address_satisfiable : FamilySatisfiable
  sol_create_program_address_contract sol_create_program_address_sample :=
  sol_create_program_address_has_execution.satisfiable

/-- Complete request/output contract for `sol_try_find_program_address`. -/
def sol_try_find_program_address_contract : Family := family RawAddress.findStep
/-- The unchanged runtime operation as the mathematical reference. -/
def sol_try_find_program_address_run : FamilyRun sol_try_find_program_address_contract := run
  RawAddress.findStep
/-- Correctness at every fixed runtime invocation. -/
theorem sol_try_find_program_address_reference : FamilyReference
  sol_try_find_program_address_contract sol_try_find_program_address_run :=
  reference RawAddress.findStep
/-- A closed, nonempty runtime interpretation. -/
def sol_try_find_program_address_sample : sol_try_find_program_address_contract.Index :=
  Sample.index
/-- A concrete successful execution, including output bytes and the after-state. -/
theorem sol_try_find_program_address_has_execution :
    FamilyHasExecution sol_try_find_program_address_contract sol_try_find_program_address_run
      sol_try_find_program_address_sample :=
  ⟨Sample.state, ⟨⟨[[1]], Solanalib.Runtime.Pubkey.zero⟩, 256, 512⟩, .returned ⟨0,
    [(Solanalib.Runtime.Pubkey.ofBytes (List.replicate 32 7)).bytes, [255]]⟩ (Sample.state),
    trivial, rfl⟩
/-- The successful execution witnesses satisfiable admission. -/
theorem sol_try_find_program_address_satisfiable : FamilySatisfiable
  sol_try_find_program_address_contract sol_try_find_program_address_sample :=
  sol_try_find_program_address_has_execution.satisfiable

/-- Complete request/output contract for `sol_get_clock_sysvar`. -/
def sol_get_clock_sysvar_contract : Family := family (RawState.typedStep .clock)
/-- The unchanged runtime operation as the mathematical reference. -/
def sol_get_clock_sysvar_run : FamilyRun sol_get_clock_sysvar_contract := run (RawState.typedStep
  .clock)
/-- Correctness at every fixed runtime invocation. -/
theorem sol_get_clock_sysvar_reference : FamilyReference sol_get_clock_sysvar_contract
  sol_get_clock_sysvar_run :=
  reference (RawState.typedStep .clock)
/-- A closed, nonempty runtime interpretation. -/
def sol_get_clock_sysvar_sample : sol_get_clock_sysvar_contract.Index := Sample.index
/-- A concrete successful execution, including output bytes and the after-state. -/
theorem sol_get_clock_sysvar_has_execution :
    FamilyHasExecution sol_get_clock_sysvar_contract sol_get_clock_sysvar_run
      sol_get_clock_sysvar_sample :=
  ⟨Sample.state, (256 : Nat), .returned ⟨0, [Sample.sysvars.clock.encode]⟩ (Sample.state), trivial,
    rfl⟩
/-- The successful execution witnesses satisfiable admission. -/
theorem sol_get_clock_sysvar_satisfiable : FamilySatisfiable sol_get_clock_sysvar_contract
  sol_get_clock_sysvar_sample :=
  sol_get_clock_sysvar_has_execution.satisfiable

/-- Complete request/output contract for `sol_get_rent_sysvar`. -/
def sol_get_rent_sysvar_contract : Family := family (RawState.typedStep .rent)
/-- The unchanged runtime operation as the mathematical reference. -/
def sol_get_rent_sysvar_run : FamilyRun sol_get_rent_sysvar_contract := run (RawState.typedStep
  .rent)
/-- Correctness at every fixed runtime invocation. -/
theorem sol_get_rent_sysvar_reference : FamilyReference sol_get_rent_sysvar_contract
  sol_get_rent_sysvar_run :=
  reference (RawState.typedStep .rent)
/-- A closed, nonempty runtime interpretation. -/
def sol_get_rent_sysvar_sample : sol_get_rent_sysvar_contract.Index := Sample.index
/-- A concrete successful execution, including output bytes and the after-state. -/
theorem sol_get_rent_sysvar_has_execution :
    FamilyHasExecution sol_get_rent_sysvar_contract sol_get_rent_sysvar_run
      sol_get_rent_sysvar_sample :=
  ⟨Sample.state, (256 : Nat), .returned ⟨0, [Sample.sysvars.rent.reprC]⟩ (Sample.state), trivial,
    rfl⟩
/-- The successful execution witnesses satisfiable admission. -/
theorem sol_get_rent_sysvar_satisfiable : FamilySatisfiable sol_get_rent_sysvar_contract
  sol_get_rent_sysvar_sample :=
  sol_get_rent_sysvar_has_execution.satisfiable

end Solanalib.Specs.SolanaProgram.syscalls.definitions

namespace Solanalib.Specs.SolanaProgram.syscalls.definitions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawSyscall

def sol_sha256_contract : Family := sha256Family
/-- The reference: the outcomes of the environment for the hash request, or for `.abort` on a call
with too many slices or an unaligned one. -/
def sol_sha256_run : FamilyRun sol_sha256_contract := sha256FamilyRun
/-- `sol_sha256_run` is the reference of `sol_sha256_contract` at every environment. -/
theorem sol_sha256_reference : FamilyReference sol_sha256_contract sol_sha256_run :=
  sha256Family_reference
/-- The sample environment. -/
def sol_sha256_sample : sol_sha256_contract.Index := sample
/-- Two slices at an aligned `vals` are hashed: status `0` and the 32 bytes of the sample, with the
request logged. -/
theorem sol_sha256_has_execution :
    FamilyHasExecution sol_sha256_contract sol_sha256_run sol_sha256_sample :=
  ⟨([] : List Solanalib.Runtime.SysReq), ⟨[[1, 2], [3]], true⟩,
    .returned ⟨0, [List.replicate 32 0]⟩ [.hash .sha256 [[1, 2], [3]]], trivial, rfl⟩
/-- The precondition holds at the sample environment, by the execution witness. -/
theorem sol_sha256_satisfiable : FamilySatisfiable sol_sha256_contract sol_sha256_sample :=
  sol_sha256_has_execution.satisfiable

end Solanalib.Specs.SolanaProgram.syscalls.definitions
