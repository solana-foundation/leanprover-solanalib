/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.ProgramPack

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.program_pack.Pack

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Generic provided Pack method with the selected unchecked decoder,
initialization query, exact error carrier and value destructor. -/
def unpack_contract : Family := ProgramPack.family
def unpack_run : FamilyRun unpack_contract := ProgramPack.reference
def unpack_sample : unpack_contract.Index := ProgramPack.sample

theorem unpack_reference : FamilyReference unpack_contract unpack_run :=
  ProgramPack.reference_holds

theorem unpack_satisfiable : FamilySatisfiable unpack_contract unpack_sample :=
  ProgramPack.sample_satisfiable

theorem unpack_has_execution : FamilyHasExecution unpack_contract unpack_run unpack_sample :=
  ProgramPack.sample_execution

end Solanalib.Specs.SolanaProgram.program_pack.Pack
