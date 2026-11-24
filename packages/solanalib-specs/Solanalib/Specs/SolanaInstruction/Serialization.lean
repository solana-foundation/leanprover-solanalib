/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionBuilderSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaInstruction.Instruction

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.InstructionBuilder

def new_with_bincode_contract : Family := family .bincode
def new_with_bincode_run : FamilyRun new_with_bincode_contract := familyRun .bincode
def new_with_bincode_sample : new_with_bincode_contract.Index := Sample.types
  _root_.Solanalib.Runtime.Bytes

theorem new_with_bincode_reference :
    FamilyReference new_with_bincode_contract new_with_bincode_run := familyReference .bincode

theorem new_with_bincode_satisfiable :
    FamilySatisfiable new_with_bincode_contract new_with_bincode_sample :=
  ⟨Sample.constructorBefore, Sample.constructorArgs, trivial⟩

theorem new_with_bincode_has_execution :
    FamilyHasExecution new_with_bincode_contract new_with_bincode_run new_with_bincode_sample :=
  ⟨Sample.constructorBefore, Sample.constructorArgs,
    .returned ⟨.zero, (0 : Nat), (0 : Nat)⟩ (Sample.constructorAfter .bincode),
    trivial, Sample.constructorSuccess .bincode⟩

def new_with_wincode_contract : Family := family .wincode
def new_with_wincode_run : FamilyRun new_with_wincode_contract := familyRun .wincode
def new_with_wincode_sample : new_with_wincode_contract.Index := Sample.types
  _root_.Solanalib.Runtime.Bytes

theorem new_with_wincode_reference :
    FamilyReference new_with_wincode_contract new_with_wincode_run := familyReference .wincode

theorem new_with_wincode_satisfiable :
    FamilySatisfiable new_with_wincode_contract new_with_wincode_sample :=
  ⟨Sample.constructorBefore, Sample.constructorArgs, trivial⟩

theorem new_with_wincode_has_execution :
    FamilyHasExecution new_with_wincode_contract new_with_wincode_run new_with_wincode_sample :=
  ⟨Sample.constructorBefore, Sample.constructorArgs,
    .returned ⟨.zero, (0 : Nat), (0 : Nat)⟩ (Sample.constructorAfter .wincode),
    trivial, Sample.constructorSuccess .wincode⟩

end Solanalib.Specs.SolanaInstruction.Instruction
