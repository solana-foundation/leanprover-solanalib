/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionAllocatedWitness
public import Solanalib.Specs.Core.TokenInstructionAllocatedFamily

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.InstructionAllocated.Witness

/-- Lift that constructive execution to any constructor family whose program
check succeeds. Versioned witnesses close these parameters and identify this
exact sample interpretation. -/
theorem family_hasExecution {Args : Type} (plan : Args → Plan) (args : Args)
    (admitted : Instruction.checkProgram (plan args).programs (plan args).programId = .ok ()) :
    FamilyHasExecution (family Args plan) (reference Args plan) sampleTypes :=
  ⟨initialState, args, .returned (.ok (returnedValue (plan args))) (returnedState (plan args)),
    trivial, run_returns (plan args) admitted⟩

/-- Legacy initialization with distinct account, mint and serialized owner. -/
def legacyInitialize : Instruction.InitializeAccount3Args :=
  ⟨legacyProgramId, .ofNat 1, .ofNat 2, .ofNat 9⟩

/-- The same initialization values under the Token-2022 program identity. -/
def tokenInitialize : Instruction.InitializeAccount3Args :=
  { legacyInitialize with programId := token2022ProgramId }

/-- A multi-byte legacy amount and three signers, including a repeated key. -/
def legacyTransfer : Instruction.TransferArgs :=
  ⟨⟨legacyProgramId, .ofNat 1, .ofNat 2, .ofNat 3, [.ofNat 4, .ofNat 4, .ofNat 5]⟩, 513⟩

/-- Token-2022 authority arguments retaining a repeated signer in order. -/
def tokenAuthority : Instruction.AuthorityArgs :=
  ⟨token2022ProgramId, .ofNat 1, .ofNat 2, .ofNat 3, [.ofNat 4, .ofNat 4]⟩

/-- Checked transfer with a multi-byte amount and the maximum decimals byte. -/
def tokenChecked : Instruction.TransferCheckedArgs := ⟨⟨tokenAuthority, 513⟩, .ofNat 7, 255⟩

end Solanalib.Specs.Core.Token.InstructionAllocated.Witness
