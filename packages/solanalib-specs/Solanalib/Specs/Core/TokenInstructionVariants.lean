/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionPlan
public import Solanalib.Specs.Core.TokenInstructionValues

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.InstructionAllocated

open Solanalib.Specs.Core.Token.Instruction

/-- InitializeAccount3 packs tag18 and the owner; the owner is not a third meta. -/
def initializeAccount3Plan (programs : ProgramSet) (args : InitializeAccount3Args) : Plan := {
  programs
  programId := args.programId
  dataSteps := [.push 18, .extend args.owner.bytes]
  metas := .fromList (initializeAccount3Instruction args).metas }

/-- CloseAccount accepts the selected program set and packs only tag9. -/
def closeAccountPlan (programs : ProgramSet) (args : AuthorityArgs) : Plan := {
  programs
  programId := args.programId
  dataSteps := [.push 9]
  metas := .withCapacity (3 + args.signers.length)
    (authorityInstruction args closeAccountData).metas }

/-- WithdrawExcessLamports constructs a three-entry literal and pushes its
signers before packing tag38 in the returned Instruction. It accepts only
Token-2022, despite sharing the final metadata layout with CloseAccount. -/
def withdrawExcessLamportsPlan (args : AuthorityArgs) : Plan := {
  programs := .token2022
  programId := args.programId
  dataSteps := [.push 38]
  metas := .fromListThenPush
    [Solanalib.Specs.Core.Instruction.accountMeta args.source false true,
      Solanalib.Specs.Core.Instruction.accountMeta args.destination false true,
      Solanalib.Specs.Core.Instruction.accountMeta args.authority args.signers.isEmpty false]
    (args.signers.map fun key => Solanalib.Specs.Core.Instruction.accountMeta key true false)
  order := .metasThenData }

/-- The allocation plan and pure InitializeAccount3 observation agree. -/
theorem initializeAccount3Plan_value (programs : ProgramSet) (args : InitializeAccount3Args) :
    (initializeAccount3Plan programs args).instruction = initializeAccount3Instruction args := by
  simp [Plan.instruction, Plan.data, MetaPlan.items, initializeAccount3Plan,
    initializeAccount3Instruction, initializeAccount3Data, DataStep.bytes,
    Solanalib.Specs.Core.Instruction.make]

/-- Metadata-first construction preserves the exact value
observation of WithdrawExcessLamports while changing its allocation and exceptional-cleanup
sequence. -/
theorem withdrawExcessLamportsPlan_value (args : AuthorityArgs) :
    (withdrawExcessLamportsPlan args).instruction =
      authorityInstruction args withdrawExcessLamportsData := by
  simp [Plan.instruction, Plan.data, MetaPlan.items, withdrawExcessLamportsPlan,
    authorityInstruction, authorityMetas, withdrawExcessLamportsData, DataStep.bytes,
    Solanalib.Specs.Core.Instruction.make]

end Solanalib.Specs.Core.Token.InstructionAllocated
