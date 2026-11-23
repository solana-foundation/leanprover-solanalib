/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstruction

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Instruction

/-- Program identities accepted by the selected constructor. In particular,
`WithdrawExcessLamports` accepts only Token-2022. -/
inductive ProgramSet where
  /-- Accept only the legacy Token program. -/
  | legacy
  /-- Accept only the Token-2022 program. -/
  | token2022
  /-- Accept either declared Token program. -/
  | either
  deriving DecidableEq, Repr

/-- The check is on the program identity of the instruction, not its accounts. -/
def ProgramSet.accepts (programs : ProgramSet) (programId : Solanalib.Runtime.Pubkey) : Bool :=
  match programs with
  | .legacy => programId == legacyProgramId
  | .token2022 => programId == token2022ProgramId
  | .either => programId == token2022ProgramId || programId == legacyProgramId

/-- The source check runs before instruction construction. -/
def checkProgram (programs : ProgramSet) (programId : Solanalib.Runtime.Pubkey) : Except Error Unit
  :=
  if programs.accepts programId then .ok () else .error .IncorrectProgramId

/-- Legacy Token transfer constructor value, including program rejection. -/
def transfer (args : TransferArgs) : Except Error Value := do
  checkProgram .legacy args.programId
  return authorityInstruction args.toAuthorityArgs (transferData args.amount)

/-- Checked-transfer constructor value for the selected accepted program set. -/
def transferChecked (programs : ProgramSet) (args : TransferCheckedArgs) :
    Except Error Value := do
  checkProgram programs args.programId
  return transferCheckedInstruction args


end Solanalib.Specs.Core.Token.Instruction
