/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionConstructors

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Instruction

/-- Fixed-width token wire encodings, before any callee interprets the data. -/
def initializeAccount3Data (owner : Solanalib.Runtime.Pubkey) : Bytes := 18 :: owner.bytes

/-- The one-byte WithdrawExcessLamports instruction payload. -/
def withdrawExcessLamportsData : Bytes := [38]

/-- Arguments of the two versioned `initialize_account3` constructors. -/
structure InitializeAccount3Args where
  /-- The caller-supplied program identity. -/
  programId : Solanalib.Runtime.Pubkey
  /-- The token account being initialized or closed. -/
  account : Solanalib.Runtime.Pubkey
  /-- The readonly mint account or observed reference. -/
  mint : Solanalib.Runtime.Pubkey
  /-- The new token-account owner serialized into the instruction data. -/
  owner : Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- Raw construction is shared; the versioned functions apply their own program check. -/
def initializeAccount3Instruction (args : InitializeAccount3Args) : Value :=
  Solanalib.Specs.Core.Instruction.make args.programId
    [Solanalib.Specs.Core.Instruction.accountMeta args.account false true,
      Solanalib.Specs.Core.Instruction.accountMeta args.mint false false]
    (initializeAccount3Data args.owner)

/-- Constructors perform the program check first. They neither check account
ownership nor enforce a multisig signer limit. -/
def initializeAccount3 (programs : ProgramSet) (args : InitializeAccount3Args) :
    Except Error Value := do
  checkProgram programs args.programId
  return initializeAccount3Instruction args

/-- CloseAccount constructor value for the selected accepted program set. -/
def closeAccount (programs : ProgramSet) (args : AuthorityArgs) : Except Error Value := do
  checkProgram programs args.programId
  return authorityInstruction args closeAccountData

/-- Token-2022-only withdrawal constructor value and program rejection. -/
def withdrawExcessLamports (args : AuthorityArgs) : Except Error Value := do
  checkProgram .token2022 args.programId
  return authorityInstruction args withdrawExcessLamportsData

/-- Constructor failure is exactly failure of its own program-id admission check. -/
theorem initializeAccount3_error_iff (programs : ProgramSet) (args : InitializeAccount3Args) :
    initializeAccount3 programs args = .error .IncorrectProgramId ↔
      programs.accepts args.programId = false := by
  cases accepted : programs.accepts args.programId <;>
    simp [initializeAccount3, checkProgram, accepted, Functor.map, Except.map]

end Solanalib.Specs.Core.Token.Instruction
