/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.ProgramError
public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.ProgramErrorOwned

/-- The older Solana error representation. Unlike `ProgramError.Value` for
3.0.1, `BorshIoError` owns a String. The parameter names that actual resource,
so moving, comparing, formatting and dropping the error retain its identity.
Availability of the later builtin variants is a separate release profile. -/
inductive Value (StringResource : Type) where
  | custom (code : UInt32)
  | invalidArgument
  | invalidInstructionData
  | invalidAccountData
  | accountDataTooSmall
  | insufficientFunds
  | incorrectProgramId
  | missingRequiredSignature
  | accountAlreadyInitialized
  | uninitializedAccount
  | notEnoughAccountKeys
  | accountBorrowFailed
  | maxSeedLengthExceeded
  | invalidSeeds
  | borshIoError (message : StringResource)
  | accountNotRentExempt
  | unsupportedSysvar
  | illegalOwner
  | maxAccountsDataAllocationsExceeded
  | invalidRealloc
  | maxInstructionTraceLengthExceeded
  | builtinProgramsMustConsumeComputeUnits
  | invalidAccountOwner
  | arithmeticOverflow
  | immutable
  | incorrectAuthority
  deriving DecidableEq, Repr

/-- Exactly the owned fields of the selected variant. Numeric status encoding
is an observation, never a substitute for this ownership information. -/
def strings {S : Type} : Value S → List S
  | .borshIoError message => [message]
  | _ => []

/-- Dropping a legacy error releases its one String when present. The concrete
String destructor cannot unwind; its actual terminal exits are retained. -/
def drop {State S Terminal : Type}
    (dropString : Callback.Run State S Unit Empty Terminal) :
    Callback.Run State (Value S) Unit Empty Terminal :=
  fun before error outcome =>
    match error with
    | .borshIoError message => dropString before message outcome
    | _ => outcome = .returned () before

/-- The legacy string is not discarded on a mismatch/error-cleanup path. -/
theorem drop_borsh {State S Terminal : Type}
    (dropString : Callback.Run State S Unit Empty Terminal)
    (before : State) (message : S) (outcome : Outcome State Unit Empty Terminal) :
    drop dropString before (.borshIoError message) outcome ↔
      dropString before message outcome := Iff.rfl

/-- A builtin without owned data has no destructor dependency. -/
theorem drop_invalidAccountData {State S Terminal : Type}
    (dropString : Callback.Run State S Unit Empty Terminal)
    (before : State) (outcome : Outcome State Unit Empty Terminal) :
    drop dropString before .invalidAccountData outcome ↔
      outcome = .returned () before := Iff.rfl

end Solanalib.Specs.Core.ProgramErrorOwned
