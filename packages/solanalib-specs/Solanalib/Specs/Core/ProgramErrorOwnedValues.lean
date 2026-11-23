/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.ProgramErrorOwned

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.ProgramErrorOwned

/-- Exact legacy dependency releases used by the reviewed Anchor builds. The
later releases add enum variants; none changes the owned Borsh String field. -/
inductive Release where
  | solana1_15_2
  | solana1_18_26
  | programError2_2_2
  deriving DecidableEq, Repr

/-- Source enum membership, kept separate from error operations. This excludes
constructors that cannot be decoded from the selected Rust dependency type. -/
def available {S : Type} (release : Release) (error : Value S) : Prop :=
  match release, error with
  | .solana1_15_2, .builtinProgramsMustConsumeComputeUnits
  | .solana1_15_2, .invalidAccountOwner
  | .solana1_15_2, .arithmeticOverflow
  | .solana1_15_2, .immutable
  | .solana1_15_2, .incorrectAuthority
  | .solana1_18_26, .immutable
  | .solana1_18_26, .incorrectAuthority => False
  | _, _ => True

instance {S : Type} (release : Release) (error : Value S) :
    Decidable (available release error) := by
  cases release <;> cases error <;> simp only [available] <;> infer_instance

/-- Same status tag as the later String-free vocabulary. This is only the
numeric observation: it is not a resource conversion or equality encoding. -/
def statusVariant {S : Type} : Value S → ProgramError.Value
  | .custom code => .custom code
  | .borshIoError _ => .borshIoError
  | .invalidArgument => .invalidArgument
  | .invalidInstructionData => .invalidInstructionData
  | .invalidAccountData => .invalidAccountData
  | .accountDataTooSmall => .accountDataTooSmall
  | .insufficientFunds => .insufficientFunds
  | .incorrectProgramId => .incorrectProgramId
  | .missingRequiredSignature => .missingRequiredSignature
  | .accountAlreadyInitialized => .accountAlreadyInitialized
  | .uninitializedAccount => .uninitializedAccount
  | .notEnoughAccountKeys => .notEnoughAccountKeys
  | .accountBorrowFailed => .accountBorrowFailed
  | .maxSeedLengthExceeded => .maxSeedLengthExceeded
  | .invalidSeeds => .invalidSeeds
  | .accountNotRentExempt => .accountNotRentExempt
  | .unsupportedSysvar => .unsupportedSysvar
  | .illegalOwner => .illegalOwner
  | .maxAccountsDataAllocationsExceeded => .maxAccountsDataAllocationsExceeded
  | .invalidRealloc => .invalidRealloc
  | .maxInstructionTraceLengthExceeded => .maxInstructionTraceLengthExceeded
  | .builtinProgramsMustConsumeComputeUnits => .builtinProgramsMustConsumeComputeUnits
  | .invalidAccountOwner => .invalidAccountOwner
  | .arithmeticOverflow => .arithmeticOverflow
  | .immutable => .immutable
  | .incorrectAuthority => .incorrectAuthority

/-- Exact status value, without discarding or pretending to drop the input
payload. A source consuming conversion must separately perform its cleanup. -/
def toStatus {S : Type} (error : Value S) : UInt64 :=
  ProgramError.V3_0_1.toStatus (statusVariant error)

/-- Read the owned String of a legacy error in its actual current state. Other
variants need no String observation. Resource indices never serve as text. -/
def observe {State S : Type} (currentString : State → S → Option String)
    (state : State) : Value S → Option (Value String)
  | .custom code => some (.custom code)
  | .borshIoError message => (currentString state message).map Value.borshIoError
  | .invalidArgument => some .invalidArgument
  | .invalidInstructionData => some .invalidInstructionData
  | .invalidAccountData => some .invalidAccountData
  | .accountDataTooSmall => some .accountDataTooSmall
  | .insufficientFunds => some .insufficientFunds
  | .incorrectProgramId => some .incorrectProgramId
  | .missingRequiredSignature => some .missingRequiredSignature
  | .accountAlreadyInitialized => some .accountAlreadyInitialized
  | .uninitializedAccount => some .uninitializedAccount
  | .notEnoughAccountKeys => some .notEnoughAccountKeys
  | .accountBorrowFailed => some .accountBorrowFailed
  | .maxSeedLengthExceeded => some .maxSeedLengthExceeded
  | .invalidSeeds => some .invalidSeeds
  | .accountNotRentExempt => some .accountNotRentExempt
  | .unsupportedSysvar => some .unsupportedSysvar
  | .illegalOwner => some .illegalOwner
  | .maxAccountsDataAllocationsExceeded => some .maxAccountsDataAllocationsExceeded
  | .invalidRealloc => some .invalidRealloc
  | .maxInstructionTraceLengthExceeded => some .maxInstructionTraceLengthExceeded
  | .builtinProgramsMustConsumeComputeUnits => some .builtinProgramsMustConsumeComputeUnits
  | .invalidAccountOwner => some .invalidAccountOwner
  | .arithmeticOverflow => some .arithmeticOverflow
  | .immutable => some .immutable
  | .incorrectAuthority => some .incorrectAuthority

/-- Rust derives structural equality on the full legacy ProgramError. In
particular, different Borsh strings remain unequal even with equal statuses. -/
def equal {State S : Type} (currentString : State → S → Option String)
    (state : State) (left right : Value S) : Option Bool := do
  let left ← observe currentString state left
  let right ← observe currentString state right
  pure (decide (left = right))

/-- The source type in Solana 1.15.2 has no later builtin variants. -/
theorem unavailable_1_15_2 {S : Type} :
    ¬ available .solana1_15_2 (Value.invalidAccountOwner : Value S) := id

/-- Every reviewed legacy enum includes the owned Borsh String. -/
theorem available_borsh {S : Type} (release : Release) (message : S) :
    available release (.borshIoError message) := by
  cases release <;> trivial

/-- A same-status control distinguishes payload-sensitive equality from
numeric status equality, without assuming any heap interpretation. -/
theorem borsh_same_status_different_value :
    toStatus (.borshIoError "a") = toStatus (.borshIoError "b") ∧
      equal (fun (_ : Unit) (text : String) => some text) ()
        (.borshIoError "a") (.borshIoError "b") = some false := by
  constructor <;> decide

end Solanalib.Specs.Core.ProgramErrorOwned
