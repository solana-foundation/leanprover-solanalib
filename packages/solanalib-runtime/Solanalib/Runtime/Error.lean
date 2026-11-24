/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Basic

@[expose] public section

/-!
# Errors

`InstrError` has the variants of `InstructionError` in
`solana-instruction-error-2.5.0/src/lib.rs`, in the same order.
An error of the syscall layer that carries no `InstructionError`, such as
`SyscallError`, `CpiError` or `EbpfError`, reaches the instruction as
`ProgramFailedToComplete` through `execute` in Agave 4.3.2
`program-runtime/src/vm.rs`, and the model produces that variant directly.
See [execution and commit](../../source-notes/agave-4.3.2.md#execution-and-commit).
-/

namespace Solanalib.Runtime

/-- The instruction errors of Agave. -/
inductive InstrError where
  | GenericError
  | InvalidArgument
  | InvalidInstructionData
  | InvalidAccountData
  | AccountDataTooSmall
  | InsufficientFunds
  | IncorrectProgramId
  | MissingRequiredSignature
  | AccountAlreadyInitialized
  | UninitializedAccount
  | UnbalancedInstruction
  | ModifiedProgramId
  | ExternalAccountLamportSpend
  | ExternalAccountDataModified
  | ReadonlyLamportChange
  | ReadonlyDataModified
  | DuplicateAccountIndex
  | ExecutableModified
  | RentEpochModified
  | NotEnoughAccountKeys
  | AccountDataSizeChanged
  | AccountNotExecutable
  | AccountBorrowFailed
  | AccountBorrowOutstanding
  | DuplicateAccountOutOfSync
  | Custom (code : Nat)
  | InvalidError
  | ExecutableDataModified
  | ExecutableLamportChange
  | ExecutableAccountNotRentExempt
  | UnsupportedProgramId
  | CallDepth
  | MissingAccount
  | ReentrancyNotAllowed
  | MaxSeedLengthExceeded
  | InvalidSeeds
  | InvalidRealloc
  | ComputationalBudgetExceeded
  | PrivilegeEscalation
  | ProgramEnvironmentSetupFailure
  | ProgramFailedToComplete
  | ProgramFailedToCompile
  | Immutable
  | IncorrectAuthority
  | BorshIoError
  | AccountNotRentExempt
  | InvalidAccountOwner
  | ArithmeticOverflow
  | UnsupportedSysvar
  | IllegalOwner
  | MaxAccountsDataAllocationsExceeded
  /-- Program-input serialization found more than 255 instruction account
  references, including duplicates. This is distinct from CPI request limits. -/
  | MaxAccountsExceeded
  | MaxInstructionTraceLengthExceeded
  | BuiltinProgramsMustConsumeComputeUnits
  deriving DecidableEq, Repr, Inhabited

namespace InstrError

/-- The value `n << 32` of a builtin program error, as encoded by solana-program-error 3.0.1. -/
def builtin (n : Nat) : Nat := n * 2 ^ 32

/-- The conversion of a nonzero r0 through `From<T> for InstructionError`, where
`T: ToPrimitive`, in solana-instruction-error 2.5.0. The runtime input is a `u64`;
correspondence for this mathematical `Nat` input therefore requires that bound. -/
def fromU64 (v : Nat) : InstrError :=
  if v = builtin 1 then Custom 0
  else if v = builtin 2 then InvalidArgument
  else if v = builtin 3 then InvalidInstructionData
  else if v = builtin 4 then InvalidAccountData
  else if v = builtin 5 then AccountDataTooSmall
  else if v = builtin 6 then InsufficientFunds
  else if v = builtin 7 then IncorrectProgramId
  else if v = builtin 8 then MissingRequiredSignature
  else if v = builtin 9 then AccountAlreadyInitialized
  else if v = builtin 10 then UninitializedAccount
  else if v = builtin 11 then NotEnoughAccountKeys
  else if v = builtin 12 then AccountBorrowFailed
  else if v = builtin 13 then MaxSeedLengthExceeded
  else if v = builtin 14 then InvalidSeeds
  else if v = builtin 15 then BorshIoError
  else if v = builtin 16 then AccountNotRentExempt
  else if v = builtin 17 then UnsupportedSysvar
  else if v = builtin 18 then IllegalOwner
  else if v = builtin 19 then MaxAccountsDataAllocationsExceeded
  else if v = builtin 20 then InvalidRealloc
  else if v = builtin 21 then MaxInstructionTraceLengthExceeded
  else if v = builtin 22 then BuiltinProgramsMustConsumeComputeUnits
  else if v = builtin 23 then InvalidAccountOwner
  else if v = builtin 24 then ArithmeticOverflow
  else if v = builtin 25 then Immutable
  else if v = builtin 26 then IncorrectAuthority
  else if v < 2 ^ 32 then Custom v
  else InvalidError

theorem fromU64_custom {v : Nat} (h0 : v < 2 ^ 32) : fromU64 v = Custom v := by
  have h : ∀ n, 1 ≤ n → ¬ (v = builtin n) := by
    intro n hn e
    unfold builtin at e
    have : 2 ^ 32 ≤ n * 2 ^ 32 := Nat.le_mul_of_pos_left _ hn
    omega
  simp [fromU64, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
    h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
    h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
    h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide), h 24 (by decide),
    h 25 (by decide), h 26 (by decide), h0]

end InstrError

/-- The compute errors admitted by the outcome abstraction. The model has no
quantitative meter, so these alternatives do not establish execution costs or
the precise step at which Agave would exhaust its budget. See
[execution and commit](../../source-notes/agave-4.3.2.md#execution-and-commit). -/
def IsComputeError (e : InstrError) : Prop :=
  e = .ComputationalBudgetExceeded ∨ e = .ProgramFailedToComplete ∨
    e = .ProgramEnvironmentSetupFailure

/-- The transaction errors that the model produces. -/
inductive TxError where
  | AccountInUse
  | AccountLoadedTwice
  | AccountNotFound
  | ProgramAccountNotFound
  | InsufficientFundsForFee
  | InvalidAccountForFee
  | AlreadyProcessed
  | BlockhashNotFound
  | InstructionError (index : Nat) (err : InstrError)
  | InvalidProgramForExecution
  | SanitizeFailure
  | TooManyAccountLocks
  | MaxLoadedAccountsDataSizeExceeded
  | InvalidLoadedAccountsDataSizeLimit
  | DuplicateInstruction (index : Nat)
  | InsufficientFundsForRent (accountIndex : Nat)
  | UnbalancedTransaction
  | ProgramCacheHitMaxLimit
  deriving DecidableEq, Repr

end Solanalib.Runtime
