/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Basic

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.Core.ProgramError

/-- The value variants of `solana-program-error` 3.0.1. In this version
`BorshIoError` has no string payload. Other SDK versions require their own source
comparison before using this vocabulary. This is not a runtime status policy. -/
inductive Value where
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
  | borshIoError
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

namespace V3_0_1

/-- Source-defined upper-word code for each builtin error. `Custom` is handled
separately, including the distinguished encoding of custom zero. -/
def builtinTag : Value → Option Nat
  | .custom _ => none
  | .invalidArgument => some 2
  | .invalidInstructionData => some 3
  | .invalidAccountData => some 4
  | .accountDataTooSmall => some 5
  | .insufficientFunds => some 6
  | .incorrectProgramId => some 7
  | .missingRequiredSignature => some 8
  | .accountAlreadyInitialized => some 9
  | .uninitializedAccount => some 10
  | .notEnoughAccountKeys => some 11
  | .accountBorrowFailed => some 12
  | .maxSeedLengthExceeded => some 13
  | .invalidSeeds => some 14
  | .borshIoError => some 15
  | .accountNotRentExempt => some 16
  | .unsupportedSysvar => some 17
  | .illegalOwner => some 18
  | .maxAccountsDataAllocationsExceeded => some 19
  | .invalidRealloc => some 20
  | .maxInstructionTraceLengthExceeded => some 21
  | .builtinProgramsMustConsumeComputeUnits => some 22
  | .invalidAccountOwner => some 23
  | .arithmeticOverflow => some 24
  | .immutable => some 25
  | .incorrectAuthority => some 26

/-- Exact mathematical `From<ProgramError> for u64` value conversion. -/
def toStatus (error : Value) : UInt64 :=
  match error with
  | .custom code => if code = 0 then UInt64.ofNat (2^32) else UInt64.ofNat code.toNat
  | other => UInt64.ofNat ((builtinTag other).getD 0 * 2^32)

/-- Exact builtin lookup for the inverse conversion, including custom zero. -/
def ofBuiltinTag : Nat → Option Value
  | 1 => some (.custom 0)
  | 2 => some .invalidArgument
  | 3 => some .invalidInstructionData
  | 4 => some .invalidAccountData
  | 5 => some .accountDataTooSmall
  | 6 => some .insufficientFunds
  | 7 => some .incorrectProgramId
  | 8 => some .missingRequiredSignature
  | 9 => some .accountAlreadyInitialized
  | 10 => some .uninitializedAccount
  | 11 => some .notEnoughAccountKeys
  | 12 => some .accountBorrowFailed
  | 13 => some .maxSeedLengthExceeded
  | 14 => some .invalidSeeds
  | 15 => some .borshIoError
  | 16 => some .accountNotRentExempt
  | 17 => some .unsupportedSysvar
  | 18 => some .illegalOwner
  | 19 => some .maxAccountsDataAllocationsExceeded
  | 20 => some .invalidRealloc
  | 21 => some .maxInstructionTraceLengthExceeded
  | 22 => some .builtinProgramsMustConsumeComputeUnits
  | 23 => some .invalidAccountOwner
  | 24 => some .arithmeticOverflow
  | 25 => some .immutable
  | 26 => some .incorrectAuthority
  | _ => none

/-- The source converts an unrecognized `u64` to `Custom(error as u32)`;
it does not reject high bits. Raw zero also becomes `Custom(0)`. Whether a
syscall treats status zero as success is a separate caller convention. -/
def fromStatus (status : UInt64) : Value :=
  if status.toNat % 2^32 = 0 then
    (ofBuiltinTag (status.toNat / 2^32)).getD (.custom (UInt32.ofNat status.toNat))
  else .custom (UInt32.ofNat status.toNat)

@[simp] theorem accountBorrowFailed_status :
    toStatus .accountBorrowFailed = UInt64.ofNat (12 * 2^32) := rfl

@[simp] theorem customZero_status : toStatus (.custom 0) = UInt64.ofNat (2^32) := rfl

end V3_0_1

end Solanalib.Specs.Core.ProgramError
