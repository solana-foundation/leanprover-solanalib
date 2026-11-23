/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionVariants

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Instruction

/-- An amount and decimals byte, with the source/destination interpreted by
the selected instruction. In checked burn both account and mint are writable. -/
structure AmountDecimalsArgs extends TransferArgs where
  /-- The source `u8`; its machine-width binding is separate. -/
  decimals : Nat
  deriving DecidableEq, Repr

/-- Set-authority inputs. The enum has four inhabitants in legacy Token and
seventeen in Token-2022 8.0.1. Optional public keys use the one-byte tag of the instruction wire,
not the four-byte in-memory `COption` tag. -/
structure SetAuthorityArgs (count : Nat) where
  /-- Program identity checked before allocation. -/
  programId : Solanalib.Runtime.Pubkey
  /-- Writable account or mint whose authority changes. -/
  owned : Solanalib.Runtime.Pubkey
  /-- Optional replacement authority, serialized even when it is the zero key. -/
  newAuthority : Option Solanalib.Runtime.Pubkey
  /-- Exact source enum discriminant. -/
  authorityType : Fin count
  /-- Current authority, readonly and a signer only when the signer list is empty. -/
  owner : Solanalib.Runtime.Pubkey
  /-- Ordered multisig signer occurrences; duplicates are retained. -/
  signers : List Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- Mint initialization without a Rent account. -/
structure InitializeMint2Args where
  /-- Program identity checked before allocation. -/
  programId : Solanalib.Runtime.Pubkey
  /-- The writable mint. -/
  mint : Solanalib.Runtime.Pubkey
  /-- Source decimals byte. -/
  decimals : Nat
  /-- Serialized mint authority; it is not an instruction account. -/
  authority : Solanalib.Runtime.Pubkey
  /-- Optional serialized freeze authority. -/
  freezeAuthority : Option Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- A constructor with one writable nonsigner account. -/
structure SingleAccountArgs where
  /-- Program identity checked before allocation. -/
  programId : Solanalib.Runtime.Pubkey
  /-- The sole writable account. -/
  account : Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- Mint-close authority initialization uses a one-byte optional-key encoding. -/
structure InitializeMintCloseAuthorityArgs extends SingleAccountArgs where
  /-- `Some zero` is accepted here, unlike OptionalNonZeroPubkey extensions. -/
  closeAuthority : Option Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

end Solanalib.Specs.Core.Token.Instruction

namespace Solanalib.Specs.Core.Token.InstructionAllocated

open Solanalib.Specs.Core.Token.Instruction

/-- The exact two-call `Some` and one-call `None` packing sequence. -/
def optionalKeySteps : Option Solanalib.Runtime.Pubkey → List DataStep
  | none => [.push 0]
  | some key => [.push 1, .extend key.bytes]

/-- MintTo uses the authority layout with both mint and destination writable. -/
def mintToPlan (programs : ProgramSet) (args : TransferArgs) : Plan where
  programs := programs
  programId := args.programId
  dataSteps := [.push 7, .extend (Solanalib.Runtime.u64le args.amount)]
  metas := .withCapacity (3 + args.signers.length)
    (authorityInstruction args.toAuthorityArgs []).metas

/-- BurnChecked makes both the source account and mint writable. -/
def burnCheckedPlan (programs : ProgramSet) (args : AmountDecimalsArgs) : Plan where
  programs := programs
  programId := args.programId
  dataSteps := [.push 15, .extend (Solanalib.Runtime.u64le args.amount),
    .push (UInt8.ofNat args.decimals)]
  metas := .withCapacity (3 + args.signers.length)
    (authorityInstruction args.toTransferArgs.toAuthorityArgs []).metas

/-- SetAuthority deliberately reserves `3 + signers.length` while inserting
only `2 + signers.length` metadata entries. No signer deduplication occurs. -/
def setAuthorityPlan {count : Nat} (programs : ProgramSet)
    (args : SetAuthorityArgs count) : Plan where
  programs := programs
  programId := args.programId
  dataSteps := [.push 6, .push (UInt8.ofNat args.authorityType.val)] ++
    optionalKeySteps args.newAuthority
  metas := .withCapacity (3 + args.signers.length)
    (Solanalib.Specs.Core.Instruction.accountMeta args.owned false true ::
      authorityMetas args.owner args.signers)

/-- FreezeAccount and ThawAccount share their readonly mint and authority
layout, differing only in the first wire byte. -/
def freezeThawPlan (programs : ProgramSet) (tag : UInt8) (args : AuthorityArgs) : Plan where
  programs := programs
  programId := args.programId
  dataSteps := [.push tag]
  metas := .withCapacity (3 + args.signers.length)
    ([Solanalib.Specs.Core.Instruction.accountMeta args.source false true,
      Solanalib.Specs.Core.Instruction.accountMeta args.destination false false] ++
        authorityMetas args.authority args.signers)

/-- the exact source tag of FreezeAccount. -/
def freezeAccountPlan (programs : ProgramSet) : AuthorityArgs → Plan := freezeThawPlan programs 10

/-- the exact source tag of ThawAccount. -/
def thawAccountPlan (programs : ProgramSet) : AuthorityArgs → Plan := freezeThawPlan programs 11

/-- InitializeMint2 packs first, then constructs its single metadata entry. -/
def initializeMint2Plan (programs : ProgramSet) (args : InitializeMint2Args) : Plan where
  programs := programs
  programId := args.programId
  dataSteps := [.push 20, .push (UInt8.ofNat args.decimals), .extend args.authority.bytes] ++
    optionalKeySteps args.freezeAuthority
  metas := .fromList [Solanalib.Specs.Core.Instruction.accountMeta args.mint false true]

/-- Immutable-owner initialization constructs metadata before allocating its
one-byte payload. The source accepts either Token program identity. -/
def initializeImmutableOwnerPlan (programs : ProgramSet) (args : SingleAccountArgs) : Plan where
  programs := programs
  programId := args.programId
  dataSteps := [.push 22]
  metas := .fromList [Solanalib.Specs.Core.Instruction.accountMeta args.account false true]
  order := .metasThenData

/-- Token-2022-only mint-close initialization: metadata first, then tag and
optional authority. Source account ownership is not checked by this builder. -/
def initializeMintCloseAuthorityPlan (args : InitializeMintCloseAuthorityArgs) : Plan where
  programs := .token2022
  programId := args.programId
  dataSteps := [.push 25] ++ optionalKeySteps args.closeAuthority
  metas := .fromList [Solanalib.Specs.Core.Instruction.accountMeta args.account false true]
  order := .metasThenData

/-- Token-2022-only nontransferable initialization also allocates metadata first. -/
def initializeNonTransferableMintPlan (args : SingleAccountArgs) : Plan where
  programs := .token2022
  programId := args.programId
  dataSteps := [.push 32]
  metas := .fromList [Solanalib.Specs.Core.Instruction.accountMeta args.account false true]
  order := .metasThenData

/-- Observable constructor value, without discarding the program check. The
primary models separately retain every allocation, mutation and cleanup exit. -/
def Plan.value (plan : Plan) : Except Error Solanalib.Runtime.CpiInstruction := do
  Instruction.checkProgram plan.programs plan.programId
  return plan.instruction

end Solanalib.Specs.Core.Token.InstructionAllocated
