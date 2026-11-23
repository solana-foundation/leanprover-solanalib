/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorContextOperations
public import Solanalib.Specs.Core.AccountInfoRc
public import Solanalib.Specs.Core.AnchorErrorOperations
public import Solanalib.Specs.Core.TokenInstructionAdditionalPlans

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations

/-- Source-release index for the shared mathematical support.
The registered checked-transfer family uses the 0.32.1 reference binding;
per-function profiles determine compatible source admission.
Other cases remain supporting definitions. -/
inductive Release where
  | v027 | v029 | v0321 | v102 | v112
  deriving DecidableEq, Repr

/-- The operations have different account field orders, parameter types and
temporary lifetimes even when they share an instruction encoder. -/
inductive Operation where
  | transfer | burn | mintTo | transferChecked | burnChecked | mintToChecked
  | closeAccount | setAuthority | initializeAccount3 | initializeMint2
  | initializeImmutableOwner | getAccountDataSize
  | mintCloseAuthority | nonTransferableMint | permanentDelegate
  | metadataPointer | groupPointer | groupMemberPointer | transferHook
  deriving DecidableEq, Repr

/-- Reviewed defining paths retained by the shared support.
The registered checked-transfer family selects `token2022TransferChecked0321`;
other cases do not register APIs or determine compatible release ranges. -/
inductive Binding where
  | tokenBurn027 | tokenMintTo027 | tokenTransfer027
  | token2022TransferChecked029 | tokenTransfer0321
  | token2022Burn0321 | token2022CloseAccount0321 | token2022GetAccountDataSize0321
  | token2022InitializeAccount30321 | token2022InitializeImmutableOwner0321
  | token2022InitializeMint20321 | token2022MintTo0321 | token2022SetAuthority0321
  | token2022TransferChecked0321
  | groupMemberPointer0321 | groupPointer0321 | metadataPointer0321
  | mintCloseAuthority0321 | nonTransferableMint0321 | permanentDelegate0321 | transferHook0321
  | token2022InitializeAccount3102 | token2022TransferChecked102
  | token2022BurnChecked112 | token2022MintToChecked112
  | token2022SetAuthority112 | token2022TransferChecked112
  deriving DecidableEq, Repr

abbrev Binding.release : Binding → Release
  | .tokenBurn027 | .tokenMintTo027 | .tokenTransfer027 => .v027
  | .token2022TransferChecked029 => .v029
  | .token2022InitializeAccount3102 | .token2022TransferChecked102 => .v102
  | .token2022BurnChecked112 | .token2022MintToChecked112
  | .token2022SetAuthority112 | .token2022TransferChecked112 => .v112
  | _ => .v0321

abbrev Binding.operation : Binding → Operation
  | .tokenBurn027 | .token2022Burn0321 => .burn
  | .tokenMintTo027 | .token2022MintTo0321 => .mintTo
  | .tokenTransfer027 | .tokenTransfer0321 => .transfer
  | .token2022TransferChecked029 | .token2022TransferChecked0321
  | .token2022TransferChecked102 | .token2022TransferChecked112 => .transferChecked
  | .token2022BurnChecked112 => .burnChecked
  | .token2022MintToChecked112 => .mintToChecked
  | .token2022CloseAccount0321 => .closeAccount
  | .token2022SetAuthority0321 | .token2022SetAuthority112 => .setAuthority
  | .token2022InitializeAccount30321 | .token2022InitializeAccount3102 => .initializeAccount3
  | .token2022InitializeMint20321 => .initializeMint2
  | .token2022InitializeImmutableOwner0321 => .initializeImmutableOwner
  | .token2022GetAccountDataSize0321 => .getAccountDataSize
  | .groupMemberPointer0321 => .groupMemberPointer
  | .groupPointer0321 => .groupPointer
  | .metadataPointer0321 => .metadataPointer
  | .mintCloseAuthority0321 => .mintCloseAuthority
  | .nonTransferableMint0321 => .nonTransferableMint
  | .permanentDelegate0321 => .permanentDelegate
  | .transferHook0321 => .transferHook

/-- Anchor 0.27 clones the temporary account array; the other reviewed
wrappers move its elements. This is not an Rc reference-count assumption. -/
def Release.clones : Release → Bool
  | .v027 => true
  | _ => false

def Release.storage : Release → AnchorErrorOperations.Storage
  | .v027 => .inline
  | _ => .boxed

/-- A pre-1.0 CpiContext owns its program AccountInfo. The later context
retains a copied program ID instead. -/
def Release.Program : Release → Type
  | .v027 | .v029 | .v0321 => AccountInfo.Value
  | .v102 | .v112 => Solanalib.Runtime.Pubkey

def Release.programKey (release : Release) : release.Program → Solanalib.Runtime.Pubkey :=
  match release with
  | .v027 | .v029 | .v0321 => AccountInfo.Value.key
  | .v102 | .v112 => id

def Release.programOwners (release : Release) : release.Program → List AccountInfo.Value :=
  match release with
  | .v027 | .v029 | .v0321 => fun value => [value]
  | .v102 | .v112 => fun _ => []

/-- Older dependency errors retain their owned Borsh message. Source adapters
also check the exact enum inhabitants and layout of the selected release. -/
abbrev Release.ProgramError (release : Release) (StringResource : Type) : Type :=
  match release with
  | .v027 | .v029 | .v0321 => ProgramErrorOwned.Value StringResource
  | .v102 | .v112 => ProgramError.Value

def Release.incorrectProgramId (release : Release) (StringResource : Type) :
    release.ProgramError StringResource :=
  match release with
  | .v027 | .v029 | .v0321 => .incorrectProgramId
  | .v102 | .v112 => .incorrectProgramId

def Release.invalidArgument (release : Release) (StringResource : Type) :
    release.ProgramError StringResource :=
  match release with
  | .v027 | .v029 | .v0321 => .invalidArgument
  | .v102 | .v112 => .invalidArgument

def Release.invalidInstructionData (release : Release) (StringResource : Type) :
    release.ProgramError StringResource :=
  match release with
  | .v027 | .v029 | .v0321 => .invalidInstructionData
  | .v102 | .v112 => .invalidInstructionData

/-- Field positions refer to the actual declaration order of each Accounts
struct, rather than the metadata order or invocation order. -/
abbrev Operation.accountCount : Operation → Nat
  | .transfer | .burn | .mintTo | .burnChecked | .mintToChecked
  | .closeAccount | .initializeAccount3 => 3
  | .transferChecked => 4
  | .initializeMint2 | .initializeImmutableOwner | .getAccountDataSize => 1
  | _ => 2

abbrev Accounts (operation : Operation) := Fin operation.accountCount → AccountInfo.Value

def Operation.invocationIndices (operation : Operation) : List (Fin operation.accountCount) :=
  match operation with
  | .transfer => [0, 1, 2]
  | .burn | .burnChecked => [1, 0, 2]
  | .mintTo | .mintToChecked => [1, 0, 2]
  | .transferChecked => [0, 1, 2, 3]
  | .closeAccount => [0, 1, 2]
  | .setAuthority => [1, 0]
  | .initializeAccount3 => [0, 1]
  | .initializeMint2 | .initializeImmutableOwner | .getAccountDataSize => [0]
  | .mintCloseAuthority | .nonTransferableMint | .permanentDelegate
  | .metadataPointer | .groupPointer | .groupMemberPointer | .transferHook => [0, 1]

/-- These calls use invoke, so signer-seed references are not read at all. -/
def Operation.signed : Operation → Bool
  | .initializeAccount3 | .initializeMint2 | .initializeImmutableOwner | .getAccountDataSize =>
    false
  | _ => true

def Operation.extension : Operation → Bool
  | .mintCloseAuthority | .nonTransferableMint | .permanentDelegate
  | .metadataPointer | .groupPointer | .groupMemberPointer | .transferHook => true
  | _ => false

structure AmountDecimals where
  amount : UInt64
  decimals : UInt8
  deriving DecidableEq, Repr

structure MintInitialization where
  decimals : UInt8
  authority : Solanalib.Runtime.Pubkey
  freezeAuthority : Option Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

structure AuthorityChange where
  /-- Both selected Token-2022 enums have exactly the reviewed codes 0..16. -/
  authorityType : Fin 17
  newAuthority : Option Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

structure PointerInitialization where
  authority : Option Solanalib.Runtime.Pubkey
  address : Option Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- Production ExtensionType 8.0.1 has exactly discriminants 0..27. Its
cfg(test) padding variants are absent from this source profile. -/
abbrev ExtensionType := Fin 28

def Parameters : Operation → Type
  | .transfer | .burn | .mintTo => UInt64
  | .transferChecked | .burnChecked | .mintToChecked => AmountDecimals
  | .setAuthority => AuthorityChange
  | .initializeMint2 => MintInitialization
  | .getAccountDataSize => List ExtensionType
  | .mintCloseAuthority => Option Solanalib.Runtime.Pubkey
  | .permanentDelegate => Solanalib.Runtime.Pubkey
  | .metadataPointer | .groupPointer | .groupMemberPointer | .transferHook => PointerInitialization
  | _ => Unit

/-- The seed-reference identity is retained separately from any observation of
its bytes. The source binding must establish the actual borrowed slice hierarchy. -/
abbrev Context (binding : Binding) (Remaining SeedRef : Type) :=
  AnchorContextOperations.CpiValue (Accounts binding.operation)
    binding.release.Program Remaining SeedRef

structure Args (binding : Binding) (Remaining SeedRef : Type) where
  context : Context binding Remaining SeedRef
  parameters : Parameters binding.operation

def allAccounts {binding : Binding} {Remaining SeedRef : Type}
    (args : Args binding Remaining SeedRef) : List AccountInfo.Value :=
  List.ofFn args.context.accounts

def invocationAccounts {binding : Binding} {Remaining SeedRef : Type}
    (args : Args binding Remaining SeedRef) : List AccountInfo.Value :=
  binding.operation.invocationIndices.map args.context.accounts

/-- A moved AccountInfo is removed from the eventual destructor of the context.
The InitializeAccount3 authority remains there; cloning removes no fields. -/
def retainedAccounts {binding : Binding} {Remaining SeedRef : Type}
    (args : Args binding Remaining SeedRef) : List AccountInfo.Value :=
  if binding.release.clones then allAccounts args
  else ((List.finRange binding.operation.accountCount).filter fun index =>
    !binding.operation.invocationIndices.contains index).map args.context.accounts

/-- Legacy token wrappers ignore CpiContext.program. Extension wrappers use
their token_program_id field. Other Token-2022 wrappers use the context key. -/
def selectedProgram {binding : Binding} {Remaining SeedRef : Type}
    (args : Args binding Remaining SeedRef) : Solanalib.Runtime.Pubkey :=
  match binding with
  | .tokenBurn027 | .tokenMintTo027 | .tokenTransfer027 | .tokenTransfer0321 =>
      Token.legacyProgramId
  | .groupMemberPointer0321 | .groupPointer0321 | .metadataPointer0321
  | .mintCloseAuthority0321 | .nonTransferableMint0321 | .permanentDelegate0321
  | .transferHook0321 => (args.context.accounts 0).key
  | other => other.release.programKey args.context.program

def Binding.programs : Binding → Token.Instruction.ProgramSet
  | .tokenBurn027 | .tokenMintTo027 | .tokenTransfer027 | .tokenTransfer0321 => .legacy
  | .groupMemberPointer0321 | .groupPointer0321 | .metadataPointer0321
  | .mintCloseAuthority0321 | .nonTransferableMint0321 | .permanentDelegate0321
  | .transferHook0321 => .token2022
  | _ => .either

end Solanalib.Specs.Core.AnchorSplTokenOperations
