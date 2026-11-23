/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.Inputs
public import Solanalib.Specs.Core.TokenMetadataPointer

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations

open Token.Instruction Token.InstructionAllocated

/-- Burn has the same three writable/writable/authority metas as MintTo but
its own discriminator. Its caller supplies source account before mint. -/
def burnPlan (programs : ProgramSet) (args : TransferArgs) : Plan where
  programs
  programId := args.programId
  dataSteps := [.push 8, .extend (Solanalib.Runtime.u64le args.amount)]
  metas := .withCapacity (3 + args.signers.length)
    (authorityInstruction args.toAuthorityArgs []).metas

/-- Checked minting reserves the same three metas and appends the actual u8
decimal after the amount. Mint and destination are both writable. -/
def mintToCheckedPlan (programs : ProgramSet) (args : AmountDecimalsArgs) : Plan where
  programs
  programId := args.programId
  dataSteps := [.push 14, .extend (Solanalib.Runtime.u64le args.amount), .push (UInt8.ofNat
    args.decimals)]
  metas := .withCapacity (3 + args.signers.length)
    (authorityInstruction args.toTransferArgs.toAuthorityArgs []).metas

/-- Permanent-delegate initialization constructs its metadata literal before
packing tag35 and the delegate key. The zero key is not rejected here. -/
def permanentDelegatePlan (programId mint delegate : Solanalib.Runtime.Pubkey) : Plan where
  programs := .token2022
  programId
  dataSteps := [.push 35, .extend delegate.bytes]
  metas := .fromList [Solanalib.Specs.Core.Instruction.accountMeta mint false true]
  order := .metasThenData

/-- The size constructor owns a copied ExtensionType vector while packing;
pointer constructors allocate metadata before either fallible field conversion.
These cases cannot be flattened into an ordinary allocation plan. -/
inductive Construction where
  | ordinary (plan : Plan)
  | pointer (tag : UInt8) (args : Token.MetadataPointer.Args)
  | size (programId mint : Solanalib.Runtime.Pubkey) (extensions : List ExtensionType)
  deriving DecidableEq, Repr

def construction (operation : Operation) (programs : ProgramSet) (programId :
  Solanalib.Runtime.Pubkey)
    (accounts : Accounts operation) (parameters : Parameters operation) : Construction :=
  match operation with
  | .transfer => .ordinary (transferPlan {
      programId, source := (accounts 0).key, destination := (accounts 1).key,
      authority := (accounts 2).key, signers := [], amount := parameters.toNat })
  | .burn => .ordinary (burnPlan programs {
      programId, source := (accounts 1).key, destination := (accounts 0).key,
      authority := (accounts 2).key, signers := [], amount := parameters.toNat })
  | .mintTo => .ordinary (mintToPlan programs {
      programId, source := (accounts 0).key, destination := (accounts 1).key,
      authority := (accounts 2).key, signers := [], amount := parameters.toNat })
  | .transferChecked => .ordinary (transferCheckedPlan programs {
      programId, source := (accounts 0).key, destination := (accounts 2).key,
      authority := (accounts 3).key, signers := [], amount := parameters.amount.toNat,
      mint := (accounts 1).key, decimals := parameters.decimals.toNat })
  | .burnChecked => .ordinary (burnCheckedPlan programs {
      programId, source := (accounts 1).key, destination := (accounts 0).key,
      authority := (accounts 2).key, signers := [], amount := parameters.amount.toNat,
      decimals := parameters.decimals.toNat })
  | .mintToChecked => .ordinary (mintToCheckedPlan programs {
      programId, source := (accounts 0).key, destination := (accounts 1).key,
      authority := (accounts 2).key, signers := [], amount := parameters.amount.toNat,
      decimals := parameters.decimals.toNat })
  | .closeAccount => .ordinary (closeAccountPlan programs {
      programId, source := (accounts 0).key, destination := (accounts 1).key,
      authority := (accounts 2).key, signers := [] })
  | .setAuthority => .ordinary (setAuthorityPlan programs {
      programId, owned := (accounts 1).key, newAuthority := parameters.newAuthority,
      authorityType := parameters.authorityType, owner := (accounts 0).key, signers := [] })
  | .initializeAccount3 => .ordinary (initializeAccount3Plan programs {
      programId, account := (accounts 0).key, mint := (accounts 1).key, owner := (accounts 2).key })
  | .initializeMint2 => .ordinary (initializeMint2Plan programs {
      programId, mint := (accounts 0).key, decimals := parameters.decimals.toNat,
      authority := parameters.authority, freezeAuthority := parameters.freezeAuthority })
  | .initializeImmutableOwner => .ordinary (initializeImmutableOwnerPlan programs {
      programId, account := (accounts 0).key })
  | .getAccountDataSize => .size programId (accounts 0).key parameters
  | .mintCloseAuthority => .ordinary (initializeMintCloseAuthorityPlan {
      programId, account := (accounts 1).key, closeAuthority := parameters })
  | .nonTransferableMint => .ordinary (initializeNonTransferableMintPlan {
      programId, account := (accounts 1).key })
  | .permanentDelegate => .ordinary (permanentDelegatePlan programId (accounts 1).key parameters)
  | .metadataPointer => .pointer 39 {
      programId, mint := (accounts 1).key, authority := parameters.authority,
      metadataAddress := parameters.address }
  | .groupPointer => .pointer 40 {
      programId, mint := (accounts 1).key, authority := parameters.authority,
      metadataAddress := parameters.address }
  | .groupMemberPointer => .pointer 41 {
      programId, mint := (accounts 1).key, authority := parameters.authority,
      metadataAddress := parameters.address }
  | .transferHook => .pointer 36 {
      programId, mint := (accounts 1).key, authority := parameters.authority,
      metadataAddress := parameters.address }

def argsConstruction {binding : Binding} {Remaining SeedRef : Type}
    (args : Args binding Remaining SeedRef) : Construction :=
  construction binding.operation binding.programs (selectedProgram args)
    args.context.accounts args.parameters

/-- Each extension discriminator is extended as a separate little-endian u16
slice, exactly as the source pack loop. The source enum has no padding tags. -/
def sizeSteps (extensions : List ExtensionType) : List DataStep :=
  .push 21 :: extensions.map fun extension =>
    .extend [UInt8.ofNat (extension.val % 256), UInt8.ofNat (extension.val / 256)]

/-- The sole additional owner in the constructor of GetAccountDataSize. Copy and
drop are explicit dependency calls; current is consulted at the pack loop. -/
structure ExtensionOps (State Resource Unwind Terminal : Type) where
  current : State → Resource → Option (List ExtensionType)
  copySlice : Callback.Run State (List ExtensionType) Resource Unwind Terminal
  drop : Callback.Run State Resource Unit Unwind Terminal

structure Builder where
  instruction : Token.InstructionAllocated.Types
  ExtensionResource : Type
  extensions : ExtensionOps instruction.State ExtensionResource instruction.Unwind
    instruction.Terminal

/-- After the copied extension vector exists, packing reads its actual current
contents. The owned extension vector of the enum is dropped at the end of the pack
statement; returned instruction data and metadata are retained. -/
def sizeAfterCopy (types : Builder) (programId : Solanalib.Runtime.Pubkey)
    (metas : types.instruction.MetaResource) (extensions : types.ExtensionResource) :
    Callback.Run types.instruction.State Unit (Except Token.Error (Value types.instruction))
      types.instruction.Unwind types.instruction.Terminal :=
  fun before _ final => ∃ current, types.extensions.current before extensions = some current ∧
    Owned.scope types.instruction.doubleUnwind
      [fun state => types.extensions.drop state extensions]
      (Callback.map (fun data => Except.ok
        ({ programId, metas, data } : Value types.instruction))
        (buildData types.instruction (sizeSteps current))) before () final

/-- An earlier metadata owner is protected across extension copying, packing,
and destruction. A terminal dependency has no fabricated cleanup state. -/
def sizeRun (types : Builder) (programId mint : Solanalib.Runtime.Pubkey) (extensions : List
  ExtensionType) :
    Callback.Run types.instruction.State Unit (Except Token.Error (Value types.instruction))
      types.instruction.Unwind types.instruction.Terminal :=
  fun before _ final =>
    match Token.Instruction.checkProgram .either programId with
    | .error error => final = .returned (.error error) before
    | .ok () => Callback.bind
        (fun state (_ : Unit) => types.instruction.metas.fromList state
          [Solanalib.Specs.Core.Instruction.accountMeta mint false false])
        (fun metas after => Owned.protect types.instruction.doubleUnwind
          [types.instruction.metas.dropAction metas]
          (Callback.bind (fun state (_ : Unit) => types.extensions.copySlice state extensions)
            (fun copied state => sizeAfterCopy types programId metas copied state ())) after ())
        before () final

def build (types : Builder) : Callback.Run types.instruction.State Construction
    (Except Token.Error (Value types.instruction)) types.instruction.Unwind
      types.instruction.Terminal :=
  fun before input => match input with
  | .ordinary plan => Token.InstructionAllocated.run types.instruction before plan
  | .pointer tag args => Token.MetadataPointer.run tag types.instruction before args
  | .size programId mint extensions => sizeRun types programId mint extensions before ()

/-- Only the actual successful copy prefix reaches the extension-vector read.
Rejected programs and earlier non-returning exits impose no observation gate. -/
def BuildInputReady (types : Builder) (before : types.instruction.State) : Construction → Prop
  | .ordinary _ | .pointer _ _ => True
  | .size programId mint extensions =>
      Token.Instruction.checkProgram .either programId = .ok () →
      ∀ metas allocated,
        types.instruction.metas.fromList before
          [Solanalib.Specs.Core.Instruction.accountMeta mint false false]
          (.returned metas allocated) →
        ∀ copied afterCopy,
          types.extensions.copySlice allocated extensions (.returned copied afterCopy) →
          ∃ current, types.extensions.current afterCopy copied = some current

/-- The selected read domain supplies a real local packing continuation for
each actual copy result, with all later byte and cleanup exits still explicit. -/
theorem size_copy_continuation (types : Builder) (programId mint : Solanalib.Runtime.Pubkey)
    (extensions : List ExtensionType) (before allocated afterCopy : types.instruction.State)
    (metas : types.instruction.MetaResource) (copied : types.ExtensionResource)
    (ready : BuildInputReady types before (.size programId mint extensions))
    (program : Token.Instruction.checkProgram .either programId = .ok ())
    (metadata : types.instruction.metas.fromList before
      [Solanalib.Specs.Core.Instruction.accountMeta mint false false] (.returned metas allocated))
    (copy : types.extensions.copySlice allocated extensions (.returned copied afterCopy)) :
    ∃ current, types.extensions.current afterCopy copied = some current ∧
      ∀ pending final,
        Callback.map (fun data => Except.ok
          ({ programId, metas, data } : Value types.instruction))
          (buildData types.instruction (sizeSteps current)) afterCopy () pending →
        Owned.cleanup types.instruction.doubleUnwind
          [fun state => types.extensions.drop state copied] pending final →
        sizeAfterCopy types programId metas copied afterCopy () final := by
  obtain ⟨current, readable⟩ := ready program metas allocated metadata copied afterCopy copy
  exact ⟨current, readable, fun pending final packed cleaned => ⟨current, readable, pending,
    packed, cleaned⟩⟩

end Solanalib.Specs.Core.AnchorSplTokenOperations
