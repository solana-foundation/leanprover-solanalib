/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Instruction
public import Solanalib.Specs.Core.AddressSyscall
public import Solanalib.Runtime.Ids

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport

/-- The creation byte is selected by the two public ATA helpers. -/
inductive CreateKind where
  | create
  | idempotent
  deriving DecidableEq, Repr

def CreateKind.tag : CreateKind → UInt8
  | .create => 0
  | .idempotent => 1

/-- The four key inputs to the ATA builder. The account passed as
`associated_token` by Anchor is not a derivation input. -/
structure AssociatedKeys where
  payer : Solanalib.Runtime.Pubkey
  authority : Solanalib.Runtime.Pubkey
  mint : Solanalib.Runtime.Pubkey
  tokenProgram : Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- PDA search uses wallet, token program and mint, in that exact order. -/
def associatedSeeds (keys : AssociatedKeys) : Address.Syscall.PdaInputs :=
  ⟨[keys.authority.bytes, keys.tokenProgram.bytes, keys.mint.bytes],
    Instruction.associatedTokenProgramId⟩

/-- Build the exact wire instruction after the actual PDA search returns.
The System ID is fixed; the supplied CPI account may still have another key. -/
def associatedInstruction (kind : CreateKind) (keys : AssociatedKeys)
    (derived : Solanalib.Runtime.Pubkey) : Instruction.Value :=
  Instruction.make Instruction.associatedTokenProgramId
    [Instruction.accountMeta keys.payer true true,
      Instruction.accountMeta derived false true,
      Instruction.accountMeta keys.authority false false,
      Instruction.accountMeta keys.mint false false,
      Instruction.accountMeta Solanalib.Runtime.Ids.systemProgram false false,
      Instruction.accountMeta keys.tokenProgram false false]
    [kind.tag]

/-- `MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr`. -/
def memoProgramId : Solanalib.Runtime.Pubkey :=
  .ofNat 0x054a535a992921064d24e87160da387c7c35b5ddbc92bb81e41fa8404105448d

/-- Every remaining account contributes one readonly signer meta. Duplicate
keys, empty memo bytes and arbitrary non-UTF8 memo bytes are preserved. -/
def memoInstruction (memo : Solanalib.Runtime.Bytes) (keys : List Solanalib.Runtime.Pubkey) :
  Instruction.Value :=
  Instruction.make memoProgramId
    (keys.map fun key => Instruction.accountMeta key true false) memo

/-- Withdraw and deactivate use fixed sysvar IDs in their metadata, whereas
the Anchor wrapper forwards the independently supplied AccountInfos. -/
def deactivateInstruction (stake staker : Solanalib.Runtime.Pubkey) : Instruction.Value :=
  Instruction.make Solanalib.Runtime.Ids.stakeProgram
    [Instruction.accountMeta stake false true,
      Instruction.accountMeta Solanalib.Runtime.Ids.sysvarClock false false,
      Instruction.accountMeta staker true false]
    (Solanalib.Runtime.u32le 5)

def withdrawInstruction (stake withdrawer destination : Solanalib.Runtime.Pubkey)
    (amount : UInt64) (custodian : Option Solanalib.Runtime.Pubkey) : Instruction.Value :=
  Instruction.make Solanalib.Runtime.Ids.stakeProgram
    ([Instruction.accountMeta stake false true,
      Instruction.accountMeta destination false true,
      Instruction.accountMeta Solanalib.Runtime.Ids.sysvarClock false false,
      Instruction.accountMeta Solanalib.Runtime.Ids.sysvarStakeHistory false false,
      Instruction.accountMeta withdrawer true false] ++
      custodian.toList.map (fun key => Instruction.accountMeta key true false))
    (Solanalib.Runtime.u32le 4 ++ Solanalib.Runtime.u64le amount.toNat)

namespace Metadata

/-- A creator retains all three Borsh fields, including an arbitrary share. -/
structure Creator where
  address : Solanalib.Runtime.Pubkey
  verified : Bool
  share : UInt8
  deriving DecidableEq, Repr

structure Collection where
  verified : Bool
  key : Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- The source Borsh discriminants, in declaration order. -/
inductive UseMethod where
  | burn
  | multiple
  | single
  deriving DecidableEq, Repr

def UseMethod.tag : UseMethod → UInt8
  | .burn => 0
  | .multiple => 1
  | .single => 2

structure Uses where
  method : UseMethod
  remaining : UInt64
  total : UInt64
  deriving DecidableEq, Repr

/-- The complete mpl-token-metadata 5.1.1 DataV2. The constructor performs no
business validation of names, percentages, creator duplicates or use counts. -/
structure DataV2 where
  name : String
  symbol : String
  uri : String
  sellerFeeBasisPoints : UInt16
  creators : Option (List Creator)
  collection : Option Collection
  uses : Option Uses
  deriving DecidableEq, Repr

/-- Both CollectionDetails variants of the resolved metadata dependency. -/
inductive CollectionDetails where
  | v1 (size : UInt64)
  | v2 (padding : { bytes : Solanalib.Runtime.Bytes // bytes.length = 8 })
  deriving DecidableEq, Repr

def boolByte (value : Bool) : UInt8 := if value then 1 else 0

def optionBytes {Value : Type} (encode : Value → Solanalib.Runtime.Bytes) : Option Value →
  Solanalib.Runtime.Bytes
  | none => [0]
  | some value => [1] ++ encode value

/-- String lengths count UTF-8 bytes, and the serialized data contains the
entire encoded string without zero padding or truncation. -/
def stringBytes (value : String) : Solanalib.Runtime.Bytes :=
  Solanalib.Runtime.u32le value.toUTF8.size ++ value.toUTF8.data.toList

def Creator.encode (value : Creator) : Solanalib.Runtime.Bytes :=
  value.address.bytes ++ [boolByte value.verified, value.share]

def Collection.encode (value : Collection) : Solanalib.Runtime.Bytes :=
  [boolByte value.verified] ++ value.key.bytes

def Uses.encode (value : Uses) : Solanalib.Runtime.Bytes :=
  [value.method.tag] ++ Solanalib.Runtime.u64le value.remaining.toNat ++ Solanalib.Runtime.u64le
    value.total.toNat

def CollectionDetails.encode : CollectionDetails → Solanalib.Runtime.Bytes
  | .v1 size => [0] ++ Solanalib.Runtime.u64le size.toNat
  | .v2 padding => [1] ++ padding.val

/-- the u32-length conversions of Borsh are checked. This predicate is a codec
domain, not metadata-program business validation. An unencodable input takes
the serializer-error/unwrap branch of the operational constructor. -/
def DataV2.Encodable (value : DataV2) : Prop :=
  value.name.toUTF8.size < 2^32 ∧ value.symbol.toUTF8.size < 2^32 ∧
    value.uri.toUTF8.size < 2^32 ∧
    (match value.creators with | none => True | some values => values.length < 2^32)

instance (value : DataV2) : Decidable value.Encodable := by
  unfold DataV2.Encodable
  cases value.creators <;> infer_instance

/-- Complete wire fields in declaration order. This byte expression is used
on the encodable branch; it is not a truncating success for an oversized input. -/
def DataV2.encode (value : DataV2) : Solanalib.Runtime.Bytes :=
  stringBytes value.name ++ stringBytes value.symbol ++ stringBytes value.uri ++
    Solanalib.Runtime.leBytes 2 value.sellerFeeBasisPoints.toNat ++
    optionBytes (fun creators => Solanalib.Runtime.u32le creators.length ++
      creators.flatMap Creator.encode) value.creators ++
    optionBytes Collection.encode value.collection ++ optionBytes Uses.encode value.uses

/-- The separate argument serialization follows DataV2 with the mutability
byte and full optional collection details. -/
def argumentBytes (data : DataV2) (isMutable : Bool)
    (details : Option CollectionDetails) : Solanalib.Runtime.Bytes :=
  data.encode ++ [boolByte isMutable] ++ optionBytes CollectionDetails.encode details

/-- `metaqbxxUerdq28cj1RbAWkYQm3ybzjb6a8bt518x1s`. -/
def programId : Solanalib.Runtime.Pubkey :=
  .ofNat 0x0b7065b1e3d17c45389d527f6b04c3cd58b86c731aa0fdb549b6d1bc03f82946

structure Keys where
  metadata : Solanalib.Runtime.Pubkey
  mint : Solanalib.Runtime.Pubkey
  mintAuthority : Solanalib.Runtime.Pubkey
  payer : Solanalib.Runtime.Pubkey
  updateAuthority : Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- Anchor passes rent=None, no remaining metas, and a fixed System program.
Its separate ToAccountInfos vector still includes rent and remaining accounts. -/
def metas (keys : Keys) (updateAuthorityIsSigner : Bool) : List Instruction.Meta :=
  [Instruction.accountMeta keys.metadata false true,
    Instruction.accountMeta keys.mint false false,
    Instruction.accountMeta keys.mintAuthority true false,
    Instruction.accountMeta keys.payer true true,
    Instruction.accountMeta keys.updateAuthority updateAuthorityIsSigner false,
    Instruction.accountMeta Solanalib.Runtime.Ids.systemProgram false false]

def instruction (keys : Keys) (data : DataV2) (isMutable updateAuthorityIsSigner : Bool)
    (details : Option CollectionDetails) : Instruction.Value :=
  Instruction.make programId (metas keys updateAuthorityIsSigner)
    ([33] ++ argumentBytes data isMutable details)

/-- The complete optional metadata tail is retained after the discriminator. -/
theorem instruction_data (keys : Keys) (data : DataV2)
    (isMutable updateAuthorityIsSigner : Bool) (details : Option CollectionDetails) :
    (instruction keys data isMutable updateAuthorityIsSigner details).data =
      [33] ++ argumentBytes data isMutable details := rfl

end Metadata

end Solanalib.Specs.Core.AnchorSplSupport
