/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequest

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Hook

/-- The SPL transfer-hook Execute discriminator, the first eight bytes of
SHA-256("spl-transfer-hook-interface:execute"). -/
def executeDiscriminator : Bytes := [105, 37, 101, 197, 75, 251, 102, 26]

/-- The address-derivation domain separator used by transfer-hook interface 2.1.0. -/
def extraAccountMetasSeed : Bytes :=
  [101, 120, 116, 114, 97, 45, 97, 99, 99, 111, 117, 110, 116, 45, 109, 101, 116, 97, 115]

/-- TransferHookError::IncorrectAccount as its actual custom ProgramError code. -/
def incorrectHookAccount : Error := .Custom 2110272652
/-- AccountResolutionError::IncorrectAccount as its custom ProgramError code. -/
def incorrectExtraAccount : Error := .Custom 2724315840
/-- AccountResolutionError::InvalidBytesForSeed as its custom ProgramError code. -/
def invalidSeedBytes : Error := .Custom 2724315849
/-- AccountResolutionError::InstructionDataTooSmall as its custom code. -/
def instructionDataTooSmall : Error := .Custom 2724315851
/-- AccountResolutionError::AccountNotFound as its custom ProgramError code. -/
def accountNotFound : Error := .Custom 2724315852
/-- AccountResolutionError::AccountDataNotFound as its custom code. -/
def accountDataNotFound : Error := .Custom 2724315854
/-- AccountResolutionError::AccountDataTooSmall as its custom code. -/
def accountDataTooSmall : Error := .Custom 2724315855
/-- AccountResolutionError::InvalidBytesForPubkeyData as its custom code. -/
def invalidPubkeyBytes : Error := .Custom 2724315858
/-- TlvError::TypeNotFound as its actual custom ProgramError code. -/
def tlvTypeNotFound : Error := .Custom 1202666432
/-- PodSliceError::BufferTooSmall as its actual custom ProgramError code. -/
def podBufferTooSmall : Error := .Custom 1

/-- The 35-byte POD record. The configuration uses a 32-byte carrier but is
interpreted according to the discriminator, not always as an address. -/
structure ExtraMeta where
  /-- The exact one-byte resolution mode. -/
  discriminator : UInt8
  /-- The fixed 32-byte configuration, interpreted according to the discriminator. -/
  configuration : Solanalib.Runtime.Pubkey
  /-- The source POD Boolean signer request. -/
  isSigner : Bool
  /-- The source POD Boolean writability request. -/
  isWritable : Bool
  deriving DecidableEq, Repr

/-- POD Boolean bytes accept every nonzero value. -/
def decodeExtraMeta (bytes : Bytes) : Except Error ExtraMeta :=
  if bytes.length = 35 then
    .ok ⟨bytes[0]!, .ofBytes (Solanalib.Runtime.slice bytes 1 32), bytes[33]! != 0, bytes[34]! != 0⟩
  else .error .InvalidArgument

/-- The list header is PodU32 (alignment one). The entire remaining allocation
must be a multiple of 35, while only the declared number of items are active. -/
def decodeMetaList (bytes : Bytes) : Except Error (List ExtraMeta) := do
  if bytes.length < 4 then throw podBufferTooSmall
  let payload := bytes.drop 4
  if payload.length % 35 ≠ 0 then throw .InvalidArgument
  let count := Solanalib.Runtime.leNat (bytes.take 4)
  if payload.length / 35 < count then throw podBufferTooSmall
  (List.range count).mapM fun index => decodeExtraMeta (Solanalib.Runtime.slice payload (35 *
    index) 35)

/-- Validation scans every nonempty TLV entry before the selected entry is
looked up. A zero discriminator ends the initialized portion. -/
def validateTlvAux : Nat → Bytes → Except Error Unit
  | 0, bytes => if bytes.isEmpty then .ok () else .error .InvalidAccountData
  | fuel + 1, bytes => do
    if bytes.isEmpty then return ()
    if bytes.length < 8 then
      if bytes.all (· == 0) then return () else throw .InvalidAccountData
    if bytes.take 8 = List.replicate 8 0 then return ()
    if bytes.length < 12 then throw .InvalidAccountData
    let length := Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes 8 4)
    if bytes.length < 12 + length then throw .InvalidAccountData
    validateTlvAux fuel (bytes.drop (12 + length))

/-- The source lookup checks a full header before recognizing an empty entry.
Consequently a short all-zero suffix can pass validation but fail this lookup. -/
def findExecuteAux : Nat → Bytes → Except Error Bytes
  | 0, _ => .error .InvalidAccountData
  | fuel + 1, bytes => do
    if bytes.length < 12 then throw .InvalidAccountData
    let tag := bytes.take 8
    let length := Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes 8 4)
    if tag = executeDiscriminator then
      if bytes.length < 12 + length then throw .InvalidAccountData
      return Solanalib.Runtime.slice bytes 12 length
    if tag = List.replicate 8 0 then throw tlvTypeNotFound
    findExecuteAux fuel (bytes.drop (12 + length))

/-- Value-level full TLV admission followed by the first Execute list lookup. -/
def decodeValidation (bytes : Bytes) : Except Error (List ExtraMeta) := do
  validateTlvAux (bytes.length + 1) bytes
  let selected ← findExecuteAux (bytes.length + 1) bytes
  decodeMetaList selected

/-- Value observations of the supported account-resolution seed configurations. -/
inductive Seed where
  /-- The literal byte payload. -/
  | literal (bytes : Bytes)
  /-- A bounded slice of the current instruction data. -/
  | instructionData (offset length : Nat)
  /-- The selected ordered the public-key bytes of the account. -/
  | accountKey (index : Nat)
  /-- A bounded slice of the data of the selected ordered account. -/
  | accountData (index offset length : Nat)
  deriving DecidableEq, Repr

/-- Decode one configuration and its consumed width. The zero tag terminates
the seed list; bytes after that tag are ignored by the source. -/
def decodeSeed (bytes : Bytes) : Except Error (Option (Seed × Nat)) :=
  match bytes with
  | [] => .error .InvalidAccountData
  | tag :: rest =>
    if tag = 0 then .ok none
    else if tag = 1 then
      match rest with
      | [] => .error invalidSeedBytes
      | length :: payload =>
        if length.toNat ≤ payload.length then
          .ok (some (.literal (payload.take length.toNat), 2 + length.toNat))
        else .error invalidSeedBytes
    else if tag = 2 then
      match rest with
      | offset :: length :: _ => .ok (some (.instructionData offset.toNat length.toNat, 3))
      | _ => .error invalidSeedBytes
    else if tag = 3 then
      match rest with
      | index :: _ => .ok (some (.accountKey index.toNat, 2))
      | _ => .error invalidSeedBytes
    else if tag = 4 then
      match rest with
      | index :: offset :: length :: _ =>
        .ok (some (.accountData index.toNat offset.toNat length.toNat, 4))
      | _ => .error invalidSeedBytes
    else .error .InvalidAccountData

/-- Consume successive seed records until the source zero tag or slice end. -/
def decodeSeedsAux : Nat → Bytes → Except Error (List Seed)
  | 0, bytes => if bytes.isEmpty then .ok [] else .error .InvalidAccountData
  | fuel + 1, bytes => do
    if bytes.isEmpty then return []
    match ← decodeSeed bytes with
    | none => return []
    | some (seed, width) => return seed :: (← decodeSeedsAux fuel (bytes.drop width))

/-- Decode a complete 32-byte address configuration as seed records. -/
def decodeSeeds (configuration : Solanalib.Runtime.Pubkey) : Except Error (List Seed) :=
  decodeSeedsAux 33 configuration.bytes

/-- Ordered observations supplied while the caller holds the corresponding
shared data guards. Missing account data is distinct from a missing account. -/
abbrev Observations := List (Solanalib.Runtime.Pubkey × Option Bytes)

/-- Resolve a seed against instruction bytes and ordered account observations. -/
def resolveSeed (instructionData : Bytes) (accounts : Observations) :
    Seed → Except Error Bytes
  | .literal bytes => .ok bytes
  | .instructionData offset length =>
    if offset + length ≤ instructionData.length then
      .ok (Solanalib.Runtime.slice instructionData offset length)
    else .error instructionDataTooSmall
  | .accountKey index =>
    match accounts[index]? with
    | none => .error accountNotFound
    | some (key, _) => .ok key.bytes
  | .accountData index offset length =>
    match accounts[index]? with
    | none => .error accountNotFound
    | some (_, none) => .error accountDataNotFound
    | some (_, some bytes) =>
      if offset + length ≤ bytes.length then .ok (Solanalib.Runtime.slice bytes offset length)
      else .error accountDataTooSmall

/-- PDA search exhaustion is a panic, not a returned ProgramError. -/
inductive ResolveFailure where
  /-- An ordinary source ProgramError. -/
  | program (error : Error)
  /-- PDA search exhaustion, handled as a local panic. -/
  | noViableProgramAddress
  deriving DecidableEq, Repr

/-- Retain a ProgramError while selecting the ordinary-error branch of the resolver. -/
def liftError {Value : Type} (result : Except Error Value) : Except ResolveFailure Value :=
  result.mapError .program

/-- Resolve the two supported PubkeyData byte-source forms and bounds errors. -/
def resolveKeyData (configuration : Solanalib.Runtime.Pubkey) (instructionData : Bytes)
    (accounts : Observations) : Except Error Solanalib.Runtime.Pubkey :=
  match configuration.bytes with
  | 1 :: index :: _ =>
    if index.toNat + 32 ≤ instructionData.length then
      .ok (.ofBytes (Solanalib.Runtime.slice instructionData index.toNat 32))
    else .error instructionDataTooSmall
  | 2 :: index :: offset :: _ =>
    match accounts[index.toNat]? with
    | none => .error accountNotFound
    | some (_, none) => .error accountDataNotFound
    | some (_, some bytes) =>
      if offset.toNat + 32 ≤ bytes.length then
        .ok (.ofBytes (Solanalib.Runtime.slice bytes offset.toNat 32))
      else .error accountDataTooSmall
  | 1 :: _ | 2 :: _ => .error invalidPubkeyBytes
  | _ => .error .InvalidAccountData

/-- Account-resolution 0.11.1: external PDA program lookup precedes seed
decoding. Static addresses need no PDA or byte-source interpretation. -/
def resolve (crypto : Address.Crypto) (instructionData : Bytes) (programId :
  Solanalib.Runtime.Pubkey)
    (accounts : Observations) (extra : ExtraMeta) : Except ResolveFailure Solanalib.Runtime.CpiMeta
      := do
  let tag := extra.discriminator.toNat
  let key ←
    if tag = 0 then pure extra.configuration
    else if tag = 1 ∨ 128 ≤ tag then do
      let pdaProgram ←
        if tag = 1 then pure programId
        else match accounts[tag - 128]? with
          | some (key, _) => pure key
          | none => throw (.program accountNotFound)
      let seeds ← liftError (decodeSeeds extra.configuration)
      let values ← liftError (seeds.mapM (resolveSeed instructionData accounts))
      match Address.tryFind ⟨crypto, values, pdaProgram⟩ with
      | some (key, _) => pure key
      | none => throw .noViableProgramAddress
    else if tag = 2 then liftError (resolveKeyData extra.configuration instructionData accounts)
    else throw (.program .InvalidAccountData)
  return Solanalib.Specs.Core.Instruction.accountMeta key extra.isSigner extra.isWritable

/-- Every extra account is made a nonsigner. An existing alias can only be
writable if some earlier occurrence is writable. Newly added accounts retain
their requested writability. -/
def deescalate (previous : List Solanalib.Runtime.CpiMeta) (item : Solanalib.Runtime.CpiMeta) :
  Solanalib.Runtime.CpiMeta :=
  let aliases := previous.filter (fun prior => prior.key == item.key)
  { item with
    signerByte := 0
    writableByte := if aliases.isEmpty || aliases.any (fun prior => prior.writableByte != 0)
      then item.writableByte else 0 }

/-- The value-level Execute instruction with four readonly nonsigner accounts. -/
def executeInstruction (programId source mint destination authority : Solanalib.Runtime.Pubkey)
    (amount : Nat) : Solanalib.Runtime.CpiInstruction :=
  Solanalib.Specs.Core.Instruction.make programId
    ([source, mint, destination, authority].map
      (fun key => Solanalib.Specs.Core.Instruction.accountMeta key false false))
    (executeDiscriminator ++ Solanalib.Runtime.u64le amount)

/-- Extra-account resolution never promotes an account to a signer. -/
theorem deescalate_nonsigner (previous : List Solanalib.Runtime.CpiMeta) (item :
  Solanalib.Runtime.CpiMeta) :
    (deescalate previous item).signerByte = 0 := rfl

/-- Privilege reduction never changes the identity of the resolved account. -/
theorem deescalate_key (previous : List Solanalib.Runtime.CpiMeta) (item :
  Solanalib.Runtime.CpiMeta) :
    (deescalate previous item).key = item.key := rfl

end Solanalib.Specs.Core.Token.Hook
