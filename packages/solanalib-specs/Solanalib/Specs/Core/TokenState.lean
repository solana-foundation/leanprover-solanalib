/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Token

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- An exact 82-byte mint storage view. Pinocchio admits all byte patterns;
semantic validation of the copied Mint of SPL is a separate operation below. -/
structure MintRaw where
  /-- The complete base mint bytes. -/
  bytes : Bytes
  /-- All base fields are present. -/
  length_eq : bytes.length = mintLength
  deriving DecidableEq, Repr

/-- An exact 165-byte token-account storage view. It deliberately retains
invalid option tags and state bytes admitted by the Pinocchio view parser. -/
structure AccountRaw where
  /-- The complete base token-account bytes. -/
  bytes : Bytes
  /-- All base fields are present. -/
  length_eq : bytes.length = accountLength
  deriving DecidableEq, Repr

/-- Exact-size raw mint construction. -/
def readMintRaw (bytes : Bytes) : Except Error MintRaw :=
  if size : bytes.length = mintLength then .ok ⟨bytes, size⟩
  else .error .InvalidAccountData

/-- Exact-size raw token-account construction. -/
def readAccountRaw (bytes : Bytes) : Except Error AccountRaw :=
  if size : bytes.length = accountLength then .ok ⟨bytes, size⟩
  else .error .InvalidAccountData

/-- A checked mint base prefix, used only after the version-specific extended-layout admission of a
caller. No TLV or initialization validation occurs here. -/
def readMintPrefix (bytes : Bytes) : Except Error MintRaw :=
  if size : mintLength ≤ bytes.length then
    .ok ⟨bytes.take mintLength, by simp [List.length_take, Nat.min_eq_left size]⟩
  else .error .InvalidAccountData

/-- A checked account base prefix, independent of extension admission. -/
def readAccountPrefix (bytes : Bytes) : Except Error AccountRaw :=
  if size : accountLength ≤ bytes.length then
    .ok ⟨bytes.take accountLength, by simp [List.length_take, Nat.min_eq_left size]⟩
  else .error .InvalidAccountData

/-- The raw COption mint-authority tag of the mint. -/
def MintRaw.mintAuthorityTag (mint : MintRaw) : Nat :=
  Solanalib.Runtime.leNat (Solanalib.Runtime.slice mint.bytes 0 4)

/-- The authority payload of the mint, whether or not its option tag is set. -/
def MintRaw.mintAuthority (mint : MintRaw) : Solanalib.Runtime.Pubkey :=
  .ofBytes (Solanalib.Runtime.slice mint.bytes 4 32)

/-- Supply occupies exactly bytes 36 through 43. -/
def MintRaw.supply (mint : MintRaw) : Nat :=
  Solanalib.Runtime.leNat (Solanalib.Runtime.slice mint.bytes 36 8)

/-- Decimal precision is the byte at offset 44. -/
def MintRaw.decimals (mint : MintRaw) : UInt8 := mint.bytes[44]!

/-- Pinocchio keeps the raw initialization byte; SPL Pack validates 0 or 1. -/
def MintRaw.initializedByte (mint : MintRaw) : UInt8 := mint.bytes[45]!

/-- The raw COption freeze-authority tag of the mint. -/
def MintRaw.freezeAuthorityTag (mint : MintRaw) : Nat :=
  Solanalib.Runtime.leNat (Solanalib.Runtime.slice mint.bytes 46 4)

/-- The freeze-authority payload, independent of its option tag. -/
def MintRaw.freezeAuthority (mint : MintRaw) : Solanalib.Runtime.Pubkey :=
  .ofBytes (Solanalib.Runtime.slice mint.bytes 50 32)

/-- The mint key of the token account. -/
def AccountRaw.mint (account : AccountRaw) : Solanalib.Runtime.Pubkey :=
  .ofBytes (Solanalib.Runtime.slice account.bytes 0 32)

/-- The owner field of the token account, distinct from the runtime account owner. -/
def AccountRaw.owner (account : AccountRaw) : Solanalib.Runtime.Pubkey :=
  .ofBytes (Solanalib.Runtime.slice account.bytes 32 32)

/-- Token balance occupies exactly bytes 64 through 71. -/
def AccountRaw.amount (account : AccountRaw) : Nat :=
  Solanalib.Runtime.leNat (Solanalib.Runtime.slice account.bytes 64 8)

/-- The raw COption delegate tag. -/
def AccountRaw.delegateTag (account : AccountRaw) : Nat :=
  Solanalib.Runtime.leNat (Solanalib.Runtime.slice account.bytes 72 4)

/-- The delegate payload, independent of its option tag. -/
def AccountRaw.delegate (account : AccountRaw) : Solanalib.Runtime.Pubkey :=
  .ofBytes (Solanalib.Runtime.slice account.bytes 76 32)

/-- The raw account-state byte; no enum conversion has occurred. -/
def AccountRaw.stateByte (account : AccountRaw) : UInt8 := account.bytes[108]!

/-- The raw COption native-token tag. -/
def AccountRaw.nativeTag (account : AccountRaw) : Nat :=
  Solanalib.Runtime.leNat (Solanalib.Runtime.slice account.bytes 109 4)

/-- Native-token reserve occupies the bytes after its option tag. -/
def AccountRaw.nativeAmount (account : AccountRaw) : Nat :=
  Solanalib.Runtime.leNat (Solanalib.Runtime.slice account.bytes 113 8)

/-- The delegated amount is a little-endian u64. -/
def AccountRaw.delegatedAmount (account : AccountRaw) : Nat :=
  Solanalib.Runtime.leNat (Solanalib.Runtime.slice account.bytes 121 8)

/-- The raw COption close-authority tag. -/
def AccountRaw.closeAuthorityTag (account : AccountRaw) : Nat :=
  Solanalib.Runtime.leNat (Solanalib.Runtime.slice account.bytes 129 4)

/-- The close-authority payload, independent of its option tag. -/
def AccountRaw.closeAuthority (account : AccountRaw) : Solanalib.Runtime.Pubkey :=
  .ofBytes (Solanalib.Runtime.slice account.bytes 133 32)

/-- The exact-length view justifies the u64 supply bound. -/
theorem MintRaw.supply_lt (mint : MintRaw) : mint.supply < Solanalib.Runtime.U64_LIMIT := by
  have range : 36 + 8 ≤ mint.bytes.length := by rw [mint.length_eq]; decide
  have bound := Solanalib.Runtime.leNat_lt (Solanalib.Runtime.slice mint.bytes 36 8)
  have width : 256^8 = Solanalib.Runtime.U64_LIMIT := by decide
  simpa only [MintRaw.supply, Solanalib.Runtime.length_slice_of_le range, width] using bound

/-- The exact-length view justifies the u64 balance bound. -/
theorem AccountRaw.amount_lt (account : AccountRaw) : account.amount < Solanalib.Runtime.U64_LIMIT
  := by
  have range : 64 + 8 ≤ account.bytes.length := by rw [account.length_eq]; decide
  have bound := Solanalib.Runtime.leNat_lt (Solanalib.Runtime.slice account.bytes 64 8)
  have width : 256^8 = Solanalib.Runtime.U64_LIMIT := by decide
  simpa only [AccountRaw.amount, Solanalib.Runtime.length_slice_of_le range, width] using bound

/-- Validated SPL Mint fields. This copied value does not itself own a Rust
borrow guard; an AccountView wrapper retains that token separately. -/
structure Mint where
  /-- The validated optional mint authority. -/
  mintAuthority : Option Solanalib.Runtime.Pubkey
  /-- The decoded u64 supply. -/
  supply : Nat
  /-- The decimal precision byte. -/
  decimals : UInt8
  /-- The validated Boolean initialization flag. -/
  isInitialized : Bool
  /-- The validated optional freeze authority. -/
  freezeAuthority : Option Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- Validated SPL token-account fields. Runtime ownership and guard permission
are separate from the token owner and option fields in these bytes. -/
structure Account where
  /-- The token mint key. -/
  mint : Solanalib.Runtime.Pubkey
  /-- The token owner field, distinct from the runtime account owner. -/
  owner : Solanalib.Runtime.Pubkey
  /-- The decoded u64 token balance. -/
  amount : Nat
  /-- The validated optional delegate. -/
  delegate : Option Solanalib.Runtime.Pubkey
  /-- The validated source state enum. -/
  state : AccountState
  /-- The optional native-token rent reserve. -/
  nativeAmount : Option Nat
  /-- The decoded u64 delegated amount. -/
  delegatedAmount : Nat
  /-- The validated optional close authority. -/
  closeAuthority : Option Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- the four-byte COption tag of SPL accepts exactly 0 and 1. The absent case does
not constrain the ignored payload bytes. -/
def decodeCOption {Value : Type} (tag : Nat) (value : Value) : Except Error (Option Value) :=
  if tag = 0 then .ok none
  else if tag = 1 then .ok (some value)
  else .error .InvalidAccountData

/-- the Boolean byte parser of SPL, distinct from the nonzero interpretation of PodBool. -/
def decodeBool (byte : UInt8) : Except Error Bool :=
  if byte = 0 then .ok false
  else if byte = 1 then .ok true
  else .error .InvalidAccountData

/-- the exact Mint field-validation order of SPL: mint authority, initialization
Boolean, then freeze authority. A false initialization flag remains admitted. -/
def decodeMint (raw : MintRaw) : Except Error Mint := do
  let mintAuthority ← decodeCOption raw.mintAuthorityTag raw.mintAuthority
  let initialized ← decodeBool raw.initializedByte
  let freezeAuthority ← decodeCOption raw.freezeAuthorityTag raw.freezeAuthority
  pure ⟨mintAuthority, raw.supply, raw.decimals, initialized, freezeAuthority⟩

/-- the exact Account field-validation order of SPL: delegate option, account
state, native option, then close-authority option. -/
def decodeAccount (raw : AccountRaw) : Except Error Account := do
  let delegate ← decodeCOption raw.delegateTag raw.delegate
  let state ← match decodeAccountState raw.stateByte with
    | some state => .ok state
    | none => .error .InvalidAccountData
  let nativeAmount ← decodeCOption raw.nativeTag raw.nativeAmount
  let closeAuthority ← decodeCOption raw.closeAuthorityTag raw.closeAuthority
  pure ⟨raw.mint, raw.owner, raw.amount, delegate, state, nativeAmount,
    raw.delegatedAmount, closeAuthority⟩

/-- The exact-size Mint decoding of Pack without the initialized-account check.
The name does not waive representation checks or permit truncated data. -/
def unpackMintUnchecked (bytes : Bytes) : Except Error Mint :=
  (readMintRaw bytes).bind decodeMint

/-- The initialized Mint decoding of Pack, after all base field checks. -/
def unpackMint (bytes : Bytes) : Except Error Mint := do
  let mint ← unpackMintUnchecked bytes
  if mint.isInitialized then pure mint else .error .UninitializedAccount

/-- The exact-size Account decoding of Pack without its initialization check. -/
def unpackAccountUnchecked (bytes : Bytes) : Except Error Account :=
  (readAccountRaw bytes).bind decodeAccount

/-- The initialized Account decoding of Pack, accepting initialized and frozen. -/
def unpackAccount (bytes : Bytes) : Except Error Account := do
  let account ← unpackAccountUnchecked bytes
  if account.state = .uninitialized then .error .UninitializedAccount else pure account

/-- PodMint admission used by extension account sizing. Unlike Pack Mint, it
accepts any nonzero initialization byte and does not validate COption tags. -/
def unpackPodMint (bytes : Bytes) : Except Error MintRaw := do
  let raw ← readMintRaw bytes
  if raw.initializedByte = 0 then .error .UninitializedAccount else pure raw

/-- the layout admission of Token-2022 Pinocchio: exact base size, or a non-multisig
extended buffer with its account-type byte at offset 165. No TLV parsing,
padding validation or initialized-state check is implied. -/
def pinocchio2022Layout (bytes : Bytes) (baseLength : Nat) (accountType : UInt8) : Bool :=
  bytes.length == baseLength ||
    (bytes.length != multisigLength && accountLength < bytes.length &&
      bytes[accountLength]! == accountType)

/-- The short-circuit check of the extended layout makes its type-byte access
in-bounds whenever it is used. -/
theorem pinocchio2022Layout_of_extended {bytes : Bytes} {baseLength : Nat}
    {accountType : UInt8}
    (notBase : bytes.length ≠ baseLength)
    (accepted : pinocchio2022Layout bytes baseLength accountType = true) :
    bytes.length ≠ multisigLength ∧ accountLength < bytes.length ∧
      bytes[accountLength]! = accountType := by
  simpa [pinocchio2022Layout, notBase, Bool.and_eq_true, and_assoc] using accepted

end Solanalib.Specs.Core.Token
