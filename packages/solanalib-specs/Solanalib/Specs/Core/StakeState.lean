/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Address
public import Solanalib.Specs.Core.Float64

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.StakeState

/-! Stake account values and their fixed little-endian wire layout. The field
order follows the source declarations; it is the same for the Borsh and bincode
encodings of these types. This module states no decoder and no Rust theorem. -/

/-- `solana_clock::Epoch`, a `u64`. -/
abbrev Epoch := UInt64

/-- `solana_clock::UnixTimestamp`, an `i64`. -/
abbrev UnixTimestamp := Int64

/-- Withdrawal lockup of a stake account. -/
structure Lockup where
  /-- Unix timestamp before which withdrawal needs the custodian. -/
  unixTimestamp : UnixTimestamp
  /-- Epoch before which withdrawal needs the custodian. -/
  epoch : Epoch
  /-- The lockup custodian. -/
  custodian : _root_.Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- Staker and withdrawer authorities. -/
structure Authorized where
  /-- The stake authority. -/
  staker : _root_.Solanalib.Runtime.Pubkey
  /-- The withdraw authority. -/
  withdrawer : _root_.Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- Stake account metadata. -/
structure Meta where
  /-- The deprecated stored rent-exempt reserve. -/
  rentExemptReserve : UInt64
  /-- The authorities. -/
  authorized : Authorized
  /-- The lockup. -/
  lockup : Lockup
  deriving DecidableEq, Repr

/-- A delegation. The deprecated warmup/cooldown rate keeps its complete
binary64 bit pattern; no floating-point operation is applied to it. -/
structure Delegation where
  /-- The vote account receiving the delegation. -/
  voterPubkey : _root_.Solanalib.Runtime.Pubkey
  /-- The delegated amount. -/
  stake : UInt64
  /-- The activation epoch. -/
  activationEpoch : Epoch
  /-- The deactivation epoch. -/
  deactivationEpoch : Epoch
  /-- The deprecated `f64` warmup/cooldown rate as raw bits. -/
  warmupCooldownRate : Float64.Bits
  deriving DecidableEq, Repr

/-- A delegation with the credits observed at delegation or redemption. -/
structure Stake where
  /-- The delegation. -/
  delegation : Delegation
  /-- The observed vote credits. -/
  creditsObserved : UInt64
  deriving DecidableEq, Repr

/-- Stake flags with all eight stored bits, including reserved bits. -/
structure StakeFlags where
  /-- The private source field `bits`. -/
  bits : UInt8
  deriving DecidableEq, Repr

/-- `StakeStateV2`, with variants in source order. -/
inductive StakeStateV2 where
  | uninitialized
  | initialized (metadata : Meta)
  | stake (metadata : Meta) (stake : Stake) (flags : StakeFlags)
  | rewardsPool
  deriving DecidableEq, Repr

/-! ## Wire layout -/

def u32Bytes (value : UInt32) : _root_.Solanalib.Runtime.Bytes := _root_.Solanalib.Runtime.leBytes
  4 value.toNat
def u64Bytes (value : UInt64) : _root_.Solanalib.Runtime.Bytes := _root_.Solanalib.Runtime.leBytes
  8 value.toNat
/-- Binary radix complement little-endian bytes of an `i64`. -/
def i64Bytes (value : Int64) : _root_.Solanalib.Runtime.Bytes := u64Bytes value.toUInt64

def Lockup.encode (lockup : Lockup) : _root_.Solanalib.Runtime.Bytes :=
  i64Bytes lockup.unixTimestamp ++ u64Bytes lockup.epoch ++ lockup.custodian.bytes

def Authorized.encode (authorized : Authorized) : _root_.Solanalib.Runtime.Bytes :=
  authorized.staker.bytes ++ authorized.withdrawer.bytes

def Meta.encode (metadata : Meta) : _root_.Solanalib.Runtime.Bytes :=
  u64Bytes metadata.rentExemptReserve ++ metadata.authorized.encode ++ metadata.lockup.encode

def Delegation.encode (delegation : Delegation) : _root_.Solanalib.Runtime.Bytes :=
  delegation.voterPubkey.bytes ++ u64Bytes delegation.stake ++
    u64Bytes delegation.activationEpoch ++ u64Bytes delegation.deactivationEpoch ++
    u64Bytes delegation.warmupCooldownRate

def Stake.encode (stake : Stake) : _root_.Solanalib.Runtime.Bytes :=
  stake.delegation.encode ++ u64Bytes stake.creditsObserved

def StakeFlags.encode (flags : StakeFlags) : _root_.Solanalib.Runtime.Bytes := [flags.bits]

/-- The `u32` variant index written before the fields of each variant. -/
def StakeStateV2.tag : StakeStateV2 → UInt32
  | .uninitialized => 0
  | .initialized _ => 1
  | .stake _ _ _ => 2
  | .rewardsPool => 3

/-- The complete encoding: a four-byte little-endian tag, then the variant
fields. Shorter variants have no padding; account data is longer than this. -/
def StakeStateV2.encode : StakeStateV2 → _root_.Solanalib.Runtime.Bytes
  | .uninitialized => u32Bytes 0
  | .initialized metadata => u32Bytes 1 ++ metadata.encode
  | .stake metadata active flags => u32Bytes 2 ++ metadata.encode ++ active.encode ++ flags.encode
  | .rewardsPool => u32Bytes 3

/-- Borsh rejects a NaN `f64`, so only these values are decoded. -/
def Delegation.Portable (delegation : Delegation) : Prop :=
  Float64.decode delegation.warmupCooldownRate ≠ .nan

def StakeStateV2.Portable : StakeStateV2 → Prop
  | .stake _ active _ => active.delegation.Portable
  | _ => True

instance (delegation : Delegation) : Decidable delegation.Portable :=
  inferInstanceAs (Decidable (_ ≠ _))

instance (state : StakeStateV2) : Decidable state.Portable := by
  cases state <;> unfold StakeStateV2.Portable <;> infer_instance

/-! ## Layout widths -/

@[simp] theorem u32Bytes_length (value : UInt32) : (u32Bytes value).length = 4 := by
  simp [u32Bytes]

@[simp] theorem u64Bytes_length (value : UInt64) : (u64Bytes value).length = 8 := by
  simp [u64Bytes]

@[simp] theorem i64Bytes_length (value : Int64) : (i64Bytes value).length = 8 := by
  simp [i64Bytes]

@[simp] theorem Lockup.encode_length (lockup : Lockup) : lockup.encode.length = 48 := by
  simp [Lockup.encode, lockup.custodian.length_eq]

@[simp] theorem Authorized.encode_length (authorized : Authorized) :
    authorized.encode.length = 64 := by
  simp [Authorized.encode, authorized.staker.length_eq, authorized.withdrawer.length_eq]

@[simp] theorem Meta.encode_length (metadata : Meta) : metadata.encode.length = 120 := by
  simp [Meta.encode]

@[simp] theorem Delegation.encode_length (delegation : Delegation) :
    delegation.encode.length = 64 := by
  simp [Delegation.encode, delegation.voterPubkey.length_eq]

@[simp] theorem Stake.encode_length (stake : Stake) : stake.encode.length = 72 := by
  simp [Stake.encode]

@[simp] theorem StakeFlags.encode_length (flags : StakeFlags) : flags.encode.length = 1 := rfl

/-- The stake flags byte is at offset 196 of an encoded `Stake` variant. -/
theorem StakeStateV2.stake_encode_length (metadata : Meta) (stake : Stake) (flags : StakeFlags) :
    (StakeStateV2.stake metadata stake flags).encode.length = 197 := by
  simp [StakeStateV2.encode]

end Solanalib.Specs.Core.StakeState
