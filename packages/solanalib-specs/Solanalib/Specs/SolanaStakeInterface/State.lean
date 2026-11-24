/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.StakeState
public import Solanalib.Specs.Borsh.De
public import Solanalib.Specs.SolanaAddress.Borsh

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! `StakeStateV2` Borsh decoding in solana-stake-interface 3.1.0 (`src/state.rs`,
`src/stake_flags.rs`) at `R = &[u8]`. The reference composes the borsh 1.6.1
primitive decoders and the solana-address 2.6.0 Address decoder; it follows the
`std` slice reader. The contract leaves the remaining slice after an error
unconstrained, as the borsh contracts do. -/

namespace Solanalib.Specs.SolanaStakeInterface.state

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Borsh
open Solanalib.Specs.Core.StakeState

/-! ## Callee models -/

/-- `<u8 as BorshDeserialize>::deserialize_reader` (borsh 1.6.1). -/
def u8 : Decoder UInt8 := fun input =>
  (Solanalib.Specs.Borsh.u8.invalid_data.deserialize_reader_model () input).1
/-- `<u32 as BorshDeserialize>::deserialize_reader` (borsh 1.6.1). -/
def u32 : Decoder UInt32 := fun input =>
  (Solanalib.Specs.Borsh.u32.invalid_data.deserialize_reader_model () input).1
/-- `<u64 as BorshDeserialize>::deserialize_reader` (borsh 1.6.1). -/
def u64 : Decoder UInt64 := fun input =>
  (Solanalib.Specs.Borsh.u64.invalid_data.deserialize_reader_model () input).1
/-- `<i64 as BorshDeserialize>::deserialize_reader` (borsh 1.6.1). -/
def i64 : Decoder Int64 := fun input =>
  (Solanalib.Specs.Borsh.i64.invalid_data.deserialize_reader_model () input).1
/-- `<f64 as BorshDeserialize>::deserialize_reader` (borsh 1.6.1), which rejects NaN. -/
def f64 : Decoder Float64.Bits :=
  fun input => (Solanalib.Specs.Borsh.f64.invalid_data.deserialize_reader_model () input).1

/-- `<solana_address::Address as BorshDeserialize>::deserialize_reader`, the
solana-address 2.6.0 model of the derived decoder of `Pubkey` fields. -/
def address : Decoder _root_.Solanalib.Runtime.Pubkey :=
  fun input => (Solanalib.Specs.SolanaAddress.Address.deserialize_reader_model () input).1

/-- the truncation error of Borsh, `InvalidData` "Unexpected length of input". -/
def shortError : IoError := Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength

/-- the `f64` NaN error of Borsh. -/
def nanError : IoError := Solanalib.Specs.Borsh.invalid_data_profile.deserializeNaN

def invalidEnumValueMessage : String := "Invalid enum value"

/-- `io::Error::new(io::ErrorKind::InvalidData, "Invalid enum value")`, built by
this crate (state.rs:189). -/
def invalidEnumError : IoError := ⟨.invalidData, invalidEnumValueMessage⟩

/-! ## Derived field decoders, in source field order -/

def Lockup.decode : Decoder Lockup :=
  i64.bind fun unixTimestamp => u64.bind fun epoch => address.bind fun custodian =>
    Decoder.pure { unixTimestamp, epoch, custodian }

def Authorized.decode : Decoder Authorized :=
  address.bind fun staker => address.bind fun withdrawer => Decoder.pure { staker, withdrawer }

def Meta.decode : Decoder Meta :=
  u64.bind fun rentExemptReserve => Authorized.decode.bind fun authorized =>
    Lockup.decode.bind fun lockup => Decoder.pure { rentExemptReserve, authorized, lockup }

def Delegation.decode : Decoder Delegation :=
  address.bind fun voterPubkey => u64.bind fun stake =>
    u64.bind fun activationEpoch => u64.bind fun deactivationEpoch =>
      f64.bind fun warmupCooldownRate =>
        Decoder.pure { voterPubkey, stake, activationEpoch, deactivationEpoch, warmupCooldownRate }

def Stake.decode : Decoder Stake :=
  Delegation.decode.bind fun delegation => u64.bind fun creditsObserved =>
    Decoder.pure { delegation, creditsObserved }

def StakeFlags.decode : Decoder StakeFlags := u8.bind fun bits => Decoder.pure { bits }

/-! ## The hand-written `StakeStateV2` decoder -/

/-- The branch selected by a decoded tag. -/
def StakeStateV2.branch (tag : UInt32) : Decoder Solanalib.Specs.Core.StakeState.StakeStateV2 :=
  if tag = 0 then Decoder.pure .uninitialized
  else if tag = 1 then Meta.decode.bind fun metadata => Decoder.pure (.initialized metadata)
  else if tag = 2 then
    Meta.decode.bind fun metadata => Stake.decode.bind fun active =>
      StakeFlags.decode.bind fun flags => Decoder.pure (.stake metadata active flags)
  else if tag = 3 then Decoder.pure .rewardsPool
  else fun remaining => (.error invalidEnumError, remaining)

/-- `impl_borsh_stake_state_v2` (state.rs:170-215): a `u32` tag, then the fields
of the variant. Another tag fails after the four tag bytes have been consumed. -/
def StakeStateV2.decode : Decoder Solanalib.Specs.Core.StakeState.StakeStateV2 :=
  u32.bind StakeStateV2.branch

/-! ## Declarative outcome -/

/-- The results of the decoder over the wire layout. A success consumes exactly
the encoding and fixes the remaining slice; after an error the remaining slice
is unconstrained. -/
inductive Decodes :
    _root_.Solanalib.Runtime.Bytes → Except IoError StakeStateV2 → _root_.Solanalib.Runtime.Bytes →
      Prop
  | ok (state : StakeStateV2) (remaining : _root_.Solanalib.Runtime.Bytes) : state.Portable →
      Decodes (state.encode ++ remaining) (.ok state) remaining
  | shortTag (bytes remaining : _root_.Solanalib.Runtime.Bytes) : bytes.length < 4 →
      Decodes bytes (.error shortError) remaining
  | invalidTag (tag : UInt32) (body remaining : _root_.Solanalib.Runtime.Bytes) : 3 < tag →
      Decodes (u32Bytes tag ++ body) (.error invalidEnumError) remaining
  | shortMeta (body remaining : _root_.Solanalib.Runtime.Bytes) : body.length < 120 →
      Decodes (u32Bytes 1 ++ body) (.error shortError) remaining
  | shortBeforeRate (body remaining : _root_.Solanalib.Runtime.Bytes) : body.length < 184 →
      Decodes (u32Bytes 2 ++ body) (.error shortError) remaining
  | nanRate (metadata : Meta) (delegation : Delegation) (tail remaining :
    _root_.Solanalib.Runtime.Bytes) :
      ¬ delegation.Portable →
      Decodes (u32Bytes 2 ++ metadata.encode ++ delegation.encode ++ tail)
        (.error nanError) remaining
  | shortAfterRate (metadata : Meta) (delegation : Delegation)
      (tail remaining : _root_.Solanalib.Runtime.Bytes) : delegation.Portable → tail.length < 9 →
      Decodes (u32Bytes 2 ++ metadata.encode ++ delegation.encode ++ tail)
        (.error shortError) remaining

/-! ## Fixed-width reads -/

theorem leBytes_leNat (bytes : _root_.Solanalib.Runtime.Bytes) :
    _root_.Solanalib.Runtime.leBytes bytes.length (_root_.Solanalib.Runtime.leNat bytes) = bytes :=
      by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    have hb : byte.toNat < 256 := byte.toNat_lt
    have hmod : (byte.toNat + 256 * _root_.Solanalib.Runtime.leNat bytes) % 256 = byte.toNat := by
      omega
    have hdiv : (byte.toNat + 256 * _root_.Solanalib.Runtime.leNat bytes) / 256 =
        _root_.Solanalib.Runtime.leNat bytes := by omega
    simp only [List.length_cons, _root_.Solanalib.Runtime.leBytes, _root_.Solanalib.Runtime.leNat,
      hmod, hdiv, ih,
      UInt8.ofNat_toNat]

/-- A decoder of a fixed-width value: it reads exactly the encoding, every
byte string of that width is an encoding, and a shorter input fails with the
truncation error and, under the `std` reader, an empty remaining slice. -/
structure Exact {Value : Type} (decode : Decoder Value) (width : Nat)
    (encode : Value → _root_.Solanalib.Runtime.Bytes) : Prop where
  length : ∀ value, (encode value).length = width
  decode_encode : ∀ value rest, decode (encode value ++ rest) = (.ok value, rest)
  onto : ∀ bytes : _root_.Solanalib.Runtime.Bytes, bytes.length = width → ∃ value, encode value =
    bytes
  short : ∀ bytes : _root_.Solanalib.Runtime.Bytes, bytes.length < width →
    decode bytes = (.error shortError, [])

theorem Exact.split {Value : Type} {decode : Decoder Value} {width : Nat}
    {encode : Value → _root_.Solanalib.Runtime.Bytes} (exact : Exact decode width encode)
    (bytes : _root_.Solanalib.Runtime.Bytes) (enough : width ≤ bytes.length) :
    ∃ value rest, bytes = encode value ++ rest ∧ rest.length = bytes.length - width := by
  obtain ⟨value, hvalue⟩ := exact.onto (bytes.take width) (by simp; omega)
  exact ⟨value, bytes.drop width, by rw [hvalue, List.take_append_drop], by simp⟩

theorem Exact.map {Value Next : Type} {decode : Decoder Value} {width : Nat}
    {encode : Value → _root_.Solanalib.Runtime.Bytes} (exact : Exact decode width encode)
    (forward : Value → Next) (backward : Next → Value)
    (forward_backward : ∀ next, forward (backward next) = next)
    (backward_forward : ∀ value, backward (forward value) = value) :
    Exact (decode.map forward) width (fun next => encode (backward next)) where
  length := fun next => exact.length (backward next)
  decode_encode := by
    intro next rest
    simp only [Decoder.map, exact.decode_encode, Except.map, forward_backward]
  onto := by
    intro bytes hbytes
    obtain ⟨value, rfl⟩ := exact.onto bytes hbytes
    exact ⟨forward value, by rw [backward_forward]⟩
  short := by
    intro bytes hbytes
    simp only [Decoder.map, exact.short bytes hbytes, Except.map]

theorem takeExact_map_exact {Value : Type} {width : Nat} {parse : _root_.Solanalib.Runtime.Bytes →
  Value}
    {encode : Value → _root_.Solanalib.Runtime.Bytes} (length : ∀ value, (encode value).length =
      width)
    (parse_encode : ∀ value, parse (encode value) = value)
    (encode_parse : ∀ bytes : _root_.Solanalib.Runtime.Bytes, bytes.length = width →
      encode (parse bytes) = bytes) :
    Exact ((takeExact Solanalib.Specs.Borsh.invalid_data_profile width).map parse) width encode
      where
  length := length
  decode_encode := by
    intro value rest
    have hlen := length value
    have enough : width ≤ (encode value ++ rest).length := by simp [hlen]
    simp only [Decoder.map, takeExact, enough, ite_true, Except.map]
    rw [← hlen, List.take_left, List.drop_left, parse_encode]
  onto := fun bytes hbytes => ⟨parse bytes, encode_parse bytes hbytes⟩
  short := by
    intro bytes hbytes
    simp [Decoder.map, takeExact, Nat.not_le.mpr hbytes, Except.map, shortError]

theorem bind_ok {Value Next : Type} {first : Decoder Value} {next : Value → Decoder Next}
    {bytes rest : _root_.Solanalib.Runtime.Bytes} {value : Value}
    (step : first bytes = (.ok value, rest)) : first.bind next bytes = next value rest := by
  simp [Decoder.bind, step]

theorem bind_error {Value Next : Type} {first : Decoder Value} {next : Value → Decoder Next}
    {bytes rest : _root_.Solanalib.Runtime.Bytes} {error : IoError}
    (step : first bytes = (.error error, rest)) :
    first.bind next bytes = (.error error, rest) := by
  simp [Decoder.bind, step]

/-- A truncated composite read fails as soon as one component is short. -/
theorem bind_short {Value Next : Type} {first : Decoder Value} {width : Nat}
    {encode : Value → _root_.Solanalib.Runtime.Bytes} (exact : Exact first width encode)
    {next : Value → Decoder Next} {width' : Nat}
    (shortNext : ∀ value (rest : _root_.Solanalib.Runtime.Bytes), rest.length < width' →
      next value rest = (.error shortError, []))
    (bytes : _root_.Solanalib.Runtime.Bytes) (short : bytes.length < width + width') :
    first.bind next bytes = (.error shortError, []) := by
  by_cases hwidth : bytes.length < width
  · exact bind_error (exact.short bytes hwidth)
  · obtain ⟨value, rest, rfl, hrest⟩ := exact.split bytes (by omega)
    rw [bind_ok (exact.decode_encode value rest)]
    exact shortNext value rest (by omega)

theorem pure_short {Value : Type} (value : Value) (rest : _root_.Solanalib.Runtime.Bytes)
    (short : rest.length < 0) : Decoder.pure value rest = (.error shortError, []) :=
  absurd short (Nat.not_lt_zero _)

/-! ## Callee decoders -/

theorem u8_exact : Exact u8 1 fun byte => [byte] :=
  takeExact_map_exact (fun _ => rfl)
    (fun byte => by simp [_root_.Solanalib.Runtime.leNat])
    (by
      intro bytes hbytes
      match bytes, hbytes with
      | [_], _ => simp [_root_.Solanalib.Runtime.leNat])

theorem u32_exact : Exact u32 4 u32Bytes :=
  takeExact_map_exact u32Bytes_length
    (by
      intro value
      simp only [u32Bytes]
      rw [_root_.Solanalib.Runtime.leNat_leBytes_of_lt (by have := value.toNat_lt; omega)]
      exact UInt32.ofNat_toNat)
    (by
      intro bytes hbytes
      have bound := _root_.Solanalib.Runtime.leNat_lt bytes
      rw [hbytes] at bound
      simp only [u32Bytes, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : _ < 2 ^ 32)]
      rw [← hbytes, leBytes_leNat])

theorem u64_parse_encode (value : UInt64) :
    UInt64.ofNat (_root_.Solanalib.Runtime.leNat (u64Bytes value)) = value := by
  simp only [u64Bytes]
  rw [_root_.Solanalib.Runtime.leNat_leBytes_of_lt (by have := value.toNat_lt; omega)]
  exact UInt64.ofNat_toNat

theorem u64_exact : Exact u64 8 u64Bytes :=
  takeExact_map_exact u64Bytes_length u64_parse_encode
    (by
      intro bytes hbytes
      have bound := _root_.Solanalib.Runtime.leNat_lt bytes
      rw [hbytes] at bound
      simp only [u64Bytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)]
      rw [← hbytes, leBytes_leNat])

theorem i64_exact : Exact i64 8 i64Bytes :=
  u64_exact.map UInt64.toInt64 Int64.toUInt64 Int64.toInt64_toUInt64 UInt64.toUInt64_toInt64

theorem address_exact : Exact address 32 _root_.Solanalib.Runtime.Pubkey.bytes where
  length := _root_.Solanalib.Runtime.Pubkey.length_eq
  decode_encode := by
    intro key rest
    obtain ⟨keyBytes, hkey⟩ := key
    have long : 32 ≤ (keyBytes ++ rest).length := by simp [hkey]
    have htake : (keyBytes ++ rest).take 32 = keyBytes := by rw [← hkey, List.take_left]
    have hdrop : (keyBytes ++ rest).drop 32 = rest := by rw [← hkey, List.drop_left]
    show Solanalib.Specs.SolanaAddress.Address.decoder (keyBytes ++ rest) = _
    rw [Solanalib.Specs.SolanaAddress.Address.decoder_ok long]
    simp only [htake, hdrop]
  onto := fun bytes hbytes => ⟨⟨bytes, hbytes⟩, rfl⟩
  short := fun _ hbytes => Solanalib.Specs.SolanaAddress.Address.decoder_short hbytes

theorem isNaN_iff (bits : Float64.Bits) : isNaN bits = true ↔ Float64.decode bits = .nan := by
  unfold isNaN
  cases Float64.decode bits <;> simp

theorem f64_encode (bits : Float64.Bits) (rest : _root_.Solanalib.Runtime.Bytes) :
    f64 (u64Bytes bits ++ rest) =
      (if Float64.decode bits = .nan then .error nanError else .ok bits, rest) := by
  have step := u64_exact.decode_encode bits rest
  simp only [u64, Solanalib.Specs.Borsh.u64.invalid_data.deserialize_reader_model, decoderModel]
    at step
  simp only [f64, Solanalib.Specs.Borsh.f64.invalid_data.deserialize_reader_model, decoderModel,
    decodeF64, step]
  by_cases hnan : Float64.decode bits = .nan
  · rw [ite_eq_left ((isNaN_iff bits).mpr hnan), ite_eq_left hnan]
    rfl
  · rw [ite_eq_right (fun h => hnan ((isNaN_iff bits).mp h)), ite_eq_right hnan]

theorem f64_short (bytes : _root_.Solanalib.Runtime.Bytes) (short : bytes.length < 8) :
    f64 bytes = (.error shortError, []) := by
  have step := u64_exact.short bytes short
  simp only [u64, Solanalib.Specs.Borsh.u64.invalid_data.deserialize_reader_model, decoderModel]
    at step
  simp only [f64, Solanalib.Specs.Borsh.f64.invalid_data.deserialize_reader_model, decoderModel,
    decodeF64, step]

/-! ## Field decoders -/

theorem Lockup.exact : Exact Lockup.decode 48 Lockup.encode where
  length := Lockup.encode_length
  decode_encode := by
    intro value rest
    simp only [Lockup.decode, Lockup.encode, List.append_assoc]
    rw [bind_ok (i64_exact.decode_encode _ _), bind_ok (u64_exact.decode_encode _ _),
      bind_ok (address_exact.decode_encode _ _)]
    rfl
  onto := by
    intro bytes hbytes
    obtain ⟨unixTimestamp, rest, rfl, hrest⟩ := i64_exact.split bytes (by omega)
    obtain ⟨epoch, custodian, rfl, hcustodian⟩ := u64_exact.split rest (by omega)
    obtain ⟨custodian, rfl⟩ := address_exact.onto custodian (by omega)
    exact ⟨{ unixTimestamp, epoch, custodian }, by simp [Lockup.encode]⟩
  short := by
    intro bytes hbytes
    exact bind_short (width' := 40) i64_exact (fun _ rest hrest =>
      bind_short (width' := 32) u64_exact (fun _ rest hrest =>
        bind_short (width' := 0) address_exact (fun _ rest hrest =>
          pure_short _ rest hrest) rest (by omega)) rest (by omega)) bytes (by omega)

theorem Authorized.exact : Exact Authorized.decode 64 Authorized.encode where
  length := Authorized.encode_length
  decode_encode := by
    intro value rest
    simp only [Authorized.decode, Authorized.encode, List.append_assoc]
    rw [bind_ok (address_exact.decode_encode _ _), bind_ok (address_exact.decode_encode _ _)]
    rfl
  onto := by
    intro bytes hbytes
    obtain ⟨staker, rest, rfl, hrest⟩ := address_exact.split bytes (by omega)
    obtain ⟨withdrawer, rfl⟩ := address_exact.onto rest (by omega)
    exact ⟨{ staker, withdrawer }, rfl⟩
  short := by
    intro bytes hbytes
    exact bind_short (width' := 32) address_exact (fun _ rest hrest =>
      bind_short (width' := 0) address_exact (fun _ rest hrest =>
        pure_short _ rest hrest) rest (by omega)) bytes (by omega)

theorem Meta.exact : Exact Meta.decode 120 Meta.encode where
  length := Meta.encode_length
  decode_encode := by
    intro value rest
    simp only [Meta.decode, Meta.encode, List.append_assoc]
    rw [bind_ok (u64_exact.decode_encode _ _), bind_ok (Authorized.exact.decode_encode _ _),
      bind_ok (Lockup.exact.decode_encode _ _)]
    rfl
  onto := by
    intro bytes hbytes
    obtain ⟨rentExemptReserve, rest, rfl, hrest⟩ := u64_exact.split bytes (by omega)
    obtain ⟨authorized, lockupBytes, rfl, hlockup⟩ := Authorized.exact.split rest (by omega)
    obtain ⟨lockup, rfl⟩ := Lockup.exact.onto lockupBytes (by omega)
    exact ⟨{ rentExemptReserve, authorized, lockup }, by simp [Meta.encode]⟩
  short := by
    intro bytes hbytes
    exact bind_short (width' := 112) u64_exact (fun _ rest hrest =>
      bind_short (width' := 48) Authorized.exact (fun _ rest hrest =>
        bind_short (width' := 0) Lockup.exact (fun _ rest hrest =>
          pure_short _ rest hrest) rest (by omega)) rest (by omega)) bytes (by omega)

theorem StakeFlags.exact : Exact StakeFlags.decode 1 StakeFlags.encode where
  length := StakeFlags.encode_length
  decode_encode := by
    intro value rest
    simp only [StakeFlags.decode, StakeFlags.encode]
    rw [bind_ok (u8_exact.decode_encode _ _)]
    rfl
  onto := by
    intro bytes hbytes
    obtain ⟨bits, rfl⟩ := u8_exact.onto bytes hbytes
    exact ⟨{ bits }, rfl⟩
  short := by
    intro bytes hbytes
    exact bind_short (width' := 0) u8_exact (fun _ rest hrest =>
      pure_short _ rest hrest) bytes (by omega)

theorem Delegation.decode_encode (delegation : Delegation) (rest : _root_.Solanalib.Runtime.Bytes) :
    Delegation.decode (delegation.encode ++ rest) =
      (if delegation.Portable then .ok delegation else .error nanError, rest) := by
  simp only [Delegation.decode, Delegation.encode, List.append_assoc]
  rw [bind_ok (address_exact.decode_encode _ _), bind_ok (u64_exact.decode_encode _ _),
    bind_ok (u64_exact.decode_encode _ _), bind_ok (u64_exact.decode_encode _ _)]
  have hrate := f64_encode delegation.warmupCooldownRate rest
  by_cases hnan : Float64.decode delegation.warmupCooldownRate = .nan
  · rw [ite_eq_left hnan] at hrate
    rw [bind_error hrate, ite_eq_right (by simp [Delegation.Portable, hnan])]
  · rw [ite_eq_right hnan] at hrate
    rw [bind_ok hrate, ite_eq_left (show delegation.Portable from hnan)]
    rfl

theorem Delegation.onto (bytes : _root_.Solanalib.Runtime.Bytes) (hbytes : bytes.length = 64) :
    ∃ delegation : Delegation, delegation.encode = bytes := by
  obtain ⟨voterPubkey, rest1, rfl, h1⟩ := address_exact.split bytes (by omega)
  obtain ⟨stake, rest2, rfl, h2⟩ := u64_exact.split rest1 (by omega)
  obtain ⟨activationEpoch, rest3, rfl, h3⟩ := u64_exact.split rest2 (by omega)
  obtain ⟨deactivationEpoch, rest4, rfl, h4⟩ := u64_exact.split rest3 (by omega)
  obtain ⟨warmupCooldownRate, rfl⟩ := u64_exact.onto rest4 (by omega)
  exact ⟨{ voterPubkey, stake, activationEpoch, deactivationEpoch, warmupCooldownRate },
    by simp [Delegation.encode]⟩

theorem Delegation.short (bytes : _root_.Solanalib.Runtime.Bytes) (hbytes : bytes.length < 64) :
    Delegation.decode bytes = (.error shortError, []) :=
  bind_short (width' := 32) address_exact (fun _ rest hrest =>
    bind_short (width' := 24) u64_exact (fun _ rest hrest =>
      bind_short (width' := 16) u64_exact (fun _ rest hrest =>
        bind_short (width' := 8) u64_exact (fun _ rest hrest =>
          bind_error (f64_short rest hrest)) rest (by omega)) rest (by omega))
      rest (by omega)) bytes (by omega)

theorem Stake.decode_nan (delegation : Delegation) (tail : _root_.Solanalib.Runtime.Bytes)
    (nan : ¬ delegation.Portable) :
    Stake.decode (delegation.encode ++ tail) = (.error nanError, tail) := by
  have := Delegation.decode_encode delegation tail
  rw [ite_eq_right nan] at this
  exact bind_error this

theorem Stake.decode_portable (delegation : Delegation) (tail : _root_.Solanalib.Runtime.Bytes)
    (portable : delegation.Portable) :
    Stake.decode (delegation.encode ++ tail) =
      u64.bind (fun creditsObserved => Decoder.pure { delegation, creditsObserved }) tail := by
  have := Delegation.decode_encode delegation tail
  rw [ite_eq_left portable] at this
  exact bind_ok this

theorem Stake.short (bytes : _root_.Solanalib.Runtime.Bytes) (hbytes : bytes.length < 64) :
    Stake.decode bytes = (.error shortError, []) :=
  bind_error (Delegation.short bytes hbytes)

/-! ## The `StakeStateV2` decoder -/

theorem StakeStateV2.decode_tag (tag : UInt32) (body : _root_.Solanalib.Runtime.Bytes) :
    StakeStateV2.decode (u32Bytes tag ++ body) = branch tag body :=
  bind_ok (u32_exact.decode_encode tag body)

theorem StakeStateV2.branch_stake (body : _root_.Solanalib.Runtime.Bytes) :
    branch 2 body = (Meta.decode.bind fun metadata => Stake.decode.bind fun active =>
      StakeFlags.decode.bind fun flags => Decoder.pure (.stake metadata active flags)) body := by
  simp only [branch, ite_eq_right (by decide : (2 : UInt32) ≠ 0),
    ite_eq_right (by decide : (2 : UInt32) ≠ 1), ite_true]

theorem StakeStateV2.decode_encode (state : Solanalib.Specs.Core.StakeState.StakeStateV2)
    (rest : _root_.Solanalib.Runtime.Bytes) (portable : state.Portable) :
    StakeStateV2.decode (state.encode ++ rest) = (.ok state, rest) := by
  cases state with
  | uninitialized =>
    rw [Solanalib.Specs.Core.StakeState.StakeStateV2.encode, decode_tag]
    rfl
  | initialized metadata =>
    rw [Solanalib.Specs.Core.StakeState.StakeStateV2.encode, List.append_assoc, decode_tag]
    simp only [branch, ite_eq_right (by decide : (1 : UInt32) ≠ 0), ite_true]
    rw [bind_ok (Meta.exact.decode_encode _ _)]
    rfl
  | stake metadata active flags =>
    simp only [Solanalib.Specs.Core.StakeState.StakeStateV2.encode, Stake.encode,
      List.append_assoc, decode_tag, branch_stake]
    rw [bind_ok (Meta.exact.decode_encode _ _)]
    rw [bind_ok (by rw [Stake.decode_portable _ _ portable,
      bind_ok (u64_exact.decode_encode _ _)]; rfl)]
    rw [bind_ok (StakeFlags.exact.decode_encode _ _)]
    rfl
  | rewardsPool =>
    rw [Solanalib.Specs.Core.StakeState.StakeStateV2.encode, decode_tag]
    rfl

/-! ## Exactness of the declarative outcome -/

theorem tag_ne_small {tag : UInt32} (large : 3 < tag) :
    tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2 ∧ tag ≠ 3 := by
  rw [UInt32.lt_iff_toNat_lt] at large
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> subst h <;> simp at large

theorem tag_gt_of_ne_small {tag : UInt32} (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2)
    (h3 : tag ≠ 3) : 3 < tag := by
  rw [UInt32.lt_iff_toNat_lt]
  have n0 : tag.toNat ≠ 0 := fun h => h0 (UInt32.toNat_inj.mp h)
  have n1 : tag.toNat ≠ 1 := fun h => h1 (UInt32.toNat_inj.mp h)
  have n2 : tag.toNat ≠ 2 := fun h => h2 (UInt32.toNat_inj.mp h)
  have n3 : tag.toNat ≠ 3 := fun h => h3 (UInt32.toNat_inj.mp h)
  simp only [UInt32.reduceToNat]
  omega

/-- The reference outcome of each declarative case, with the `std` remainder. -/
theorem Decodes.reference {bytes remaining : _root_.Solanalib.Runtime.Bytes}
    {result : Except IoError Solanalib.Specs.Core.StakeState.StakeStateV2}
    (decodes : Decodes bytes result remaining) :
    ∃ actual, StakeStateV2.decode bytes = (result, actual) ∧
      (result.toOption.isSome → actual = remaining) := by
  cases decodes with
  | ok state remaining portable =>
    exact ⟨remaining, StakeStateV2.decode_encode state remaining portable, fun _ => rfl⟩
  | shortTag bytes remaining short =>
    exact ⟨[], bind_error (u32_exact.short bytes short), nofun⟩
  | invalidTag tag body remaining large =>
    obtain ⟨h0, h1, h2, h3⟩ := tag_ne_small large
    refine ⟨body, ?_, nofun⟩
    rw [StakeStateV2.decode_tag]
    simp only [StakeStateV2.branch, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2,
      ite_eq_right h3]
  | shortMeta body remaining short =>
    refine ⟨[], ?_, nofun⟩
    rw [StakeStateV2.decode_tag]
    simp only [StakeStateV2.branch, ite_eq_right (by decide : (1 : UInt32) ≠ 0), ite_true]
    exact bind_error (Meta.exact.short body short)
  | shortBeforeRate body remaining short =>
    refine ⟨[], ?_, nofun⟩
    rw [StakeStateV2.decode_tag, StakeStateV2.branch_stake]
    exact bind_short (width' := 64) Meta.exact (fun _ rest hrest =>
      bind_error (Stake.short rest hrest)) body (by omega)
  | nanRate metadata delegation tail remaining nan =>
    refine ⟨tail, ?_, nofun⟩
    simp only [List.append_assoc, StakeStateV2.decode_tag, StakeStateV2.branch_stake]
    rw [bind_ok (Meta.exact.decode_encode _ _)]
    exact bind_error (Stake.decode_nan delegation tail nan)
  | shortAfterRate metadata delegation tail remaining portable short =>
    refine ⟨[], ?_, nofun⟩
    simp only [List.append_assoc, StakeStateV2.decode_tag, StakeStateV2.branch_stake]
    rw [bind_ok (Meta.exact.decode_encode _ _)]
    by_cases credits : tail.length < 8
    · have hstake : Stake.decode (delegation.encode ++ tail) = (.error shortError, []) := by
        rw [Stake.decode_portable _ _ portable]
        exact bind_error (u64_exact.short tail credits)
      exact bind_error hstake
    · obtain ⟨creditsObserved, flags, rfl, hflags⟩ := u64_exact.split tail (by omega)
      have hstake : Stake.decode (delegation.encode ++ (u64Bytes creditsObserved ++ flags)) =
          (.ok { delegation, creditsObserved }, flags) := by
        rw [Stake.decode_portable _ _ portable, bind_ok (u64_exact.decode_encode _ _)]
        rfl
      rw [bind_ok hstake]
      rw [List.length_append, u64Bytes_length] at short
      exact bind_error (StakeFlags.exact.short flags (by omega))

/-- An error case holds with every remaining slice. -/
theorem Decodes.any_remaining {bytes remaining : _root_.Solanalib.Runtime.Bytes} {error : IoError}
    (decodes : Decodes bytes (.error error) remaining) (other : _root_.Solanalib.Runtime.Bytes) :
    Decodes bytes (.error error) other := by
  generalize hresult : (Except.error error : Except IoError StakeStateV2) = result at decodes
  cases decodes with
  | ok => cases hresult
  | shortTag bytes _ short => cases hresult; exact .shortTag bytes other short
  | invalidTag tag body _ large => cases hresult; exact .invalidTag tag body other large
  | shortMeta body _ short => cases hresult; exact .shortMeta body other short
  | shortBeforeRate body _ short => cases hresult; exact .shortBeforeRate body other short
  | nanRate metadata delegation tail _ nan =>
    cases hresult; exact .nanRate metadata delegation tail other nan
  | shortAfterRate metadata delegation tail _ portable short =>
    cases hresult; exact .shortAfterRate metadata delegation tail other portable short

/-- Every input has a declarative case. -/
theorem Decodes.exists (bytes : _root_.Solanalib.Runtime.Bytes) :
    ∃ result remaining, Decodes bytes result remaining := by
  by_cases h4 : bytes.length < 4
  · exact ⟨_, _, .shortTag bytes [] h4⟩
  obtain ⟨tag, body, rfl, -⟩ := u32_exact.split bytes (by omega)
  by_cases t0 : tag = 0
  · subst t0
    exact ⟨_, _, Decodes.ok .uninitialized body trivial⟩
  by_cases t1 : tag = 1
  · subst t1
    by_cases short : body.length < 120
    · exact ⟨_, _, .shortMeta body [] short⟩
    obtain ⟨metadata, rest, rfl, -⟩ := Meta.exact.split body (by omega)
    rw [← List.append_assoc]
    exact ⟨_, _, Decodes.ok (.initialized metadata) rest trivial⟩
  by_cases t2 : tag = 2
  · subst t2
    by_cases short : body.length < 184
    · exact ⟨_, _, .shortBeforeRate body [] short⟩
    obtain ⟨metadata, rest, rfl, hrest⟩ := Meta.exact.split body (by omega)
    rw [List.length_append, Meta.encode_length] at short
    obtain ⟨delegation, hdelegation⟩ := Delegation.onto (rest.take 64) (by simp; omega)
    have hsplit : rest = delegation.encode ++ rest.drop 64 := by
      rw [hdelegation, List.take_append_drop]
    rw [hsplit]
    generalize rest.drop 64 = tail
    by_cases portable : delegation.Portable
    · by_cases short : tail.length < 9
      · have := Decodes.shortAfterRate metadata delegation tail [] portable short
        simp only [List.append_assoc] at this
        exact ⟨_, _, this⟩
      obtain ⟨creditsObserved, flagBytes, rfl, -⟩ := u64_exact.split tail (by omega)
      obtain ⟨flags, remaining, rfl, -⟩ :=
        StakeFlags.exact.split flagBytes (by simp at short; omega)
      have := Decodes.ok (.stake metadata { delegation, creditsObserved } flags) remaining
        portable
      simp only [Solanalib.Specs.Core.StakeState.StakeStateV2.encode, Stake.encode,
        List.append_assoc] at this
      exact ⟨_, _, this⟩
    · have := Decodes.nanRate metadata delegation tail [] portable
      simp only [List.append_assoc] at this
      exact ⟨_, _, this⟩
  by_cases t3 : tag = 3
  · subst t3
    exact ⟨_, _, Decodes.ok .rewardsPool body trivial⟩
  exact ⟨_, _, .invalidTag tag body [] (tag_gt_of_ne_small t0 t1 t2 t3)⟩

/-- The reference result always satisfies the declarative outcome. -/
theorem StakeStateV2.decode_sound (bytes : _root_.Solanalib.Runtime.Bytes) :
    Decodes bytes (StakeStateV2.decode bytes).1 (StakeStateV2.decode bytes).2 := by
  obtain ⟨result, remaining, decodes⟩ := Decodes.exists bytes
  obtain ⟨actual, hdecode, hsuccess⟩ := decodes.reference
  rw [hdecode]
  cases result with
  | ok state =>
    rw [hsuccess rfl]
    exact decodes
  | error error => exact decodes.any_remaining actual

/-- The declarative outcome is exactly the Borsh agreement with the reference:
the same result, and on success the same remaining slice. -/
theorem decodes_iff (bytes remaining : _root_.Solanalib.Runtime.Bytes)
    (result : Except IoError Solanalib.Specs.Core.StakeState.StakeStateV2) :
    Decodes bytes result remaining ↔
      DecodeMatches (StakeStateV2.decode bytes) (result, remaining) := by
  constructor
  · intro decodes
    obtain ⟨actual, hdecode, hsuccess⟩ := decodes.reference
    rw [hdecode]
    cases result with
    | ok state => rw [hsuccess rfl]; rfl
    | error error => rfl
  · intro hmatch
    have sound := StakeStateV2.decode_sound bytes
    revert hmatch sound
    rcases StakeStateV2.decode bytes with ⟨_ | expected, actual⟩
    · intro hmatch sound
      simp only [DecodeMatches] at hmatch
      subst hmatch
      exact sound.any_remaining remaining
    · intro hmatch sound
      simp only [DecodeMatches, Prod.mk.injEq] at hmatch
      obtain ⟨rfl, rfl⟩ := hmatch
      exact sound

/-! ## Model -/

namespace StakeStateV2

/-- `<StakeStateV2 as BorshDeserialize>::deserialize_reader` at `R = &[u8]`.
The ambient state is unchanged; the result carries the remaining slice. -/
def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit _root_.Solanalib.Runtime.Bytes
      (Except IoError Solanalib.Specs.Core.StakeState.StakeStateV2 ×
        _root_.Solanalib.Runtime.Bytes) where
  requires := fun _ _ => True
  post := fun before bytes outcome => match outcome with
    | .returned (result, remaining) after => after = before ∧ Decodes bytes result remaining
    | .unwound _ _ | .terminated _ => False

/-- The executable reference, registered as the graph of the decoder function. -/
def deserialize_reader_run :
    Decode Unit Solanalib.Specs.Core.StakeState.StakeStateV2 Empty Empty :=
  Callback.ofFunction (Decoder.lift decode)

theorem deserialize_reader_reference :
    deserialize_reader_contract.Holds deserialize_reader_run := by
  intro before bytes outcome _ execution
  subst execution
  exact ⟨rfl, decode_sound bytes⟩

theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  ⟨(), [], trivial⟩

/-- A permitted execution: the `RewardsPool` tag followed by one trailing byte. -/
theorem deserialize_reader_has_execution :
    deserialize_reader_contract.HasExecution deserialize_reader_run :=
  ⟨(), [3, 0, 0, 0, 7], .returned (.ok .rewardsPool, [7]) (), trivial, rfl⟩

/-- The contract admits exactly the outcomes that agree with the reference. -/
theorem deserialize_reader_post_iff (before : Unit) (bytes : _root_.Solanalib.Runtime.Bytes)
    (outcome : Outcome Unit
      (Except IoError Solanalib.Specs.Core.StakeState.StakeStateV2 × _root_.Solanalib.Runtime.Bytes)
      Empty Empty) :
    deserialize_reader_contract.post before bytes outcome ↔
      DecodeOutcomeMatches (.returned (decode bytes) before) outcome := by
  cases outcome with
  | returned actual after =>
    rcases actual with ⟨result, remaining⟩
    constructor
    · rintro ⟨rfl, decodes⟩
      exact ⟨(result, remaining), rfl, (decodes_iff bytes remaining result).mp decodes⟩
    · rintro ⟨_, hactual, hmatch⟩
      cases hactual
      exact ⟨rfl, (decodes_iff bytes remaining result).mpr hmatch⟩
  | unwound reason _ => exact nomatch reason
  | terminated reason => exact nomatch reason

/-- The callback index of this decoder for the borsh `deserialize` and Solana
Borsh `try_from_slice_unchecked` families. -/
def deserialize_reader_index : DecodeIndex :=
  ⟨Unit, Empty, Empty, Solanalib.Specs.Core.StakeState.StakeStateV2, deserialize_reader_run⟩

end StakeStateV2

end Solanalib.Specs.SolanaStakeInterface.state
