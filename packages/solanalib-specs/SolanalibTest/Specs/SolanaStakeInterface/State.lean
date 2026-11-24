/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaStakeInterface.State
public import Solanalib.Specs.Borsh.De

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

-- Concrete 200-byte decodings exceed the default elaboration depth of `rfl`.
set_option maxRecDepth 8192

namespace SolanalibTest.Specs.SolanaStakeInterface.State

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Borsh
open Solanalib.Specs.Core.StakeState
open Solanalib.Specs.SolanaStakeInterface.state

/-- Account data of an initialized stake account, copied from the upstream test
`borsh_deserialization_live_data` (state.rs:1685). -/
def liveData : Solanalib.Runtime.Bytes := [
  1, 0, 0, 0, 128, 213, 34, 0, 0, 0, 0, 0, 133, 0, 79, 231, 141, 29, 73, 61,
  232, 35, 119, 124, 168, 12, 120, 216, 195, 29, 12, 166, 139, 28, 36, 182, 186, 154, 246, 149,
  224, 109, 52, 100, 133, 0, 79, 231, 141, 29, 73, 61, 232, 35, 119, 124, 168, 12, 120, 216,
  195, 29, 12, 166, 139, 28, 36, 182, 186, 154, 246, 149, 224, 109, 52, 100] ++
  List.replicate 124 0

def rentReserve? : Except IoError StakeStateV2 → Option UInt64
  | .ok (.initialized metadata) => some metadata.rentExemptReserve
  | _ => none

/-- Upstream expects `Initialized` with reserve 2282880. The decoder consumes
124 bytes and leaves the 76 trailing bytes of the account. -/
theorem live_data_initialized :
    liveData.length = 200 ∧
    rentReserve? (StakeStateV2.decode liveData).1 = some 2282880 ∧
    (StakeStateV2.decode liveData).2 = List.replicate 76 0 := by
  refine ⟨rfl, rfl, rfl⟩

/-- Distinct nonpalindromic field values make field order and byte order observable. -/
def key (seed : Nat) : Solanalib.Runtime.Pubkey :=
  ⟨(List.range 32).map fun index => UInt8.ofNat (seed + index), by simp⟩

def sampleMeta : Meta where
  rentExemptReserve := 0x0102030405060708
  authorized := { staker := key 1, withdrawer := key 64 }
  lockup := { unixTimestamp := -2, epoch := 9, custodian := key 128 }

/-- Binary64 0.25, the source default rate. -/
def quarter : Float64.Bits := 0x3FD0000000000000

def sampleState (rate : Float64.Bits) (flags : UInt8) : StakeStateV2 :=
  .stake sampleMeta
    { delegation :=
        { voterPubkey := key 200, stake := 1000000000, activationEpoch := 5,
          deactivationEpoch := 0xFFFFFFFFFFFFFFFF, warmupCooldownRate := rate },
      creditsObserved := 77 }
    { bits := flags }

/-- A 200-byte stake account: the 197-byte encoding and three trailing bytes. -/
def sampleAccount (rate : Float64.Bits) (flags : UInt8) : Solanalib.Runtime.Bytes :=
  (sampleState rate flags).encode ++ [0, 0, 0]

theorem stake_account_decodes :
    (sampleAccount quarter 1).length = 200 ∧
    StakeStateV2.decode (sampleAccount quarter 1) = (.ok (sampleState quarter 1), [0, 0, 0]) :=
  ⟨rfl, rfl⟩

/-- The flag byte is at offset 196, as in the upstream `stake_flag_member_offset`. -/
theorem flag_offset : (sampleAccount quarter 1)[196]? = some 1 := rfl

/-- The tag and the reserve are little-endian. -/
theorem little_endian_prefix :
    (sampleAccount quarter 1).take 12 = [2, 0, 0, 0, 8, 7, 6, 5, 4, 3, 2, 1] := rfl

/-- Reserved flag bits are kept. -/
theorem reserved_flag_bits_kept :
    StakeStateV2.decode (sampleState quarter 0xFF).encode =
      (.ok (sampleState quarter 0xFF), []) := rfl

theorem invalid_tag_rejected :
    StakeStateV2.decode [4, 0, 0, 0, 9] = (.error invalidEnumError, [9]) := rfl

/-- A big-endian tag 1 is the little-endian tag 16777216, which is invalid. -/
theorem big_endian_tag_rejected :
    StakeStateV2.decode ([0, 0, 0, 1] ++ sampleMeta.encode) =
      (.error invalidEnumError, sampleMeta.encode) := rfl

theorem truncated_tag_rejected : StakeStateV2.decode [2, 0, 0] = (.error shortError, []) := rfl

/-- One missing flag byte: the truncation error empties the remaining slice. -/
theorem truncated_stake_rejected :
    StakeStateV2.decode ((sampleState quarter 1).encode.take 196) = (.error shortError, []) :=
  rfl

/-- A NaN rate is rejected after its eight bytes; the credits, the flag byte and
the trailing bytes remain. -/
theorem nan_rate_rejected :
    StakeStateV2.decode (sampleAccount Float64.quietNaN 1) =
      (.error nanError, u64Bytes 77 ++ [1, 0, 0, 0]) := rfl

/-- The NaN check precedes the truncated credits. -/
theorem nan_rate_before_truncation :
    StakeStateV2.decode ((sampleState Float64.quietNaN 1).encode.take 188) =
      (.error nanError, []) := rfl

/-- Only NaN is rejected: an infinite rate decodes. -/
theorem infinite_rate_accepted :
    StakeStateV2.decode (sampleState Float64.positiveInfinity 1).encode =
      (.ok (sampleState Float64.positiveInfinity 1), []) := rfl

theorem rewards_pool_reads_only_tag :
    StakeStateV2.decode [3, 0, 0, 0, 2, 0, 0, 0] = (.ok .rewardsPool, [2, 0, 0, 0]) := rfl

/-- The versioned contract holds on the live data at the reference outcome. -/
theorem contract_holds_on_live_data :
    StakeStateV2.deserialize_reader_contract.post () liveData
      (.returned (StakeStateV2.decode liveData) ()) :=
  StakeStateV2.deserialize_reader_reference () liveData _ trivial rfl

/-- The errors are plain `(kind, message)` data. -/
theorem error_values :
    invalidEnumError = ⟨⟨"InvalidData"⟩, "Invalid enum value"⟩ ∧
    shortError = ⟨⟨"InvalidData"⟩, "Unexpected length of input"⟩ ∧
    nanError = ⟨⟨"InvalidData"⟩,
      "For portability reasons we do not allow to deserialize NaNs."⟩ :=
  ⟨rfl, rfl, rfl⟩

/-- The contract rejects a fabricated success on an invalid tag. -/
theorem contract_rejects_fabricated_success :
    ¬ StakeStateV2.deserialize_reader_contract.post () [4, 0, 0, 0]
      (.returned (.ok .uninitialized, []) ()) := by
  rw [StakeStateV2.deserialize_reader_post_iff]
  rintro ⟨actual, hactual, hmatch⟩
  cases hactual
  have : StakeStateV2.decode [4, 0, 0, 0] = (.error invalidEnumError, []) := rfl
  rw [this] at hmatch
  cases hmatch

/-- The contract rejects a different error for a truncated input. -/
theorem contract_rejects_wrong_error :
    ¬ StakeStateV2.deserialize_reader_contract.post () [2, 0, 0]
      (.returned (.error nanError, []) ()) := by
  rw [StakeStateV2.deserialize_reader_post_iff]
  rintro ⟨actual, hactual, hmatch⟩
  cases hactual
  have : StakeStateV2.decode [2, 0, 0] = (.error shortError, []) := rfl
  rw [this] at hmatch
  have messages := congrArg (fun result : Except IoError StakeStateV2 => match result with
    | .error error => error.message
    | .ok _ => "") hmatch
  exact absurd messages (by decide)

/-- On success the contract fixes the remaining slice. -/
theorem contract_rejects_wrong_success_remainder :
    ¬ StakeStateV2.deserialize_reader_contract.post () [3, 0, 0, 0, 7]
      (.returned (.ok .rewardsPool, []) ()) := by
  rw [StakeStateV2.deserialize_reader_post_iff]
  rintro ⟨actual, hactual, hmatch⟩
  cases hactual
  have : StakeStateV2.decode [3, 0, 0, 0, 7] = (.ok .rewardsPool, [7]) := rfl
  rw [this] at hmatch
  cases hmatch

/-- After an error the contract leaves the remaining slice open: the `nostd_io` reader of borsh
keeps the bytes of a short read, which `std` empties. -/
theorem contract_allows_kept_remainder_after_error :
    StakeStateV2.deserialize_reader_contract.post () [2, 0, 0]
      (.returned (.error shortError, [2, 0, 0]) ()) :=
  ⟨rfl, .shortTag [2, 0, 0] [2, 0, 0] (by decide)⟩

/-- The borsh 1.6.1 default `deserialize` forwards the outcome of this decoder. -/
theorem borsh_deserialize_forwards :
    Solanalib.Specs.Borsh.de.BorshDeserialize.deserialize_run StakeStateV2.deserialize_reader_index
      ()
      liveData (.returned (StakeStateV2.decode liveData) ()) :=
  (deserializeRun_iff _ _ _ _).2 rfl

end SolanalibTest.Specs.SolanaStakeInterface.State
