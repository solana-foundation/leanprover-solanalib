/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Ids
public import Solanalib.Runtime.Profile

@[expose] public section

/-!
# Sysvars

The sysvar values of a bank, with two encodings: the `repr(C)` layout that the typed
getters write (`CloneZeroed`, including zeroed padding), and the bincode layout of
the account data that `sol_get_sysvar` serves. The current SDK versions and the
additional width and cache-coherence premises are recorded in
[syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives).
-/

namespace Solanalib.Runtime

/-- The binary radix-complement little-endian encoding of an `i64`. -/
def i64le (x : Int) : Bytes :=
  leBytes 8 (if 0 ≤ x then x.toNat else (2 ^ 64 - (-x).toNat))

/-- `Clock` from solana-clock 3.2.0: 40 bytes in both encodings when its values
fit their runtime `u64` and `i64` fields. -/
structure Clock where
  slot : Nat
  epochStartTimestamp : Int
  epoch : Nat
  leaderScheduleEpoch : Nat
  unixTimestamp : Int
  deriving DecidableEq, Repr

def Clock.encode (c : Clock) : Bytes :=
  u64le c.slot ++ i64le c.epochStartTimestamp ++ u64le c.epoch ++ u64le c.leaderScheduleEpoch ++
    i64le c.unixTimestamp

/-- `EpochSchedule` from solana-epoch-schedule 3.3.0. -/
structure EpochSchedule where
  slotsPerEpoch : Nat
  leaderScheduleSlotOffset : Nat
  warmup : Bool
  firstNormalEpoch : Nat
  firstNormalSlot : Nat
  deriving DecidableEq, Repr

/-- The `repr(C)` layout: 40 bytes, with 7 zero bytes after `warmup`. -/
def EpochSchedule.reprC (e : EpochSchedule) : Bytes :=
  u64le e.slotsPerEpoch ++ u64le e.leaderScheduleSlotOffset ++ [boolByte e.warmup] ++
    List.replicate 7 0 ++ u64le e.firstNormalEpoch ++ u64le e.firstNormalSlot

/-- The bincode layout: 33 bytes. -/
def EpochSchedule.bincode (e : EpochSchedule) : Bytes :=
  u64le e.slotsPerEpoch ++ u64le e.leaderScheduleSlotOffset ++ [boolByte e.warmup] ++
    u64le e.firstNormalEpoch ++ u64le e.firstNormalSlot

/-- The `Rent` sysvar from solana-rent 4.4.0. The threshold is kept as the 8 bytes
of its `f64` representation. -/
structure RentSysvar where
  lamportsPerByte : Nat
  thresholdBits : Nat
  burnPercent : Nat
  deriving DecidableEq, Repr

/-- Encode the fixed rent profile as the typed Rent sysvar. Under `RentParams.WF`,
the threshold bits are exactly the IEEE-754 encodings of 1.0 or 2.0. -/
def RentParams.toSysvar (rent : RentParams) : RentSysvar :=
  { lamportsPerByte := rent.lamportsPerByte
    thresholdBits := if rent.thresholdNum = 1 then 0x3ff0000000000000 else 0x4000000000000000
    burnPercent := rent.burnPercent }

/-- The `repr(C)` layout: 24 bytes. -/
def RentSysvar.reprC (r : RentSysvar) : Bytes :=
  u64le r.lamportsPerByte ++ leBytes 8 r.thresholdBits ++ [UInt8.ofNat r.burnPercent] ++
    List.replicate 7 0

/-- The bincode layout: 17 bytes. -/
def RentSysvar.bincode (r : RentSysvar) : Bytes :=
  u64le r.lamportsPerByte ++ leBytes 8 r.thresholdBits ++ [UInt8.ofNat r.burnPercent]

/-- `EpochRewards` from solana-epoch-rewards 3.2.0, declared `repr(C, align(16))`.
Its runtime representation additionally requires bounded integer fields and a
32-byte parent blockhash. -/
structure EpochRewards where
  distributionStartingBlockHeight : Nat
  numPartitions : Nat
  parentBlockhash : Bytes
  totalPoints : Nat
  totalRewards : Nat
  distributedRewards : Nat
  active : Bool
  deriving DecidableEq, Repr

/-- The `repr(C)` layout: 96 bytes, with 15 zero bytes after `active`. -/
def EpochRewards.reprC (e : EpochRewards) : Bytes :=
  u64le e.distributionStartingBlockHeight ++ u64le e.numPartitions ++ e.parentBlockhash ++
    leBytes 16 e.totalPoints ++ u64le e.totalRewards ++ u64le e.distributedRewards ++
    [boolByte e.active] ++ List.replicate 15 0

/-- The bincode layout: 81 bytes. -/
def EpochRewards.bincode (e : EpochRewards) : Bytes :=
  u64le e.distributionStartingBlockHeight ++ u64le e.numPartitions ++ e.parentBlockhash ++
    leBytes 16 e.totalPoints ++ u64le e.totalRewards ++ u64le e.distributedRewards ++
    [boolByte e.active]

/-- The sysvars of a bank, fixed for a transaction. The typed values serve the typed
getters, and `data` holds the account data of the seven sysvars of the sysvar cache,
which `sol_get_sysvar` serves through `SysvarCache::sysvar_id_to_buffer` in Agave 4.3.2. -/
structure Sysvars where
  clock : Clock
  epochSchedule : EpochSchedule
  rent : RentSysvar
  epochRewards : Option EpochRewards
  lastRestartSlot : Option Nat
  /-- `lamports_per_signature` of the deprecated `Fees` sysvar. -/
  feesLamportsPerSignature : Nat
  /-- The account data of Clock, EpochSchedule, EpochRewards, Rent, SlotHashes,
  StakeHistory and LastRestartSlot, where present. -/
  data : Pubkey → Option Bytes

/-- The sysvar ids that the sysvar cache holds as bytes. -/
def cachedSysvarIds : List Pubkey :=
  [Ids.sysvarClock, Ids.sysvarEpochSchedule, Ids.sysvarEpochRewards, Ids.sysvarRent,
    Ids.sysvarSlotHashes, Ids.sysvarStakeHistory, Ids.sysvarLastRestartSlot]

/-- The partial cache invariant for Clock, Rent and EpochSchedule and the permitted
cached ids. This does not impose runtime integer widths or agreement of optional
EpochRewards and LastRestartSlot values with their cached bytes. Those remain
separate source-correspondence premises. -/
def Sysvars.WF (s : Sysvars) : Prop :=
  (∃ d, s.data Ids.sysvarClock = some d ∧ s.clock.encode <+: d) ∧
  (∃ d, s.data Ids.sysvarRent = some d ∧ s.rent.bincode <+: d) ∧
  (∃ d, s.data Ids.sysvarEpochSchedule = some d ∧ s.epochSchedule.bincode <+: d) ∧
  (∀ k, k ∉ cachedSysvarIds → s.data k = none)

/-- The typed sysvars and the bytes that their getters write. -/
inductive TypedSysvar where
  | clock
  | epochSchedule
  | rent
  | epochRewards
  | lastRestartSlot
  | fees
  deriving DecidableEq, Repr

/-- The size and alignment used by `get_sysvar` for the typed getters in Agave 4.3.2,
`syscalls/src/sysvar.rs`; see
[syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives). -/
def TypedSysvar.sizeAlign : TypedSysvar → Nat × Nat
  | .clock => (40, 8)
  | .epochSchedule => (40, 8)
  | .rent => (24, 8)
  | .epochRewards => (96, 16)
  | .lastRestartSlot => (8, 8)
  | .fees => (8, 8)

/-- The bytes that a typed getter writes, or `none` when the sysvar cache has no entry
(`UnsupportedSysvar`). -/
def TypedSysvar.value (s : Sysvars) : TypedSysvar → Option Bytes
  | .clock => some s.clock.encode
  | .epochSchedule => some s.epochSchedule.reprC
  | .rent => some s.rent.reprC
  | .epochRewards => s.epochRewards.map EpochRewards.reprC
  | .lastRestartSlot => s.lastRestartSlot.map u64le
  | .fees => some (u64le s.feesLamportsPerSignature)

end Solanalib.Runtime
