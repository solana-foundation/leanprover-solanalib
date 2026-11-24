/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Basic

@[expose] public section

/-!
# Runtime profile

A profile fixes the runtime release, the feature gates that a program can observe
and the rent parameters.
Compute units are outside the model: a profile has no compute budget, and the
semantics lets every metered step fail with a compute error instead
(cf. `Solanalib.Runtime.IsComputeError`).

The [current source justification](../../source-notes/agave-4.3.2.md#profile-and-limits)
fixes Agave 4.3.2 and distinguishes checked runtime behavior, observed feature
settings and the historical branches retained for earlier releases.
-/

namespace Solanalib.Runtime

/-- The release that a profile describes. -/
inductive Release where
  | agave_3_1_12
  | agave_4_1_2
  /-- Agave 4.3.2. The account setters and touched-account commit rules are
  checked against the source at the `v4.3.2` tag. -/
  | agave_4_3_2
  deriving DecidableEq, Repr

/-- The memory configurations of the input region; see the current
[memory analysis](../../source-notes/agave-4.3.2.md#memory). -/
inductive MemConfig where
  /-- One writable region; account data is copied in and compared at read-back. -/
  | L
  /-- Account data in regions of their own, whose length tracks the data length. -/
  | S
  /-- Account data regions that map the account storage of the transaction context. -/
  | D
  deriving DecidableEq, Repr

/-- The feature gates represented by the model; see
[profile and limits](../../source-notes/agave-4.3.2.md#profile-and-limits). -/
structure Features where
  /-- SIMD-0459 `syscall_parameter_address_restrictions`, or SIMD-0219 in 3.1.12:
  account-info pointer checks, destinations below the input region, and the
  realloc bound on both CPI edges. -/
  pointerChecks : Bool
  /-- SIMD-0460 `virtual_address_space_adjustments`, or SIMD-0219 in 3.1.12. -/
  addressSpace : Bool
  /-- `account_data_direct_mapping`; effective only together with `addressSpace`. -/
  directMapping : Bool
  /-- SIMD-0449: account pointer array after the program id. -/
  accountPointerArray : Bool
  /-- SIMD-0267: rent epoch serialized as `u64::MAX`; unconditional from 4.1.2. -/
  maskRentEpoch : Bool
  /-- SIMD-0321: r2 holds the instruction-data address; unconditional from 4.1.2. -/
  instrDataInR2 : Bool
  /-- SIMD-0268: instruction stack depth 9 instead of 5. -/
  cpiNesting8 : Bool
  /-- SIMD-0339: 255 account infos per CPI in 3.1.12; unconditional from 4.1.2. -/
  cpiAccountInfos255 : Bool
  /-- `increase_tx_account_lock_limit`: 128 account locks instead of 64. -/
  txAccountLockLimit128 : Bool
  /-- SIMD-0160: at most 64 top-level instructions. -/
  staticInstructionLimit : Bool
  /-- SIMD-0406: at most 255 account references per instruction. -/
  limitInstructionAccounts : Bool
  /-- SIMD-0186: loaded-data accounting with 64 bytes per account. -/
  loadedDataSizeAccounting : Bool
  /-- SIMD-0392: relaxed post-execution minimum-balance check. -/
  relaxPostExecMinBalance : Bool
  /-- SIMD-0312: System instruction `CreateAccountAllowPrefund`. -/
  createAccountAllowPrefund : Bool
  /-- SIMD-0127: `sol_get_sysvar`. -/
  getSysvarSyscall : Bool
  /-- `sol_get_epoch_stake`. -/
  epochStakeSyscall : Bool
  /-- `sol_get_last_restart_slot`. -/
  lastRestartSlotSysvar : Bool
  /-- `disable_fees_sysvar`: `sol_get_fees_sysvar` unregistered. -/
  disableFeesSysvar : Bool
  /-- `sol_curve_validate_point`, `sol_curve_group_op`, `sol_curve_multiscalar_mul`. -/
  curve25519Syscalls : Bool
  /-- SIMD-0388: BLS12-381 curve ids and two further syscalls. -/
  bls12_381Syscalls : Bool
  /-- `sol_alt_bn128_group_op`. -/
  altBn128Syscall : Bool
  /-- `sol_alt_bn128_compression`. -/
  altBn128Compression : Bool
  /-- SIMD-0284: little-endian BN254 operations. -/
  altBn128LittleEndian : Bool
  /-- SIMD-0302: BN254 G2 operations. -/
  altBn128G2 : Bool
  /-- `sol_poseidon`. -/
  poseidonSyscall : Bool
  /-- `sol_remaining_compute_units`. -/
  remainingComputeUnitsSyscall : Bool
  /-- `sol_big_mod_exp`. -/
  bigModExpSyscall : Bool
  /-- `sol_blake3`. -/
  blake3Syscall : Bool
  /-- SIMD-0512: `sol_sha512`. -/
  sha512Syscall : Bool
  /-- SIMD-0137: an unknown curve id or operation aborts. -/
  abortOnInvalidCurve : Bool
  /-- SIMD-0075: the secp256r1 precompile. -/
  secp256r1Precompile : Bool
  /-- SIMD-0167: loader v4. -/
  loaderV4 : Bool
  /-- `enable_extend_program_checked`. -/
  extendProgramChecked : Bool
  /-- `enable_bpf_loader_set_authority_checked_ix`. -/
  setAuthorityCheckedIx : Bool
  /-- SIMD-0290 NoOp fee payers. The supported profile keeps this inactive;
  its separate fee-payer classification is outside this model. -/
  noopFeePayer : Bool := false
  deriving DecidableEq, Repr

/-- Rent parameters. The mathematical minimum for `len` data bytes is
`(128 + len) * lamportsPerByte * thresholdNum / thresholdDen`. It agrees with the
integer branches of solana-rent 4.4.0 at thresholds 1 and 2 when the length and rate
satisfy `Rent::try_minimum_balance`; see
[accounts and rent](../../source-notes/agave-4.3.2.md#accounts-and-rent). -/
structure RentParams where
  lamportsPerByte : Nat
  thresholdNum : Nat
  thresholdDen : Nat
  burnPercent : Nat
  deriving DecidableEq, Repr

/-- The integer rent parameters admitted by the mathematical model.
The thresholds 1 and 2 avoid floating-point arithmetic. This predicate does not
enforce the stronger rate and length bounds of `Rent::try_minimum_balance`, so a
runtime correspondence needs those bounds separately. -/
def RentParams.WF (rent : RentParams) : Prop :=
  rent.lamportsPerByte < U64_LIMIT ∧ rent.thresholdDen = 1 ∧
    (rent.thresholdNum = 1 ∨ rent.thresholdNum = 2) ∧ rent.burnPercent ≤ 100

/-- A runtime profile. -/
structure Profile where
  release : Release
  features : Features
  rent : RentParams
  /-- The slot at which the feature accounts were read. -/
  slot : Nat
  deriving Repr

/-! ## Constants of the runtime -/

/-- `MAX_PERMITTED_DATA_INCREASE` (`solana-account-info-3.1.1/src/lib.rs:23`). -/
def MAX_PERMITTED_DATA_INCREASE : Nat := 10240
/-- `MAX_ACCOUNT_DATA_LEN`, Agave 4.3.2 `transaction-context/src/lib.rs`. -/
def MAX_ACCOUNT_DATA_LEN : Nat := 10 * 1024 * 1024
/-- `MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION`, Agave 4.3.2
`transaction-context/src/lib.rs`. -/
def MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION : Nat := 2 * MAX_ACCOUNT_DATA_LEN
/-- `MAX_ACCOUNTS_PER_INSTRUCTION`, Agave 4.3.2 `transaction-context/src/lib.rs`. -/
def MAX_ACCOUNTS_PER_INSTRUCTION : Nat := 255
/-- `MAX_INSTRUCTION_TRACE_LENGTH`, Agave 4.3.2 `transaction-context/src/lib.rs`. -/
def MAX_INSTRUCTION_TRACE_LENGTH : Nat := 64
/-- The CPI account-meta limit checked by `check_instruction_size` in Agave 4.3.2
`program-runtime/src/cpi.rs`. -/
def MAX_CPI_INSTRUCTION_ACCOUNTS : Nat := 255
/-- The CPI instruction-data limit checked by `check_instruction_size` in Agave 4.3.2
`program-runtime/src/cpi.rs`. -/
def MAX_CPI_INSTRUCTION_DATA_LEN : Nat := 10240
/-- `MAX_SIGNERS` of a CPI, Agave 4.3.2 `program-runtime/src/cpi.rs`. -/
def MAX_SIGNERS : Nat := 16
/-- `MAX_SEEDS`, used by `translate_signers` in Agave 4.3.2; see
[syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives). -/
def MAX_SEEDS : Nat := 16
/-- `MAX_SEED_LEN`, checked by program-address derivation; see
[syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives). -/
def MAX_SEED_LEN : Nat := 32
/-- `MAX_RETURN_DATA` from solana-cpi 3.1.0, used by
`SyscallSetReturnData` in Agave 4.3.2. -/
def MAX_RETURN_DATA : Nat := 1024
/-- The maximum number of slices passed to a hash syscall
(`ExecutionBudget::sha256_max_slices`, Agave 4.3.2). -/
def MAX_HASH_SLICES : Nat := 20000
/-- `MM_INPUT_START` in the pinned solana-sbpf 0.23.0 address space; see
[memory](../../source-notes/agave-4.3.2.md#memory). -/
def MM_INPUT_START : Nat := 4 * 2 ^ 32
/-- `MM_HEAP_START` in the pinned solana-sbpf 0.23.0 address space. -/
def MM_HEAP_START : Nat := 3 * 2 ^ 32
/-- `MM_STACK_START` in the pinned solana-sbpf 0.23.0 address space. -/
def MM_STACK_START : Nat := 2 * 2 ^ 32
/-- `NON_DUP_MARKER` (`solana-program-entrypoint-3.1.1/src/lib.rs:42`). -/
def NON_DUP_MARKER : UInt8 := 0xFF
/-- `MAX_ACCOUNTS_PER_TRANSACTION` in Agave 4.3.2
`transaction-context/src/lib.rs`. The selected account-lock limit can be smaller. -/
def MAX_TX_ACCOUNTS : Nat := 256
/-- `MIN_HEAP_FRAME_BYTES`, the default heap size of `ExecutionBudget` in Agave 4.3.2. -/
def DEFAULT_HEAP_SIZE : Nat := 32 * 1024
/-- `MAX_LOADED_ACCOUNTS_DATA_SIZE_BYTES` in Agave 4.3.2
`program-runtime/src/execution_budget.rs`. -/
def MAX_LOADED_ACCOUNTS_DATA_SIZE : Nat := 64 * 1024 * 1024

namespace Profile

/-- Validity of the fixed rent configuration. -/
def WF (profile : Profile) : Prop := profile.rent.WF ∧ profile.features.noopFeePayer = false

/-- The supported limit on slice inputs of a hash syscall. -/
def maxHashSlices (_p : Profile) : Nat := MAX_HASH_SLICES

/-- The memory configuration selected by the represented feature gates; see
[memory](../../source-notes/agave-4.3.2.md#memory). -/
def memConfig (p : Profile) : MemConfig :=
  if !p.features.addressSpace then .L else if p.features.directMapping then .D else .S

/-- The instruction stack capacity selected by `ExecutionBudget`: 5, or 9 with
`raise_cpi_nesting_limit_to_8`; see
[profile and limits](../../source-notes/agave-4.3.2.md#profile-and-limits). -/
def maxStackDepth (p : Profile) : Nat := if p.features.cpiNesting8 then 9 else 5

/-- The account-info limit of `check_account_infos` in Agave 4.3.2.
The 3.1.12 branch retains its historical feature-dependent limit; see
[CPI](../../source-notes/agave-4.3.2.md#cpi). -/
def maxCpiAccountInfos (p : Profile) : Nat :=
  match p.release with
  | .agave_3_1_12 =>
    if p.features.cpiAccountInfos255 then 255
    else if p.features.txAccountLockLimit128 then 128 else 64
  | _ => 255

/-- The represented account-lock limit; see
[profile and limits](../../source-notes/agave-4.3.2.md#profile-and-limits). -/
def maxTxAccountLocks (p : Profile) : Nat :=
  if p.features.txAccountLockLimit128 then 128 else 64

/-- Whether r2 holds the instruction-data address at entry. Agave 4.3.2 sets it
unconditionally in `execute`, `program-runtime/src/vm.rs`; the 3.1.12 branch
retains its historical gate. -/
def instrDataInR2 (p : Profile) : Bool :=
  match p.release with
  | .agave_3_1_12 => p.features.instrDataInR2
  | _ => true

/-- Whether `serialize_parameters_for_abiv1` and `serialize_parameters_for_abiv0`
write `u64::MAX` as the rent epoch. Agave 4.3.2 does so unconditionally; the 3.1.12
branch retains its historical gate. -/
def rentEpochMasked (p : Profile) : Bool :=
  match p.release with
  | .agave_3_1_12 => p.features.maskRentEpoch
  | _ => true

/-- Whether the CPI entry edge bounds a changed length by the length at instruction
entry plus 10 KiB. Agave 4.3.2 uses `syscall_parameter_address_restrictions` in
`CallerAccount::get_serialized_data`; the 3.1.12 branch retains the historical
address-space gate. See [CPI](../../source-notes/agave-4.3.2.md#cpi). -/
def cpiEntryEdgeBound (p : Profile) : Bool :=
  match p.release with
  | .agave_3_1_12 => p.features.addressSpace
  | _ => p.features.pointerChecks

/-- The optional account pointer array of `serialize_parameters_for_abiv1`
in Agave 4.3.2. The 3.1.12 branch retains the
historical layout without that array; see
[serialization](../../source-notes/agave-4.3.2.md#serialization-and-read-back). -/
def accountPointerArray (p : Profile) : Bool :=
  match p.release with
  | .agave_3_1_12 => false
  | _ => p.features.accountPointerArray

end Profile

/-- The feature gates of mainnet-beta at slot 462908421, epoch 1071, read on
29 October 2026. This is a fixed observation, not a claim about later slots; see
[profile and limits](../../source-notes/agave-4.3.2.md#profile-and-limits).
The status of `setAuthorityCheckedIx` comes from the LiteSVM mainnet table
(`litesvm-0.14.0/src/features.rs:354-357`), a secondary source. -/
def mainnetFeatures : Features where
  pointerChecks := true
  addressSpace := false
  directMapping := false
  accountPointerArray := false
  maskRentEpoch := true
  instrDataInR2 := true
  cpiNesting8 := false
  cpiAccountInfos255 := true
  txAccountLockLimit128 := false
  staticInstructionLimit := true
  limitInstructionAccounts := true
  loadedDataSizeAccounting := true
  relaxPostExecMinBalance := true
  createAccountAllowPrefund := true
  getSysvarSyscall := true
  epochStakeSyscall := true
  lastRestartSlotSysvar := true
  disableFeesSysvar := true
  curve25519Syscalls := true
  bls12_381Syscalls := true
  altBn128Syscall := true
  altBn128Compression := true
  altBn128LittleEndian := true
  altBn128G2 := true
  poseidonSyscall := true
  remainingComputeUnitsSyscall := false
  bigModExpSyscall := false
  blake3Syscall := false
  sha512Syscall := false
  abortOnInvalidCurve := true
  secp256r1Precompile := true
  loaderV4 := false
  extendProgramChecked := false
  setAuthorityCheckedIx := true

/-- The observed mainnet rent parameters: 5080 lamports per byte, threshold 1 and
burn 50%. The observation and the checked integer branch are recorded in
[accounts and rent](../../source-notes/agave-4.3.2.md#accounts-and-rent). -/
def mainnetRent : RentParams :=
  { lamportsPerByte := 5080, thresholdNum := 1, thresholdDen := 1, burnPercent := 50 }

/-- The mainnet profile, the primary target of the model. -/
def mainnet : Profile :=
  { release := .agave_4_3_2, features := mainnetFeatures, rent := mainnetRent, slot := 462908421 }

theorem mainnet_memConfig : mainnet.memConfig = .L := rfl

theorem mainnet_maxStackDepth : mainnet.maxStackDepth = 5 := rfl

theorem mainnet_wf : mainnet.WF := by
  unfold Profile.WF RentParams.WF mainnet mainnetRent
  decide

end Solanalib.Runtime
