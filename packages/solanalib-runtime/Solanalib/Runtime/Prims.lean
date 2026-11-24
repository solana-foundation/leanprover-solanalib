/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Profile

@[expose] public section

/-!
# Cryptographic primitives and program addresses

The hash functions and curve operations are parameters. Their intended inputs,
result interpretation and width requirements follow the handlers in Agave 4.3.2,
`syscalls/src/lib.rs`. The output widths of the four hash syscalls are laws of `Prims`:
`SyscallHash` writes `size_of::<H::Output>()` bytes, 32 for SHA-256, Keccak-256 and
BLAKE3 and 64 for SHA-512. The correctness of the supplied functions, and the widths
of the other primitives, are separate premises. Program addresses use the same
SHA-256 and curve predicate as the corresponding syscall requests. See
[syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives).
-/

namespace Solanalib.Runtime

/-- The shared symbolic primitives used by address derivation and SHA-256 calls.
The functions remain abstract in specifications and proofs. An executable client
may provide concrete implementations for concrete inputs. The address
contracts of the SDK share this structure for any function; the width of the SHA-256 of the runtime
is a law of `Prims`. -/
structure CryptoPrimitives where
  sha256 : Bytes → Bytes
  /-- Whether 32 bytes decompress to a point of the ed25519 curve. -/
  onCurve : Bytes → Bool

/-- The primitives of the runtime. Each is a deterministic function. -/
structure Prims extends CryptoPrimitives where
  keccak256 : List Bytes → Bytes
  blake3 : List Bytes → Bytes
  sha512 : List Bytes → Bytes
  /-- `sol_sha256` writes `size_of::<Hash>()` bytes: `HASH_BYTES`, 32, in solana-hash 4.6.0. -/
  sha256_length : ∀ bytes, (sha256 bytes).length = 32
  /-- `sol_keccak256` writes `size_of::<keccak::Hash>()` bytes; solana-keccak-hasher 3.1.0
  re-exports the 32-byte `Hash` of solana-hash. -/
  keccak256_length : ∀ slices, (keccak256 slices).length = 32
  /-- `sol_blake3` writes `size_of::<blake3::Hash>()` bytes; solana-blake3-hasher 3.1.0
  re-exports the 32-byte `Hash` of solana-hash. -/
  blake3_length : ∀ slices, (blake3 slices).length = 32
  /-- `sol_sha512` writes `size_of::<Hash512>()` bytes: `HASH_BYTES`, 64, in solana-hash-512
  1.2.0. -/
  sha512_length : ∀ slices, (sha512 slices).length = 64
  /-- UTF-8 validity, which `sol_log_` and `sol_panic_` test. -/
  isUtf8 : Bytes → Bool
  /-- Intended result of `SyscallSecp256k1Recover`: a 64-byte key, or status 2 or 3.
  The supplied primitive must satisfy this width and error contract. -/
  secp256k1Recover : Bytes → Nat → Bytes → Except Nat Bytes
  /-- Poseidon with a parameter set and an endianness; `none` for a library error. -/
  poseidon : Nat → Nat → List Bytes → Option Bytes
  /-- Curve point validation, group operations, multiscalar multiplication,
  decompression and pairing, indexed by the curve id and operation code interpreted
  by the handlers in Agave 4.3.2 `syscalls/src/lib.rs`. -/
  curveValidate : Nat → Bytes → Bool
  curveGroupOp : Nat → Nat → Bytes → Bytes → Option Bytes
  curveMultiscalarMul : Nat → List Bytes → List Bytes → Option Bytes
  curveDecompress : Nat → Bytes → Option Bytes
  curvePairingMap : Nat → List Bytes → List Bytes → Option Bytes
  /-- The abstract operations invoked by `SyscallAltBn128` and
  `SyscallAltBn128Compression` in Agave 4.3.2. -/
  altBn128GroupOp : Nat → Bytes → Option Bytes
  altBn128Compression : Nat → Bytes → Option Bytes
  /-- Legacy modular exponentiation, with big-endian operands and leading zero padding. -/
  bigModExp : Bytes → Bytes → Bytes → Bytes
  /-- Agave 4.3.2 uses solana-big-mod-exp 4.0.0: little-endian operands and trailing
  zero padding; invalid moduli return none. The syscall remains feature-gated. -/
  bigModExpLe : Bytes → Bytes → Bytes → Option Bytes
  /-- The verification of a precompile instruction, given the program id, the
  instruction data and the data of all top-level instructions; `some n` is the
  discriminant of the `PrecompileError`. The relation to actual verification is
  an explicit contract, as described in
  [syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives). -/
  precompileVerify : Pubkey → Bytes → List Bytes → Option Nat

/-- Edwards validation and PDA derivation use the same symbolic curve predicate.
Other supported curves retain their separately supplied abstract operations. -/
def Prims.validatePoint (P : Prims) (curve : Nat) (point : Bytes) : Bool :=
  if curve = 0 then P.onCurve point else P.curveValidate curve point

theorem Prims.validatePoint_edwards (P : Prims) (point : Bytes) :
    P.validatePoint 0 point = P.onCurve point := by
  simp only [validatePoint, ite_true]

/-- The `PDA_MARKER` appended by `create_program_address`; see
[syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives). -/
def PDA_MARKER : Bytes := strBytes "ProgramDerivedAddress"

/-- The failures of `create_program_address`. -/
inductive PdaError where
  | maxSeedLengthExceeded
  | invalidSeeds
  deriving DecidableEq, Repr

/-- The seed limits checked by both runtime address operations and their interfaces. -/
def seedsOk (seeds : List Bytes) : Bool :=
  seeds.length ≤ MAX_SEEDS && seeds.all (·.length ≤ MAX_SEED_LEN)

/-- Byte-level address derivation, shared by the runtime and its executable interfaces. -/
def createProgramAddressBytes (P : CryptoPrimitives) (seeds : List Bytes) (programId : Bytes) :
    Except PdaError Bytes :=
  if MAX_SEEDS < seeds.length then .error .maxSeedLengthExceeded
  else if seeds.any (fun s => decide (MAX_SEED_LEN < s.length)) then .error .maxSeedLengthExceeded
  else
    let h := P.sha256 (seeds.flatten ++ programId ++ PDA_MARKER)
    if P.onCurve h then .error .invalidSeeds else .ok h

/-- The value-level `create_program_address` operation used by
`SyscallCreateProgramAddress` in Agave 4.3.2. -/
def createProgramAddress (P : Prims) (seeds : List Bytes) (programId : Pubkey) :
    Except PdaError Pubkey :=
  (createProgramAddressBytes P.toCryptoPrimitives seeds programId.bytes).map Pubkey.ofBytes

/-- The address search shared by the runtime and its executable interfaces: bumps
from 255 down to 1. `SyscallTryFindProgramAddress` in Agave 4.3.2 never tries bump 0. -/
def findProgramAddressBytes (P : CryptoPrimitives) (seeds : List Bytes) (programId : Bytes) :
    Option (Bytes × Nat) :=
  go 255
where
  go : Nat → Option (Bytes × Nat)
    | 0 => none
    | b + 1 =>
      match createProgramAddressBytes P (seeds ++ [[UInt8.ofNat (b + 1)]]) programId with
      | .ok k => some (k, b + 1)
      | .error _ => go b

/-- The typed runtime view of the shared byte-level address search. -/
def findProgramAddress (P : Prims) (seeds : List Bytes) (programId : Pubkey) :
    Option (Pubkey × Nat) :=
  (findProgramAddressBytes P.toCryptoPrimitives seeds programId.bytes).map
    (fun (key, bump) => (Pubkey.ofBytes key, bump))

/-- `Pubkey::create_with_seed`, with the discriminants of `PubkeyError` as errors:
0 for a seed longer than 32 bytes, 2 for an owner that ends with the marker
(`solana-address` `create_with_seed`). -/
def createWithSeed (P : Prims) (base : Pubkey) (seed : Bytes) (owner : Pubkey) :
    Except Nat Pubkey :=
  if MAX_SEED_LEN < seed.length then .error 0
  else if owner.bytes.drop (32 - PDA_MARKER.length) = PDA_MARKER then .error 2
  else .ok (Pubkey.ofBytes (P.sha256 (base.bytes ++ seed ++ owner.bytes)))

end Solanalib.Runtime
