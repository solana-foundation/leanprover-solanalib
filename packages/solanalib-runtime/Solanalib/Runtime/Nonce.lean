/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Message

@[expose] public section

/-!
# Durable nonce admission

The account and instruction checks used by Agave 4.3.2 before fee-payer
validation. The bank supplies its blockhash-age decision; the model checks that
the selected nonce is consistent with that decision and the first instruction.
The durable nonce value is derived through the existing symbolic SHA-256
primitive. No caller supplies an advanced account.

Sources: `runtime/src/bank/check_transactions.rs:231-299`,
`svm/src/transaction_processor.rs:833-897`, `solana-svm-transaction` 5.0.0
`src/svm_message.rs:125-179`, and `solana-nonce` 3.3.0 `state.rs` / `versions.rs`.
The exact immutable revisions and scope are recorded in
[`agave-4.3.2.md`](../../source-notes/agave-4.3.2.md).
-/

namespace Solanalib.Runtime

/-- The initialized payload of a current nonce account. The fee field occupies
eight bytes; decoding therefore gives a value below `2^64`. -/
structure NonceData where
  authority : Pubkey
  durableNonce : Pubkey
  lamportsPerSignature : Nat
  deriving DecidableEq, Repr

/-- Current-version and initialized-state tags, authority, durable nonce and
the next signature fee, in their stored order. -/
def NonceData.encode (data : NonceData) : Bytes :=
  u32le 1 ++ u32le 1 ++ data.authority.bytes ++ data.durableNonce.bytes ++
    u64le data.lamportsPerSignature

theorem NonceData.encode_length (data : NonceData) : data.encode.length = 80 := by
  simp [encode, u32le, u64le, Pubkey.length_eq]

/-- Decode a current initialized nonce. Legacy nonce accounts can pay fees,
but `Versions::verify_recent_blockhash` excludes them from durable admission.
Trailing bytes are accepted by the account codec; the strict size check is
applied separately by transaction validation. -/
def decodeCurrentNonce (account : Account) : Option NonceData :=
  if account.owner != Ids.systemProgram || account.data.length < 80 ||
      leNat (slice account.data 0 4) != 1 || leNat (slice account.data 4 4) != 1 then none
  else some {
    authority := Pubkey.ofBytes (slice account.data 8 32)
    durableNonce := Pubkey.ofBytes (slice account.data 40 32)
    lamportsPerSignature := leNat (slice account.data 72 8) }

theorem decodeCurrentNonce_size {account : Account} {data : NonceData}
    (decoded : decodeCurrentNonce account = some data) : 80 ≤ account.data.length := by
  by_cases sized : 80 ≤ account.data.length
  · exact sized
  · have short : account.data.length < 80 := by omega
    simp [decodeCurrentNonce, short] at decoded

theorem decodeCurrentNonce_fee_bound {account : Account} {data : NonceData}
    (decoded : decodeCurrentNonce account = some data) : data.lamportsPerSignature < U64_LIMIT := by
  have sized := decodeCurrentNonce_size decoded
  have width : (slice account.data 72 8).length = 8 := length_slice_of_le sized
  have bound := leNat_lt (slice account.data 72 8)
  rw [width] at bound
  unfold decodeCurrentNonce at decoded
  split at decoded
  · cases decoded
  · cases decoded
    exact bound

/-- `DurableNonce::from_blockhash`: SHA-256 of the domain prefix followed by
the current bank blockhash. The `Prims` of a bank give a 32-byte result
(`Prims.sha256_length`, `BankEnv.WF.nonceHash`). -/
def nextDurableNonce (prims : CryptoPrimitives) (blockhash : Pubkey) : Pubkey :=
  Pubkey.ofBytes (prims.sha256 (strBytes "DURABLE_NONCE" ++ blockhash.bytes))

/-- `SVMMessage::get_durable_nonce`: the first instruction invokes the System
program and begins with tag 4; its first account is a static writable key.
The marker check permits instruction data after the first four bytes. -/
def Message.durableNonceIndex (profile : Profile) (message : Message) : Option Nat := do
  let instruction ← message.instructions.head?
  let program ← message.keys[instruction.programIdIndex]?
  if program != Ids.systemProgram || slice instruction.data 0 4 != u32le 4 then none
  else do
    let index ← instruction.accounts.head?
    if index < message.staticKeys.length && message.isWritable profile index then some index
    else none

/-- `get_ix_signers(0)` inspects signer accounts of the marker instruction and
resolves their addresses only among static keys. A signature elsewhere in the
message does not authorize nonce admission. -/
def Message.nonceAuthoritySigned (message : Message) (authority : Pubkey) : Bool :=
  match message.instructions.head? with
  | none => false
  | some instruction => instruction.accounts.any fun index =>
      message.isSigner index && message.staticKeys[index]? == some authority

/-- Check the selected nonce against the bank age decision. A valid recent
blockhash uses no durable nonce, even if its first instruction is a nonce
advance; otherwise a matching nonce marker is required. The predicate
`isRecentBlockhash` is the explicit boundary for the bank blockhash queue and
its configured maximum age. -/
def checkNonceSelection (profile : Profile) (isRecentBlockhash : Bytes → Bool)
    (message : Message) (selected : Option Nat) : Except TxError (Option Nat) :=
  if isRecentBlockhash message.recentBlockhash then
    if selected = none then .ok none else .error .BlockhashNotFound
  else match message.durableNonceIndex profile with
    | none => .error .BlockhashNotFound
    | some index =>
      if selected = some index then .ok (some index) else .error .BlockhashNotFound

/-- Advance only the serialized nonce state. The account length and any
trailing bytes remain unchanged when strict size checking is disabled. -/
def advanceNonceAccount (account : Account) (authority next : Pubkey)
    (lamportsPerSignature : UInt64) : Account :=
  let encoded := NonceData.encode ⟨authority, next, lamportsPerSignature.toNat⟩
  { account with data := writeAt account.data 0 encoded }

theorem advanceNonceAccount_fields (account : Account) (authority next : Pubkey)
    (lamportsPerSignature : UInt64) :
    let advanced := advanceNonceAccount account authority next lamportsPerSignature
    advanced.lamports = account.lamports ∧ advanced.owner = account.owner ∧
      advanced.executable = account.executable ∧ advanced.rentEpoch = account.rentEpoch := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem advanceNonceAccount_length (account : Account) (authority next : Pubkey)
    (lamportsPerSignature : UInt64) (sized : 80 ≤ account.data.length) :
    (advanceNonceAccount account authority next lamportsPerSignature).data.length =
      account.data.length := by
  apply length_writeAt
  simpa only [Nat.zero_add, NonceData.encode_length] using sized

end Solanalib.Runtime
