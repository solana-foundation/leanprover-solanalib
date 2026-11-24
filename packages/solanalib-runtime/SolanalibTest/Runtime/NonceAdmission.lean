/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

import Solanalib.Runtime.Transaction

/-!
Focused admission and rollback regressions. Hash values in this fixture are
explicit symbolic-primitive outputs; the tests make no cryptographic claim.
They exercise the pre-fee nonce check rather than complete transaction execution.
-/

open Solanalib.Runtime

namespace SolanalibTest.Runtime.NonceAdmissionTest

private def payerKey : Pubkey := Pubkey.ofNat 501
private def nonceKey : Pubkey := Pubkey.ofNat 502
private def authorityKey : Pubkey := Pubkey.ofNat 503
private def oldNonce : Pubkey := Pubkey.ofNat 504
private def newNonce : Pubkey := Pubkey.ofNat 505

private def nonceAccount (authority : Pubkey) : Account :=
  { lamports := 2000000, owner := Ids.systemProgram, executable := false, rentEpoch := 12,
    data := NonceData.encode ⟨authority, oldNonce, 5000⟩ }

private def payerAccount : Account :=
  { lamports := 1000000, owner := Ids.systemProgram, executable := false, rentEpoch := 11,
    data := [] }

private def accounts : Accounts := fun key =>
  if key = payerKey then some payerAccount
  else if key = nonceKey then some (nonceAccount authorityKey) else none

private def message : Message :=
  { numRequiredSignatures := 2, numReadonlySigned := 1, numReadonlyUnsigned := 1,
    staticKeys := [payerKey, authorityKey, nonceKey, Ids.systemProgram],
    loadedWritable := [], loadedReadonly := [], recentBlockhash := oldNonce.bytes,
    instructions := [⟨3, [2, 1], u32le 4⟩] }

private def tx : Tx :=
  { message := message, fee := 10000, loadedDataLimit := 64 * 1024 * 1024,
    heapSize := 32 * 1024, nonce := some 2, bankCheck := none }

private def bank (base : BankEnv) : BankEnv :=
  { base with
    prof := mainnet
    prims := { base.prims with
      sha256 := fun _ => newNonce.bytes, sha256_length := fun _ => newNonce.length_eq }
    isRecentBlockhash := fun _ => false
    environmentBlockhash := Pubkey.ofNat 506
    nextLamportsPerSignature := 6000
    strictNonceSizeCheck := true }

private def advanced (authority : Pubkey) : Account :=
  { nonceAccount authority with data := NonceData.encode ⟨authority, newNonce, 6000⟩ }

/-- The fixture satisfies the source representation and header index conditions. -/
theorem message_well_formed : message.WF mainnet := by
  simp [Message.WF, message, Message.keys, mainnet, mainnetFeatures,
    Profile.maxTxAccountLocks]
  decide

theorem nonce_account_well_formed (authority : Pubkey) : (nonceAccount authority).WF := by
  simp [Account.WF, nonceAccount, NonceData.encode_length, U64_LIMIT, MAX_ACCOUNT_DATA_LEN]

theorem bank_well_formed (base : BankEnv) (valid : base.WF) (profile : base.prof = mainnet) :
    (bank base).WF := by
  refine ⟨?_, valid.sysvars, ?_, valid.builtins⟩
  · simpa [bank, ← profile] using valid.profile
  · simpa [bank, ← profile] using valid.rent

theorem separate_nonce_admitted (base : BankEnv) :
    validateNonce (bank base) accounts tx = .ok (some (nonceKey, advanced authorityKey)) := by
  rfl

/-- A forged balance cannot be the advanced state admitted for rollback. -/
theorem forged_balance_not_admitted (base : BankEnv) :
    validateNonce (bank base) accounts tx ≠
      .ok (some (nonceKey, { advanced authorityKey with lamports := 9000000 })) := by
  intro valid
  obtain ⟨account, stored, balance, _⟩ := validateNonce_preserves_fields valid
  have actual : accounts nonceKey = some (nonceAccount authorityKey) := by rfl
  rw [actual] at stored
  cases stored
  cases balance

private def samePayerTx : Tx :=
  { tx with
    message :=
      { message with
        numRequiredSignatures := 1
        numReadonlySigned := 0
        staticKeys := [payerKey, Ids.systemProgram]
        instructions := [⟨1, [0], u32le 4⟩] }
    nonce := some 0 }

private def samePayerAccounts : Accounts := fun key =>
  if key = payerKey then some (nonceAccount payerKey) else none

theorem same_payer_nonce_admitted (base : BankEnv) :
    validateNonce (bank base) samePayerAccounts samePayerTx =
      .ok (some (payerKey, advanced payerKey)) := by
  rfl

/-- A valid recent blockhash selects no durable nonce despite a nonce instruction. -/
theorem recent_blockhash_has_no_nonce_write (base : BankEnv) :
    validateNonce { bank base with isRecentBlockhash := fun _ => true } accounts
      { tx with nonce := none } = .ok none := by
  rfl

theorem omitted_required_nonce_rejected (base : BankEnv) :
    validateNonce (bank base) accounts { tx with nonce := none } =
      .error .BlockhashNotFound := by
  rfl

theorem out_of_range_nonce_rejected (base : BankEnv) :
    validateNonce (bank base) accounts { tx with nonce := some 999 } =
      .error .BlockhashNotFound := by
  rfl

theorem selected_nonce_with_recent_blockhash_rejected (base : BankEnv) :
    validateNonce { bank base with isRecentBlockhash := fun _ => true } accounts tx =
      .error .BlockhashNotFound := by
  rfl

theorem readonly_nonce_rejected (base : BankEnv) :
    validateNonce (bank base) accounts
      { tx with message := { message with numReadonlyUnsigned := 2 } } =
      .error .BlockhashNotFound := by
  rfl

/-- A writable lookup-table key still fails the static nonce-key restriction. -/
theorem lookup_table_nonce_rejected (base : BankEnv) :
    validateNonce (bank base) accounts
      { tx with
        message :=
          { message with
            staticKeys := [payerKey, authorityKey, Ids.systemProgram]
            loadedWritable := [nonceKey]
            instructions := [⟨2, [3, 1], u32le 4⟩] }
        nonce := some 3 } = .error .BlockhashNotFound := by
  rfl

theorem marker_trailing_instruction_bytes_allowed (base : BankEnv) :
    validateNonce (bank base) accounts
      { tx with message := { message with instructions := [⟨3, [2, 1], u32le 4 ++ [123]⟩] } } =
      .ok (some (nonceKey, advanced authorityKey)) := by
  rfl

theorem authority_must_be_in_marker_instruction (base : BankEnv) :
    validateNonce (bank base) accounts
      { tx with message := { message with instructions := [⟨3, [2], u32le 4⟩] } } =
      .error .BlockhashNotFound := by
  rfl

theorem authority_must_be_signer (base : BankEnv) :
    validateNonce (bank base) accounts
      { tx with message := { message with numRequiredSignatures := 1 } } =
      .error .BlockhashNotFound := by
  rfl

theorem different_stored_blockhash_rejected (base : BankEnv) :
    validateNonce (bank base) accounts
      { tx with message := { message with recentBlockhash := (Pubkey.ofNat 507).bytes } } =
      .error .BlockhashNotFound := by
  rfl

theorem already_advanced_nonce_rejected (base : BankEnv) :
    validateNonce
      { bank base with prims := { base.prims with
          sha256 := fun _ => oldNonce.bytes, sha256_length := fun _ => oldNonce.length_eq } }
      accounts tx = .error .BlockhashNotFound := by
  rfl

theorem missing_nonce_rejected_before_fee_payer (base : BankEnv) :
    validateNonce (bank base) (fun _ => none) tx = .error .AccountNotFound := by
  rfl

private def replaceNonce (account : Account) : Accounts := fun key =>
  if key = nonceKey then some account else accounts key

theorem zero_balance_nonce_is_missing (base : BankEnv) :
    validateNonce (bank base)
      (replaceNonce { nonceAccount authorityKey with lamports := 0 }) tx =
      .error .AccountNotFound := by
  rfl

theorem foreign_owner_nonce_rejected (base : BankEnv) :
    validateNonce (bank base)
      (replaceNonce { nonceAccount authorityKey with owner := payerKey }) tx =
      .error .BlockhashNotFound := by
  rfl

private def legacyNonce : Account :=
  { nonceAccount authorityKey with
    data := u32le 0 ++ (nonceAccount authorityKey).data.drop 4 }

theorem legacy_nonce_still_fee_payer : isInitializedNonceAccount legacyNonce = true := by
  rfl

theorem legacy_nonce_not_durable_admission (base : BankEnv) :
    validateNonce (bank base) (replaceNonce legacyNonce) tx = .error .BlockhashNotFound := by
  rfl

private def nonceWithTail : Account :=
  { nonceAccount authorityKey with data := (nonceAccount authorityKey).data ++ [8, 9] }

theorem strict_nonce_size_rejects_tail (base : BankEnv) :
    validateNonce (bank base) (replaceNonce nonceWithTail) tx =
      .error .BlockhashNotFound := by
  rfl

theorem nonstrict_nonce_preserves_tail (base : BankEnv) :
    validateNonce { bank base with strictNonceSizeCheck := false }
      (replaceNonce nonceWithTail) tx =
      .ok (some (nonceKey,
        { advanced authorityKey with data := (advanced authorityKey).data ++ [8, 9] })) := by
  rfl

/-- Admission uses the current stored rent epoch; it does not apply the
separate fee-payer rent-exempt normalization to the advanced nonce copy. -/
theorem advance_retains_stored_epoch : (advanced authorityKey).rentEpoch = 12 := by
  rfl

/-- No fee or rollback effect can follow a rejected nonce, even if fee-payer
validation would independently have failed. -/
theorem rejected_nonce_outcome (base : BankEnv) :
    ProcTx (bank base) accounts { tx with nonce := some 999 } accounts
      (.notLoaded .BlockhashNotFound) := by
  exact ProcTx.nonceRejected rfl (out_of_range_nonce_rejected base)

theorem rejected_nonce_preserves_every_account (base : BankEnv) {post : Accounts}
    {outcome : TxOutcome}
    (processed : ProcTx (bank base) accounts { tx with nonce := some 999 } post outcome) :
    post = accounts ∧ outcome = .notLoaded .BlockhashNotFound := by
  exact ProcTx.nonce_error rfl (out_of_range_nonce_rejected base) processed

end SolanalibTest.Runtime.NonceAdmissionTest
