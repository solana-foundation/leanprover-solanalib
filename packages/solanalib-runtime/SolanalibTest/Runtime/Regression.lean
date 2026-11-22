/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Transaction
public import Solanalib.Runtime.StoreOps

@[expose] public section

set_option autoImplicit false

open Solanalib.Runtime

namespace SolanalibTest.Runtime

/-- The largest representable shared count remains available, and taking one
more borrow fails instead of acquiring the exclusive-byte representation. -/
theorem shared_borrow_last : Lease.addShared (.shared 253) = some (.shared 254) := rfl

theorem shared_borrow_full : Lease.addShared (.shared 254) = none := rfl

/-- Agave 4.3.2 performs the size checks and then the readonly/owner checks;
older releases report a foreign resize before those latter checks. -/
theorem resized_foreign_current {state : TxState} {context : SetterCtx} {length : Nat}
    (release : context.release = .agave_4_3_2)
    (room : txCanDataBeResized state (state.acct context.txIdx).data.length length = .ok ())
    (writable : context.writable = true) (foreign : context.owned state = false) :
    canDataBeResized state context length = .error .ExternalAccountDataModified := by
  simp [canDataBeResized, canDataBeChanged, release, room, writable, foreign]

theorem resized_foreign_legacy {state : TxState} {context : SetterCtx} {length : Nat}
    (release : context.release ≠ .agave_4_3_2)
    (different : length ≠ (state.acct context.txIdx).data.length)
    (foreign : context.owned state = false) :
    canDataBeResized state context length = .error .AccountDataSizeChanged := by
  simp [canDataBeResized, release, different, foreign]

/-- Replacing data marks a touch even when the bytes are unchanged. A same-value
lamport setter, in contrast, leaves the touch metadata unchanged. -/
def touchExample : TxState :=
  initTxState [Pubkey.ofNat 10]
    [⟨1000000, [1, 2], Pubkey.ofNat 20, false, 7⟩]

def touchContext : SetterCtx :=
  { program := Pubkey.ofNat 20, txIdx := 0, writable := true }

theorem data_same_value_touches :
    (setDataFromSlice touchExample touchContext [1, 2]).map TxState.touched = .ok [0] := by
  rfl

theorem lamports_same_value_untouched :
    (setLamports touchExample touchContext 1000000).map TxState.touched = .ok [] := by
  rfl

/-- The administrative Instructions-sysvar update changes the index bytes without
manufacturing a program touch. -/
def sysvarTouchExample : TxState :=
  { initTxState [Ids.sysvarInstructions] [⟨1, [0, 0], Ids.sysvarOwner, false, 7⟩] with
    topIndex := 1 }

theorem sysvar_index_not_touched :
    (writeIxSysvarIndex sysvarTouchExample).map (fun state => ((state.acct 0).data, state.touched))
      =
      .ok ([1, 0], []) := by
  rfl

/-- The nonce classifier uses actual bytes and owner, with no environment oracle. -/
theorem nonce_current_initialized (payload : Bytes) (length : payload.length = 72) :
    isInitializedNonceAccount ⟨1, [1, 0, 0, 0, 1, 0, 0, 0] ++ payload,
      Ids.systemProgram, false, 0⟩ = true := by
  simp [isInitializedNonceAccount, slice, leNat, length]

theorem nonce_foreign_owner {account : Account} (foreign : account.owner ≠ Ids.systemProgram) :
    isInitializedNonceAccount account = false := by
  simp [isInitializedNonceAccount, foreign]

def saveMessage : Message where
  numRequiredSignatures := 1
  numReadonlySigned := 0
  numReadonlyUnsigned := 0
  staticKeys := [Pubkey.ofNat 10, Pubkey.ofNat 11]
  loadedWritable := []
  loadedReadonly := []
  recentBlockhash := List.replicate 32 0
  instructions := []

def saveTransaction : Tx where
  message := saveMessage
  fee := 10000
  loadedDataLimit := MAX_LOADED_ACCOUNTS_DATA_SIZE
  heapSize := DEFAULT_HEAP_SIZE
  nonce := none
  bankCheck := none

def savedPayer : Account := ⟨1000000, [], Ids.systemProgram, false, 7⟩
def savedOther : Account := ⟨1000000, [], Ids.systemProgram, false, 17⟩
def loadedPayer : Account := { savedPayer with lamports := 990000, rentEpoch := U64_MAX }
def loadedOther : Account := { savedOther with rentEpoch := U64_MAX }

def savedAccounts : Accounts := fun key =>
  if key = Pubkey.ofNat 10 then some savedPayer
  else if key = Pubkey.ofNat 11 then some savedOther else none

def savedResult : TxState :=
  initTxState saveMessage.keys [loadedPayer, loadedOther]

theorem untouched_example_is_writable : saveMessage.isWritable mainnet 1 = true := by decide

/-- Loading masked the rent epoch, but no mutation touched this writable account.
The original stored epoch therefore survives a successful transaction. -/
theorem commit_untouched_keeps_epoch (bank : BankEnv) :
    commitSuccess { bank with prof := mainnet } saveTransaction savedAccounts savedResult
      (Pubkey.ofNat 11) = some savedOther := by
  rfl

/-- Touching the same loaded account makes its masked rent epoch part of the save. -/
theorem commit_touched_saves_epoch (bank : BankEnv) :
    commitSuccess { bank with prof := mainnet } saveTransaction savedAccounts
      { savedResult with touched := [1] } (Pubkey.ofNat 11) = some loadedOther := by
  rfl

/-- Fee deduction is saved even when the invocation marked no account. -/
theorem commit_fee_payer_without_vm_touch (bank : BankEnv) :
    commitSuccess { bank with prof := mainnet } saveTransaction savedAccounts savedResult
      (Pubkey.ofNat 10) = some loadedPayer := by
  rfl

/-- A last instruction can extend beyond u16 range: only its start is stored
in the offset table. No arbitrary final-buffer bound is imposed. -/
theorem sysvar_last_instruction_may_be_large (profile : Profile) (data : Bytes) :
    ixSysvarOffsetsFit profile
      { saveMessage with instructions := [⟨0, [], data⟩] } = true := by
  simp [ixSysvarOffsetsFit, prefixLen]

/-- For two instructions without account metas, the second begins at
42 plus the first payload length. An unrepresentable start is rejected. -/
theorem sysvar_second_offset_overflow (profile : Profile) (data : Bytes)
    (large : 2^16 ≤ 42 + data.length) :
    ixSysvarOffsetsFit profile
      { saveMessage with instructions := [⟨0, [], data⟩, ⟨0, [], []⟩] } = false := by
  unfold ixSysvarOffsetsFit
  apply List.all_eq_false.mpr
  refine ⟨1, by simp, ?_⟩
  intro fits
  have bounded := of_decide_eq_true fits
  simp [prefixLen, ixSysvarEntry_length] at bounded
  omega

/-- The incinerator exemption of the post-execution account check does not
apply to the static fee-payer rent check of Agave4.3.2. -/
theorem fee_payer_rent_has_no_incinerator_exemption :
    feePayerRentCheck mainnet Ids.incinerator
      ⟨650240, [], Ids.systemProgram, false, 0⟩
      ⟨650239, [], Ids.systemProgram, false, 0⟩ = false := by
  rfl

/-- Sixteen input seeds leave no room for the bump. Every search attempt
fails the seed-count check, independently of the cryptographic parameters. -/
theorem findProgramAddress_full_seeds (P : Prims) (seeds : List Bytes) (pid : Pubkey)
    (h : seeds.length = MAX_SEEDS) : findProgramAddress P seeds pid = none := by
  have search : findProgramAddressBytes P.toCryptoPrimitives seeds pid.bytes = none := by
    unfold findProgramAddressBytes
    generalize 255 = n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp [findProgramAddressBytes.go, createProgramAddressBytes, h, MAX_SEEDS, ih]
  simp [findProgramAddress, search]

/-- Exhausted PDA search returns status 1 without inspecting or writing the
destination pair. This covers overlapping destinations as well. -/
theorem tryFindProgramAddress_failure (p : Profile) (P : Prims) (sv : Sysvars)
    (stake : Option Pubkey → Nat) (ctx : InvCtx) (st : InvState)
    (seeds : List Bytes) (pid : Pubkey) (address bump : Nat)
    (hcount : seeds.length ≤ MAX_SEEDS)
    (hlength : seeds.any (fun s => decide (MAX_SEED_LEN < s.length)) = false)
    (hsearch : findProgramAddress P seeds pid = none) :
    sysStep p P sv stake ctx st (.tryFindProgramAddress seeds pid address bump) =
      .ok (⟨1, []⟩, st) := by
  have search : findProgramAddressBytes P.toCryptoPrimitives seeds pid.bytes = none := by
    cases found : findProgramAddressBytes P.toCryptoPrimitives seeds pid.bytes with
    | none => rfl
    | some value => simp [findProgramAddress, found] at hsearch
  have lengths : ∀ seed ∈ seeds, seed.length ≤ MAX_SEED_LEN := by
    simpa [List.any_eq_false] using hlength
  have seedsValid : seedsOk seeds = true := by
    simp [seedsOk, hcount, List.all_eq_true]
    exact lengths
  simp [sysStep, findAddressReply, seedsValid, search]

theorem tryFindProgramAddress_exhausted_overlapping (p : Profile) (P : Prims) (sv : Sysvars)
    (stake : Option Pubkey → Nat) (ctx : InvCtx) (st : InvState)
    (pid : Pubkey) (destination : Nat) :
    sysStep p P sv stake ctx st
      (.tryFindProgramAddress (List.replicate MAX_SEEDS []) pid destination destination) =
      .ok (⟨1, []⟩, st) := by
  apply tryFindProgramAddress_failure
  · simp
  · simp
  · apply findProgramAddress_full_seeds
    simp

/-- A separate durable nonce retains the rent epoch of the validated payer,
rather than restoring the epoch from storage. -/
theorem rollback_separate_nonce_payer_epoch {tx : Tx} {accounts : Accounts} {payer adv : Account}
    {address : Pubkey} (hkey : tx.payerKey ≠ address) (hlamports : payer.lamports ≠ 0) :
    ((commitRollback tx accounts payer (some (address, adv))) tx.payerKey).map Account.rentEpoch =
      some payer.rentEpoch := by
  simp [commitRollback, storeAccount, hkey, Ne.symm hkey, hlamports]

/-- When the payer itself is the durable nonce, rollback retains its
validated rent epoch and copies only the advanced nonce data. -/
theorem rollback_same_nonce_payer {tx : Tx} {accounts : Accounts} {payer adv : Account}
    (hlamports : payer.lamports ≠ 0) :
    (commitRollback tx accounts payer (some (tx.payerKey, adv))) tx.payerKey =
      some { payer with data := adv.data } := by
  simp [commitRollback, storeAccount, hlamports]

/-- Ordinary failed transactions still restore the previously loaded epoch. -/
theorem rollback_without_nonce_epoch {tx : Tx} {accounts : Accounts} {payer stored : Account}
    (hstored : accounts tx.payerKey = some stored)
    (hlamports : payer.lamports ≠ 0) :
    ((commitRollback tx accounts payer none) tx.payerKey).map Account.rentEpoch =
      some stored.rentEpoch := by
  simp [commitRollback, hstored, storeAccount, hlamports]

end SolanalibTest.Runtime
