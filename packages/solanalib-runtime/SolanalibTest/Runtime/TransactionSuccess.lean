/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Transaction

@[expose] public section

/-!
A closed successful transaction: one System transfer of 100,000 lamports with a
5,000-lamport fee. The mainnet profile, account checks, instruction push and pop,
System builtin, post-execution checks and touched-account commit are exercised.

The bank supplies admission, recent-blockhash and fee inputs at the documented
transaction boundary. This witness does not prove signature verification or
correspondence with a deployed bank. The primitive functions below inhabit the
unused fields of this closed fixture; the transfer is also proved for arbitrary
primitives and does not rely on a supplied successful program execution.
-/

open Solanalib.Runtime

namespace SolanalibTest.Runtime.TransactionSuccessTest

/-- The public key of RFC 8032, Ed25519 test 1. -/
def senderKey : Pubkey :=
  ⟨[0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7,
    0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64, 0x07, 0x3a,
    0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25,
    0xaf, 0x02, 0x1a, 0x68, 0xf7, 0x07, 0x51, 0x1a], rfl⟩

/-- The public key of RFC 8032, Ed25519 test 2. -/
def recipientKey : Pubkey :=
  ⟨[0x3d, 0x40, 0x17, 0xc3, 0xe8, 0x43, 0x89, 0x5a,
    0x92, 0xb7, 0x0a, 0xa7, 0x4d, 0x1b, 0x7e, 0xbc,
    0x9c, 0x98, 0x2c, 0xcf, 0x2e, 0xc4, 0x96, 0x8c,
    0xc0, 0xcd, 0x55, 0xf1, 0x2a, 0xf4, 0x66, 0x0c], rfl⟩

def recentBlockhash : Pubkey := Pubkey.ofNat 700
def transferAmount : Nat := 100000

def senderAccount : Account :=
  { lamports := 3000000, data := [], owner := Ids.systemProgram,
    executable := false, rentEpoch := 0 }

def recipientAccount : Account :=
  { lamports := 1000000, data := [], owner := Ids.systemProgram,
    executable := false, rentEpoch := 0 }

/-- The native System builtin account, with the bytes of `system_program`. -/
def systemAccount : Account :=
  { lamports := 1,
    data := [115, 121, 115, 116, 101, 109, 95, 112, 114, 111, 103, 114, 97, 109],
    owner := Ids.nativeLoader, executable := true, rentEpoch := 0 }

def accounts : Accounts := fun key =>
  if key = senderKey then some senderAccount
  else if key = recipientKey then some recipientAccount
  else if key = Ids.systemProgram then some systemAccount
  else none

def instruction : CompiledIx :=
  ⟨2, [0, 1], u32le 2 ++ u64le transferAmount⟩

def message : Message :=
  { numRequiredSignatures := 1, numReadonlySigned := 0, numReadonlyUnsigned := 1,
    staticKeys := [senderKey, recipientKey, Ids.systemProgram],
    loadedWritable := [], loadedReadonly := [], recentBlockhash := recentBlockhash.bytes,
    instructions := [instruction] }

def tx : Tx :=
  { message := message, fee := 5000, loadedDataLimit := MAX_LOADED_ACCOUNTS_DATA_SIZE,
    heapSize := DEFAULT_HEAP_SIZE, nonce := none, bankCheck := none }

/-- Unused primitive fields. No hash, curve, precompile or VM call occurs here. -/
def primitives : Prims where
  sha256 := fun _ => List.replicate 32 0
  onCurve := fun _ => false
  keccak256 := fun _ => List.replicate 32 0
  blake3 := fun _ => List.replicate 32 0
  sha512 := fun _ => List.replicate 64 0
  sha256_length := fun _ => List.length_replicate
  keccak256_length := fun _ => List.length_replicate
  blake3_length := fun _ => List.length_replicate
  sha512_length := fun _ => List.length_replicate
  isUtf8 := fun _ => false
  secp256k1Recover := fun _ _ _ => .error 2
  poseidon := fun _ _ _ => none
  curveValidate := fun _ _ => false
  curveGroupOp := fun _ _ _ _ => none
  curveMultiscalarMul := fun _ _ _ => none
  curveDecompress := fun _ _ => none
  curvePairingMap := fun _ _ _ => none
  altBn128GroupOp := fun _ _ => none
  altBn128Compression := fun _ _ => none
  bigModExp := fun _ _ _ => []
  bigModExpLe := fun _ _ _ => none
  precompileVerify := fun _ _ _ => some 1

def clock : Clock :=
  ⟨462908421, 1793100000, 1071, 1072, 1793260000⟩

def epochSchedule : EpochSchedule := ⟨432000, 432000, false, 0, 0⟩

def sysvarData : Pubkey → Option Bytes := fun key =>
  if key = Ids.sysvarClock then some clock.encode
  else if key = Ids.sysvarRent then some mainnet.rent.toSysvar.bincode
  else if key = Ids.sysvarEpochSchedule then some epochSchedule.bincode
  else none

def sysvars : Sysvars :=
  { clock := clock, epochSchedule := epochSchedule, rent := mainnet.rent.toSysvar,
    epochRewards := none, lastRestartSlot := none, feesLamportsPerSignature := 5000,
    data := sysvarData }

def bank : BankEnv :=
  { prof := mainnet, prims := primitives, sysvars := sysvars,
    epochStake := fun _ => 0, builtins := builtinTable (fun _ => false),
    programs := fun _ => .notDeployed, extraLoadedSize := fun _ => 0,
    isRecentBlockhash := fun hash => decide (hash = recentBlockhash.bytes),
    environmentBlockhash := recentBlockhash, nextLamportsPerSignature := 5000,
    strictNonceSizeCheck := true }

theorem sysvars_well_formed : sysvars.WF := by
  refine ⟨⟨clock.encode, rfl, ?_⟩,
    ⟨mainnet.rent.toSysvar.bincode, rfl, ?_⟩,
    ⟨epochSchedule.bincode, rfl, ?_⟩, ?_⟩
  · exact List.prefix_refl _
  · exact List.prefix_refl _
  · exact List.prefix_refl _
  · intro key outside
    have clock_ne : key ≠ Ids.sysvarClock := by
      intro same
      exact outside (by simp [cachedSysvarIds, same])
    have rent_ne : key ≠ Ids.sysvarRent := by
      intro same
      exact outside (by simp [cachedSysvarIds, same])
    have schedule_ne : key ≠ Ids.sysvarEpochSchedule := by
      intro same
      exact outside (by simp [cachedSysvarIds, same])
    simp [sysvars, sysvarData, clock_ne, rent_ne, schedule_ne]

theorem bank_well_formed : bank.WF :=
  ⟨mainnet_wf, sysvars_well_formed, rfl, builtinTable_wf _⟩

theorem world_well_formed : (bank.world tx).WF :=
  BankEnv.world_wf bank_well_formed tx

theorem message_well_formed : message.WF mainnet := by
  simp [Message.WF, message, Message.keys, instruction, mainnet, mainnetFeatures,
    Profile.maxTxAccountLocks]
  decide

/-- Concrete header and width constraints in addition to the partial `Message.WF`. -/
theorem transaction_bounds :
    tx.message.numReadonlySigned < tx.message.numRequiredSignatures ∧
    tx.message.numRequiredSignatures + tx.message.numReadonlyUnsigned ≤
      tx.message.staticKeys.length ∧
    tx.message.staticKeys.length ≤ 256 ∧
    tx.message.recentBlockhash.length = 32 ∧
    tx.message.instructions.length = 1 ∧
    instruction.programIdIndex = 2 ∧ instruction.accounts = [0, 1] ∧
    instruction.data.length = 12 ∧
    0 < tx.fee ∧ tx.fee < U64_LIMIT ∧
    0 < transferAmount ∧ transferAmount < U64_LIMIT ∧
    tx.heapSize = 32768 ∧ tx.loadedDataLimit = 67108864 := by
  decide

/-- The scalar sysvars fit their runtime integer representations. -/
theorem sysvar_widths :
    clock.slot < U64_LIMIT ∧ clock.epoch < U64_LIMIT ∧
    clock.leaderScheduleEpoch < U64_LIMIT ∧
    -(2^63 : Int) ≤ clock.epochStartTimestamp ∧ clock.epochStartTimestamp < 2^63 ∧
    -(2^63 : Int) ≤ clock.unixTimestamp ∧ clock.unixTimestamp < 2^63 ∧
    epochSchedule.slotsPerEpoch < U64_LIMIT ∧
    epochSchedule.leaderScheduleSlotOffset < U64_LIMIT ∧
    epochSchedule.firstNormalEpoch < U64_LIMIT ∧
    epochSchedule.firstNormalSlot < U64_LIMIT ∧
    sysvars.feesLamportsPerSignature < U64_LIMIT := by
  decide

/-- The clock uses the slot and epoch of the selected profile, without epoch warmup. -/
theorem clock_epoch_fields :
    clock.slot = mainnet.slot ∧ epochSchedule.warmup = false ∧
    clock.epoch = clock.slot / epochSchedule.slotsPerEpoch ∧
    clock.leaderScheduleEpoch = clock.epoch + 1 ∧
    clock.epochStartTimestamp ≤ clock.unixTimestamp := by
  decide

def loadedSender : Account :=
  { senderAccount with lamports := senderAccount.lamports - tx.fee, rentEpoch := U64_MAX }

def loadedRecipient : Account := { recipientAccount with rentEpoch := U64_MAX }

def loaded : List Account := [loadedSender, loadedRecipient, systemAccount]

def initial : TxState := initTxState message.keys loaded

def frame : Frame :=
  { programIdx := 2, accounts := [⟨0, true, true⟩, ⟨1, false, true⟩],
    data := instruction.data }

def pushed : TxState := { initial with stack := [frame], trace := [⟨1, frame⟩] }

def senderAfter : Account :=
  { loadedSender with lamports := loadedSender.lamports - transferAmount }

def recipientAfter : Account :=
  { loadedRecipient with lamports := loadedRecipient.lamports + transferAmount }

def debited : TxState :=
  { pushed with
    accts := [senderAfter, loadedRecipient, systemAccount]
    lamportsDelta := -(transferAmount : Int)
    returnData := (Ids.systemProgram, [])
    touched := [0] }

def afterTransfer : TxState :=
  { pushed with
    accts := [senderAfter, recipientAfter, systemAccount]
    returnData := (Ids.systemProgram, [])
    touched := [1, 0] }

def post : TxState := { afterTransfer with stack := [], topIndex := 1 }

def committed : Accounts := commitSuccess bank tx accounts post

theorem account_bounds :
    senderAccount.WF ∧ recipientAccount.WF ∧ systemAccount.WF ∧
    loadedSender.WF ∧ loadedRecipient.WF ∧ senderAfter.WF ∧ recipientAfter.WF := by
  unfold Account.WF
  decide

theorem balance_bounds :
    tx.fee + transferAmount ≤ senderAccount.lamports ∧
    recipientAccount.lamports + transferAmount < U64_LIMIT ∧
    mainnet.rent.minBalance 0 = 650240 ∧
    mainnet.rent.minBalance 0 ≤ senderAfter.lamports ∧
    mainnet.rent.minBalance 0 ≤ recipientAccount.lamports ∧
    initial.lamportSum < 2^128 ∧
    -(2^127 : Int) < -(transferAmount : Int) ∧ (transferAmount : Int) < 2^127 := by
  decide

theorem frame_privileges : message.frames mainnet = [frame] := by rfl

theorem frame_flags_consistent : frame.FlagsConsistent := by
  intro a memberA b memberB same
  simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at memberA memberB
  rcases memberA with rfl | rfl <;> rcases memberB with rfl | rfl <;> simp_all

theorem nonce_admitted : validateNonce bank accounts tx = .ok none := by rfl

theorem fee_payer_validated : validateFeePayer bank accounts tx = .ok loadedSender := by
  rfl

theorem load_size : loadedSize bank accounts tx = 206 := by
  rfl

theorem load_checked : checkLoad bank accounts tx = .ok () := by
  rfl

theorem accounts_loaded : loadedAccounts bank accounts tx loadedSender = loaded := by
  rfl

theorem instruction_pushed : push mainnet initial frame = .ok pushed := by rfl

theorem system_dispatched :
    dispatch (bank.world tx) (resetReturnData pushed) frame = .builtin .system := by
  rfl

/-- The decoded transfer branch does not use any supplied primitive. -/
theorem transfer_decoded (prims : Prims) :
    decodeSystemIx prims instruction.data = some (.transfer transferAmount) := by rfl

def systemContext : SysCtx := ⟨resetReturnData pushed, frame, mainnet.release⟩

set_option maxRecDepth 16384 in
theorem sender_debited :
    checkedSubLamports (resetReturnData pushed)
      (systemContext.sc (resetReturnData pushed) 0) transferAmount = .ok debited := by
  cbv

set_option maxRecDepth 16384 in
theorem recipient_credited :
    checkedAddLamports debited (systemContext.sc debited 1) transferAmount =
      .ok afterTransfer := by
  cbv

set_option maxRecDepth 16384 in
/-- Both checked lamport setters execute; no successful builtin result is assumed. -/
theorem system_transfer_runs (prims : Prims) :
    systemProcess mainnet prims (resetReturnData pushed) frame = some (.ok afterTransfer) := by
  cbv

theorem instruction_popped : afterProgram (.ok afterTransfer) = .ok post := by rfl

theorem instruction_executed :
    ProcInstr (bank.world tx) initial frame (.ok post) := by
  have executed :
      ProcInstr (bank.world tx) initial frame (afterProgram (.ok afterTransfer)) :=
    Exec.run instruction_pushed (Exec.system system_dispatched (system_transfer_runs bank.prims))
  simpa only [instruction_popped] using executed

theorem message_executed :
    ProcMessage (bank.world tx) tx.allData initial (message.frames mainnet) 0 (.ok post) := by
  rw [frame_privileges]
  exact ProcMessage.instr (by rfl) instruction_executed ProcMessage.nil

theorem rent_checked : rentCheckAll mainnet message loaded post.accts = .ok () := by rfl

theorem execution_balance_preserved : post.lamportSum = initial.lamportSum := by rfl

theorem transaction_executed : Execute bank tx loaded (.ok post) :=
  Execute.ok message_executed rent_checked execution_balance_preserved

/-- The full success constructor, including ordinary admission, fee debit and loading. -/
theorem transaction_succeeds :
    ProcTx bank accounts tx committed (.executed (.ok ())) := by
  apply ProcTx.executedOk (payer := loadedSender) (post := post) (nonce := none)
  · rfl
  · exact nonce_admitted
  · exact fee_payer_validated
  · exact load_checked
  · rw [accounts_loaded]
    exact transaction_executed

theorem execution_metadata :
    post.stack = [] ∧ post.trace = [⟨1, frame⟩] ∧ post.topIndex = 1 ∧
    post.lamportsDelta = 0 ∧ post.resizeDelta = 0 ∧ post.touched = [1, 0] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The recipient is saved by its real setter touch; the readonly program is not saved. -/
theorem commit_eligibility :
    savesAccount bank tx post 0 = true ∧ savesAccount bank tx post 1 = true ∧
    savesAccount bank tx post 2 = false := by
  decide

theorem committed_accounts :
    committed senderKey = some senderAfter ∧
    committed recipientKey = some recipientAfter ∧
    committed Ids.systemProgram = accounts Ids.systemProgram := by
  exact ⟨rfl, rfl, rfl⟩

theorem committed_balances :
    (committed senderKey).map Account.lamports = some 2895000 ∧
    (committed recipientKey).map Account.lamports = some 1100000 ∧
    senderAfter.lamports + tx.fee + transferAmount = senderAccount.lamports ∧
    recipientAfter.lamports = recipientAccount.lamports + transferAmount := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem outside_accounts_unchanged (key : Pubkey)
    (not_sender : key ≠ senderKey) (not_recipient : key ≠ recipientKey) :
    committed key = accounts key := by
  have stores : committed =
      storeAccount (storeAccount accounts senderKey senderAfter) recipientKey recipientAfter := by
    rfl
  rw [stores]
  simp [storeAccount, not_sender, not_recipient]

theorem accounts_well_formed :
    ∀ key account, accounts key = some account → account.WF := by
  intro key account present
  unfold accounts at present
  split at present
  · cases present
    exact account_bounds.1
  · split at present
    · cases present
      exact account_bounds.2.1
    · split at present
      · cases present
        exact account_bounds.2.2.1
      · cases present

theorem committed_well_formed :
    ∀ key account, committed key = some account → account.WF := by
  intro key account present
  by_cases sender : key = senderKey
  · subst key
    rw [committed_accounts.1] at present
    exact (Option.some.inj present) ▸ account_bounds.2.2.2.2.2.1
  · by_cases recipient : key = recipientKey
    · subst key
      rw [committed_accounts.2.1] at present
      exact (Option.some.inj present) ▸ account_bounds.2.2.2.2.2.2
    · rw [outside_accounts_unchanged key sender recipient] at present
      exact accounts_well_formed key account present

/-- A closed non-vacuity witness, with a real instruction, fee and committed balance changes. -/
theorem successful_transaction_exists :
    ∃ (B : BankEnv) (before after : Accounts) (transaction : Tx),
      B.prof = mainnet ∧ B.WF ∧ transaction.message.WF B.prof ∧
      (∀ key account, before key = some account → account.WF) ∧
      (∀ key account, after key = some account → account.WF) ∧
      transaction.message.instructions ≠ [] ∧ 0 < transaction.fee ∧
      ProcTx B before transaction after (.executed (.ok ())) ∧
      (before senderKey).map Account.lamports = some 3000000 ∧
      (after senderKey).map Account.lamports = some 2895000 ∧
      (before recipientKey).map Account.lamports = some 1000000 ∧
      (after recipientKey).map Account.lamports = some 1100000 := by
  exact ⟨bank, accounts, committed, tx, rfl, bank_well_formed, message_well_formed,
    accounts_well_formed, committed_well_formed, by decide, by decide,
    transaction_succeeds, rfl, committed_balances.1, rfl, committed_balances.2.1⟩

end SolanalibTest.Runtime.TransactionSuccessTest
