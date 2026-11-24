/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Runtime.TransactionSuccess

@[expose] public section

/-!
A closed execution-error transaction with a real intermediate mutation. The first
System instruction transfers 100,000 lamports. The second requests 3,000,000 from
the same sender and fails for insufficient funds. Transaction rollback discards
the completed transfer and retains only the 5,000-lamport fee.

The fixture reuses the concrete mainnet bank and accounts of `TransactionSuccess`.
Admission, recent-blockhash membership and fee/resource inputs retain the same
documented bank boundary. Both System instructions are interpreted; no successful
external program execution is assumed.
-/

open Solanalib.Runtime

namespace SolanalibTest.Runtime.TransactionRollbackTest

open TransactionSuccessTest

def failingAmount : Nat := 3000000

def failingInstruction : CompiledIx :=
  ⟨2, [0, 1], u32le 2 ++ u64le failingAmount⟩

def rollbackMessage : Message :=
  { message with instructions := [instruction, failingInstruction] }

def rollbackTx : Tx := { tx with message := rollbackMessage }

def failingFrame : Frame :=
  { programIdx := 2, accounts := [⟨0, true, true⟩, ⟨1, false, true⟩],
    data := failingInstruction.data }

/-- The already-mutated transaction state at entry to the second instruction. -/
def secondPushed : TxState :=
  { post with
    stack := [failingFrame]
    trace := post.trace ++ [⟨1, failingFrame⟩] }

def failure : TxError := .InstructionError 1 (.Custom 1)

/-- Ordinary rollback restores stored metadata and retains the fee debit. -/
def rollbackSender : Account :=
  { senderAccount with lamports := senderAccount.lamports - rollbackTx.fee }

def rollbackAccounts : Accounts := commitRollback rollbackTx accounts loadedSender none

theorem rollback_message_well_formed : rollbackMessage.WF mainnet := by
  simp [Message.WF, rollbackMessage, message, Message.keys, instruction, failingInstruction,
    mainnet, mainnetFeatures, Profile.maxTxAccountLocks]
  decide

theorem rollback_world_well_formed : (bank.world rollbackTx).WF :=
  BankEnv.world_wf bank_well_formed rollbackTx

/-- The two instructions have ordinary header, index, byte-width and resource bounds. -/
theorem rollback_transaction_bounds :
    rollbackTx.message.numReadonlySigned < rollbackTx.message.numRequiredSignatures ∧
    rollbackTx.message.numRequiredSignatures + rollbackTx.message.numReadonlyUnsigned ≤
      rollbackTx.message.staticKeys.length ∧
    rollbackTx.message.staticKeys.length = 3 ∧
    rollbackTx.message.recentBlockhash.length = 32 ∧
    rollbackTx.message.instructions.length = 2 ∧
    failingInstruction.programIdIndex = 2 ∧ failingInstruction.accounts = [0, 1] ∧
    failingInstruction.data.length = 12 ∧
    0 < rollbackTx.fee ∧ rollbackTx.fee < U64_LIMIT ∧
    0 < failingAmount ∧ failingAmount < U64_LIMIT ∧
    rollbackTx.heapSize = 32768 ∧ rollbackTx.loadedDataLimit = 67108864 := by
  decide

theorem rollback_frame_privileges :
    rollbackMessage.frames mainnet = [frame, failingFrame] := by
  rfl

theorem failing_frame_flags_consistent : failingFrame.FlagsConsistent := by
  intro a memberA b memberB same
  simp only [failingFrame, List.mem_cons, List.not_mem_nil, or_false] at memberA memberB
  rcases memberA with rfl | rfl <;> rcases memberB with rfl | rfl <;> simp_all

theorem rollback_nonce_admitted : validateNonce bank accounts rollbackTx = .ok none := by
  rfl

theorem rollback_fee_payer_validated :
    validateFeePayer bank accounts rollbackTx = .ok loadedSender := by
  rfl

theorem rollback_load_size : loadedSize bank accounts rollbackTx = 206 := by rfl

theorem rollback_load_checked : checkLoad bank accounts rollbackTx = .ok () := by rfl

theorem rollback_accounts_loaded :
    loadedAccounts bank accounts rollbackTx loadedSender = loaded := by
  rfl

/-- The closed first-instruction proof uses the checked System debit and credit. -/
theorem first_instruction_executed :
    ProcInstr (bank.world rollbackTx) initial frame (.ok post) :=
  instruction_executed

/-- The successful prefix has actually changed both balances before the later failure. -/
theorem first_instruction_mutates :
    ProcMessage (bank.world rollbackTx) rollbackTx.allData initial [frame] 0 (.ok post) ∧
    (initial.acct 0).lamports = 2995000 ∧ (initial.acct 1).lamports = 1000000 ∧
    (post.acct 0).lamports = 2895000 ∧ (post.acct 1).lamports = 1100000 ∧
    (post.acct 0).lamports ≠ (initial.acct 0).lamports ∧
    (post.acct 1).lamports ≠ (initial.acct 1).lamports ∧ post.touched = [1, 0] := by
  refine ⟨ProcMessage.instr (by rfl) first_instruction_executed ProcMessage.nil,
    rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩ <;> decide

theorem intermediate_accounts_well_formed :
    ∀ account ∈ post.accts, account.WF := by
  intro account present
  change account ∈ [senderAfter, recipientAfter, systemAccount] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl
  · exact account_bounds.2.2.2.2.2.1
  · exact account_bounds.2.2.2.2.2.2
  · exact account_bounds.2.2.1

theorem second_instruction_pushed : push mainnet post failingFrame = .ok secondPushed := by
  rfl

theorem second_system_dispatched :
    dispatch (bank.world rollbackTx) (resetReturnData secondPushed) failingFrame =
      .builtin .system := by
  rfl

theorem second_transfer_decoded (prims : Prims) :
    decodeSystemIx prims failingInstruction.data = some (.transfer failingAmount) := by
  rfl

/-- The failing amount is representable, but exceeds the actual intermediate balance. -/
theorem second_transfer_insufficient :
    (post.acct 0).lamports < failingAmount ∧ failingAmount < U64_LIMIT ∧
    (post.acct 0).data = [] ∧ failingFrame.accounts =
      [⟨0, true, true⟩, ⟨1, false, true⟩] := by
  decide

set_option maxRecDepth 16384 in
/-- The concrete System transfer rejects insufficient funds without using primitives. -/
theorem second_system_fails (prims : Prims) :
    systemProcess mainnet prims (resetReturnData secondPushed) failingFrame =
      some (.error (.Custom 1)) := by
  cbv

theorem second_instruction_failed :
    ProcInstr (bank.world rollbackTx) post failingFrame (.error (.Custom 1)) := by
  have executed : ProcInstr (bank.world rollbackTx) post failingFrame
      (afterProgram (.error (.Custom 1))) :=
    Exec.run second_instruction_pushed
      (Exec.system second_system_dispatched (second_system_fails bank.prims))
  simpa only [afterProgram] using executed

/-- Processing reaches the second instruction only after the first transfer completes. -/
theorem message_executes_then_fails :
    ProcMessage (bank.world rollbackTx) rollbackTx.allData initial
      (rollbackMessage.frames mainnet) 0 (.error failure) := by
  rw [rollback_frame_privileges]
  exact ProcMessage.instr (by rfl) first_instruction_executed
    (ProcMessage.instrFail (by rfl) second_instruction_failed)

theorem transaction_execution_failed : Execute bank rollbackTx loaded (.error failure) :=
  Execute.fail message_executes_then_fails

/-- Admission, fee validation and loading all pass; execution fails at instruction index 1. -/
theorem transaction_rolls_back :
    ProcTx bank accounts rollbackTx rollbackAccounts (.executed (.error failure)) := by
  apply ProcTx.executedErr (payer := loadedSender) (nonce := none)
  · rfl
  · exact rollback_nonce_admitted
  · exact rollback_fee_payer_validated
  · exact rollback_load_checked
  · rw [rollback_accounts_loaded]
    exact transaction_execution_failed

theorem rollback_stores :
    rollbackAccounts = storeAccount accounts senderKey rollbackSender := by
  rfl

/-- The fee payer changes only in balance; every other stored field is restored. -/
theorem rollback_sender_fields :
    rollbackSender.lamports + rollbackTx.fee = senderAccount.lamports ∧
    rollbackSender.data = senderAccount.data ∧ rollbackSender.owner = senderAccount.owner ∧
    rollbackSender.executable = senderAccount.executable ∧
    rollbackSender.rentEpoch = senderAccount.rentEpoch := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem rollback_committed_accounts :
    rollbackAccounts senderKey = some rollbackSender ∧
    rollbackAccounts recipientKey = accounts recipientKey ∧
    rollbackAccounts Ids.systemProgram = accounts Ids.systemProgram := by
  exact ⟨rfl, rfl, rfl⟩

/-- These are committed balances, after discarding the completed transfer. -/
theorem rollback_committed_balances :
    (accounts senderKey).map Account.lamports = some 3000000 ∧
    (rollbackAccounts senderKey).map Account.lamports = some 2995000 ∧
    (accounts recipientKey).map Account.lamports = some 1000000 ∧
    (rollbackAccounts recipientKey).map Account.lamports = some 1000000 ∧
    rollbackTx.fee = 5000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Neither actual execution write is committed; the ordinary rollback restores rent epochs. -/
theorem execution_writes_discarded :
    rollbackAccounts senderKey ≠ some (post.acct 0) ∧
    rollbackAccounts recipientKey ≠ some (post.acct 1) ∧
    rollbackSender.lamports = (post.acct 0).lamports + transferAmount ∧
    (post.acct 1).lamports = recipientAccount.lamports + transferAmount ∧
    (rollbackAccounts senderKey).map Account.rentEpoch = some 0 ∧
    (rollbackAccounts recipientKey).map Account.rentEpoch = some 0 := by
  decide

theorem other_accounts_unchanged (key : Pubkey) (not_sender : key ≠ senderKey) :
    rollbackAccounts key = accounts key := by
  rw [rollback_stores]
  simp [storeAccount, not_sender]

theorem rollback_sender_well_formed : rollbackSender.WF := by
  unfold Account.WF
  decide

theorem rollback_accounts_well_formed :
    ∀ key account, rollbackAccounts key = some account → account.WF := by
  intro key account present
  by_cases sender : key = senderKey
  · subst key
    rw [rollback_committed_accounts.1] at present
    exact (Option.some.inj present) ▸ rollback_sender_well_formed
  · rw [other_accounts_unchanged key sender] at present
    exact accounts_well_formed key account present

/-- A closed witness combining real intermediate writes, execution failure and fee-only effects. -/
theorem execution_rollback_exists :
    ∃ (B : BankEnv) (before after : Accounts) (transaction : Tx) (middle : TxState),
      B.prof = mainnet ∧ B.WF ∧ transaction.message.WF B.prof ∧
      (∀ key account, before key = some account → account.WF) ∧
      (∀ key account, after key = some account → account.WF) ∧
      (∀ account ∈ middle.accts, account.WF) ∧
      transaction.message.instructions = [instruction, failingInstruction] ∧
      transaction.fee = 5000 ∧
      ProcMessage (B.world transaction) transaction.allData
        (initTxState transaction.message.keys
          (loadedAccounts B before transaction loadedSender)) [frame] 0 (.ok middle) ∧
      (middle.acct 0).lamports = 2895000 ∧ (middle.acct 1).lamports = 1100000 ∧
      ProcTx B before transaction after (.executed (.error (.InstructionError 1 (.Custom 1)))) ∧
      (before senderKey).map Account.lamports = some 3000000 ∧
      (after senderKey).map Account.lamports = some 2995000 ∧
      (before recipientKey).map Account.lamports = some 1000000 ∧
      (after recipientKey).map Account.lamports = some 1000000 ∧
      (∀ key, key ≠ senderKey → after key = before key) := by
  refine ⟨bank, accounts, rollbackAccounts, rollbackTx, post, rfl, bank_well_formed,
    rollback_message_well_formed, accounts_well_formed, rollback_accounts_well_formed,
    intermediate_accounts_well_formed, rfl, rfl, ?_, rfl, rfl, transaction_rolls_back,
    rfl, rfl, rfl, rfl, other_accounts_unchanged⟩
  rw [rollback_accounts_loaded]
  exact first_instruction_mutates.1

end SolanalibTest.Runtime.TransactionRollbackTest
