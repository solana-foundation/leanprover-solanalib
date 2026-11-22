/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Runtime.TransactionSuccess

@[expose] public section

/-!
Loader-v3 cache regressions on the mainnet profile. The close fixture starts with
an empty transaction overlay and a loaded program, performs the ProgramData
account setters through the opaque builtin contract, and then invokes that
program. The cache write is required by `Exec.loaderV3`; it is not supplied in
the initial state or assumed as a final execution result.

The loader account operations remain an explicit opaque behavior. These tests
do not verify loader authority validation, executable bytes or deployed-bank
correspondence. Deploy, Upgrade and ExtendProgram controls below check their
mandatory cache-effect classification, without claiming successful deployment.
The reusable mainnet bank fixture supplies unused primitive fields.
-/

set_option maxRecDepth 32768

open Solanalib.Runtime

namespace SolanalibTest.Runtime.ProgramCacheTest

def programKey : Pubkey := Pubkey.ofNat 10
def programDataKey : Pubkey := Pubkey.ofNat 11
def recipientKey : Pubkey := Pubkey.ofNat 12
def authorityKey : Pubkey := TransactionSuccessTest.senderKey

def zeroProgram : Program := fun _ run => run = ⟨[], .exit 0⟩

def programAccount : Account :=
  ⟨2000000, u32le 2 ++ programDataKey.bytes, Ids.bpfLoaderUpgradeable, true, U64_MAX⟩

def programDataAccount : Account :=
  ⟨2000000, u32le 3 ++ u64le (mainnet.slot - 1) ++ [1] ++ authorityKey.bytes ++
    List.replicate 64 0, Ids.bpfLoaderUpgradeable, false, U64_MAX⟩

def recipientAccount : Account :=
  ⟨1000000, [], Ids.systemProgram, false, U64_MAX⟩

def loaderAccount : Account :=
  ⟨1000000, [], Ids.nativeLoader, true, U64_MAX⟩

def accounts : Accounts := fun key =>
  if key = authorityKey then some TransactionSuccessTest.senderAccount
  else if key = programKey then some programAccount
  else if key = programDataKey then some programDataAccount
  else if key = recipientKey then some recipientAccount
  else if key = Ids.bpfLoaderUpgradeable then some loaderAccount
  else none

def closeInstruction : CompiledIx := ⟨4, [2, 3, 0, 1], u32le 5⟩
def callInstruction : CompiledIx := ⟨1, [], []⟩

def closeMessage : Message :=
  { numRequiredSignatures := 1, numReadonlySigned := 0, numReadonlyUnsigned := 1,
    staticKeys := [authorityKey, programKey, programDataKey, recipientKey,
      Ids.bpfLoaderUpgradeable],
    loadedWritable := [], loadedReadonly := [],
    recentBlockhash := TransactionSuccessTest.recentBlockhash.bytes,
    instructions := [closeInstruction] }

def failedMessage : Message :=
  { closeMessage with instructions := [closeInstruction, callInstruction] }

def closeTx : Tx := { TransactionSuccessTest.tx with message := closeMessage }
def failedTx : Tx := { closeTx with message := failedMessage }

def bank : BankEnv :=
  { TransactionSuccessTest.bank with
    builtins := builtinTable (· == Ids.bpfLoaderUpgradeable)
    programs := fun _ => .sbf zeroProgram }

def world : World := bank.world closeTx

def loadedPayer : Account :=
  { TransactionSuccessTest.senderAccount with lamports := 2995000, rentEpoch := U64_MAX }

def loaded : List Account :=
  [loadedPayer, programAccount, programDataAccount, recipientAccount, loaderAccount]

def initial : TxState := initTxState closeMessage.keys loaded

def closeFrame : Frame :=
  ⟨4, [⟨2, false, true⟩, ⟨3, false, true⟩, ⟨0, true, true⟩, ⟨1, false, true⟩], u32le 5⟩

def callFrame : Frame := ⟨1, [], []⟩

def setter (index : Nat) : SetterCtx :=
  ⟨Ids.bpfLoaderUpgradeable, index, true, .agave_4_3_2⟩

/-- Computed fixture states; the execution proofs check each successful result. -/
def stateOf (result : Except InstrError TxState) : TxState := result.toOption.getD initial

def entered : TxState := stateOf (push mainnet initial closeFrame)
def beforeClose : TxState := resetReturnData entered
def shortened : TxState := stateOf (setDataLength beforeClose (setter 2) 4)
def credited : TxState := stateOf (setLamports shortened (setter 3) 3000000)
def debited : TxState := stateOf (setLamports credited (setter 2) 0)
def closedData : TxState := stateOf (setDataFromSlice debited (setter 2) (u32le 0))
def finished : TxState := applyLoaderV3Effect mainnet.slot beforeClose closeFrame closedData
def closed : TxState := stateOf (pop finished)
def callEntered : TxState := stateOf (push mainnet closed callFrame)
def callRunning : TxState := resetReturnData callEntered

theorem bank_well_formed : bank.WF :=
  ⟨mainnet_wf, TransactionSuccessTest.sysvars_well_formed, rfl, builtinTable_wf _⟩

theorem clock_matches_profile : world.sysvars.clock.slot = world.prof.slot := rfl

theorem close_message_well_formed : closeMessage.WF mainnet := by
  simp [Message.WF, closeMessage, Message.keys, closeInstruction, mainnet, mainnetFeatures,
    Profile.maxTxAccountLocks]
  decide

theorem failed_message_well_formed : failedMessage.WF mainnet := by
  simp [Message.WF, failedMessage, closeMessage, Message.keys, closeInstruction,
    callInstruction, mainnet, mainnetFeatures, Profile.maxTxAccountLocks]
  decide

theorem frame_privileges :
    closeMessage.frames mainnet = [closeFrame] ∧
    failedMessage.frames mainnet = [closeFrame, callFrame] := ⟨rfl, rfl⟩

theorem consistent_flags : closeFrame.FlagsConsistent ∧ callFrame.FlagsConsistent := by
  simp [Frame.FlagsConsistent, closeFrame, callFrame]

theorem initial_accounts_well_formed : ∀ account ∈ initial.accts, account.WF := by
  simp only [initial, initTxState, loaded, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Account.WF]
  decide

theorem distinct_keys : initial.keys.Nodup := by decide

theorem initial_cache_empty : initial.modifiedPrograms = [] := rfl

theorem initial_program_loaded : dispatch world initial callFrame = .sbf .v1 zeroProgram := rfl

theorem close_classified :
    loaderV3CacheEffect mainnet.slot beforeClose closeFrame =
      some (programKey, .closed mainnet.slot) := rfl

/-- Closing overwrites the header, so classification must read the original state. -/
theorem closed_header_no_longer_classifies :
    loaderV3CacheEffect mainnet.slot closedData closeFrame = none := rfl

theorem close_header_and_privileges :
    programAccount.owner = Ids.bpfLoaderUpgradeable ∧
    programAccount.data = u32le 2 ++ programDataKey.bytes ∧
    programDataAccount.owner = Ids.bpfLoaderUpgradeable ∧
    loaderDiscriminant programDataAccount.data = some 3 ∧
    slice programDataAccount.data 13 32 = authorityKey.bytes ∧
    leNat (slice programDataAccount.data 4 8) < world.sysvars.clock.slot ∧
    closeFrame.accounts[0]? = some ⟨2, false, true⟩ ∧
    closeFrame.accounts[2]? = some ⟨0, true, true⟩ ∧
    closeFrame.accounts[3]? = some ⟨1, false, true⟩ ∧
    programDataKey ≠ recipientKey := by
  decide

/-- The opaque behavior is exhibited by checked account setters, not postulated. -/
theorem close_account_execution : Havoc world beforeClose closeFrame (.ok closedData) := by
  apply Exec.havocSetter (.dataLength 4) ⟨2, false, true⟩
  · simp [closeFrame]
  · rfl
  · apply Exec.havocSetter (.lamports 3000000) ⟨3, false, true⟩
    · simp [closeFrame]
    · rfl
    · apply Exec.havocSetter (.lamports 0) ⟨2, false, true⟩
      · simp [closeFrame]
      · rfl
      · apply Exec.havocSetter (.dataFromSlice (u32le 0)) ⟨2, false, true⟩
        · simp [closeFrame]
        · rfl
        · exact Exec.havocDone

/-- The actual loader rule adds the cache write before the instruction pops. -/
theorem close_executed : ProcInstr world initial closeFrame (.ok closed) := by
  change Exec world (.procInstr initial closeFrame
    (afterProgram (finishLoaderV3 mainnet.slot beforeClose closeFrame (.ok closedData))))
  apply Exec.run (ts1 := entered)
  · rfl
  · exact Exec.loaderV3 (by rfl) close_account_execution rfl rfl

/-- The cache effect is necessary for every successful close at this dispatch. -/
theorem every_successful_close_records_cache (after : TxState)
    (execution : RunProgram world beforeClose closeFrame (.ok after)) :
    after.modifiedPrograms.lookup programKey = some (.closed mainnet.slot) :=
  RunProgram.loaderV3_cache (by rfl) close_classified execution

theorem account_effects_alone_cannot_finish :
    ¬ RunProgram world beforeClose closeFrame (.ok closedData) := by
  intro execution
  have forced := every_successful_close_records_cache closedData execution
  have absent : closedData.modifiedPrograms.lookup programKey = none := rfl
  rw [absent] at forced
  cases forced

theorem close_changes_accounts_and_cache :
    closedData.modifiedPrograms = [] ∧
    closed.modifiedPrograms = [(programKey, .closed mainnet.slot)] ∧
    (closed.acct 2).lamports = 0 ∧ (closed.acct 2).data = u32le 0 ∧
    (closed.acct 3).lamports = 3000000 ∧
    closed.acct 1 = initial.acct 1 ∧ closed.lamportSum = initial.lamportSum := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem invocation_after_close_unsupported :
    dispatch world callRunning callFrame = .unsupported := rfl

theorem invocation_after_close_fails :
    ProcInstr world closed callFrame (.error .UnsupportedProgramId) := by
  have execution : ProcInstr world closed callFrame
      (afterProgram (.error .UnsupportedProgramId)) :=
    Exec.run (ts1 := callEntered) (by rfl) (Exec.unsupported invocation_after_close_unsupported)
  simpa only [afterProgram] using execution

/-- A loaded initial entry cannot supply a successful run after the mandatory close. -/
theorem closed_run_cannot_succeed (after : TxState) :
    ¬ RunProgram world callRunning callFrame (.ok after) := by
  intro execution
  cases execution with
  | system dispatched _ => cases dispatched.symm.trans invocation_after_close_unsupported
  | systemNonce dispatched _ _ => cases dispatched.symm.trans invocation_after_close_unsupported
  | computeBudget dispatched => cases dispatched.symm.trans invocation_after_close_unsupported
  | unmodelled dispatched _ _ => cases dispatched.symm.trans invocation_after_close_unsupported
  | loaderV3 dispatched _ _ _ => cases dispatched.symm.trans invocation_after_close_unsupported
  | sbf dispatched _ _ _ => cases dispatched.symm.trans invocation_after_close_unsupported

theorem close_message_succeeds :
    ProcMessage world closeTx.allData initial (closeMessage.frames mainnet) 0 (.ok closed) := by
  rw [frame_privileges.1]
  exact ProcMessage.instr (by rfl) close_executed ProcMessage.nil

/-- The failure occurs at instruction 1 after a successful, state-changing instruction 0. -/
theorem close_then_call_fails :
    ProcMessage world failedTx.allData initial (failedMessage.frames mainnet) 0
      (.error (.InstructionError 1 .UnsupportedProgramId)) := by
  rw [frame_privileges.2]
  exact ProcMessage.instr (by rfl) close_executed
    (ProcMessage.instrFail (by rfl) invocation_after_close_fails)

theorem close_executes : Execute bank closeTx loaded (.ok closed) := by
  apply Execute.ok
  · exact close_message_succeeds
  · rfl
  · rfl

theorem close_then_call_execution_fails :
    Execute bank failedTx loaded (.error (.InstructionError 1 .UnsupportedProgramId)) :=
  Execute.fail close_then_call_fails

def committed : Accounts := commitSuccess bank closeTx accounts closed
def rollbackAccounts : Accounts := commitRollback failedTx accounts loadedPayer none

/-- Admission and loading lead to the same concrete state used in the close proof. -/
theorem close_admission_and_loading :
    validateNonce bank accounts closeTx = .ok none ∧
    validateFeePayer bank accounts closeTx = .ok loadedPayer ∧
    checkLoad bank accounts closeTx = .ok () ∧
    loadedAccounts bank accounts closeTx loadedPayer = loaded := ⟨rfl, rfl, rfl, rfl⟩

theorem failed_admission_and_loading :
    validateNonce bank accounts failedTx = .ok none ∧
    validateFeePayer bank accounts failedTx = .ok loadedPayer ∧
    checkLoad bank accounts failedTx = .ok () ∧
    loadedAccounts bank accounts failedTx loadedPayer = loaded := ⟨rfl, rfl, rfl, rfl⟩

/-- The successful receipt is taken from the state of the exhibited execution. -/
theorem close_transaction_commits_cache :
    ProcTxWithCache bank accounts closeTx committed (.executed (.ok ()))
      closed.modifiedPrograms := by
  apply ProcTxWithCache.executedOk (payer := loadedPayer) (post := closed) (nonce := none)
  · rfl
  · exact close_admission_and_loading.1
  · exact close_admission_and_loading.2.1
  · exact close_admission_and_loading.2.2.1
  · rw [close_admission_and_loading.2.2.2]
    exact close_executes

/-- The same close has occurred, but the later dispatch failure discards its cache write. -/
theorem failed_transaction_discards_cache :
    ProcTxWithCache bank accounts failedTx rollbackAccounts
      (.executed (.error (.InstructionError 1 .UnsupportedProgramId))) [] := by
  apply ProcTxWithCache.executedErr (payer := loadedPayer) (nonce := none)
  · rfl
  · exact failed_admission_and_loading.1
  · exact failed_admission_and_loading.2.1
  · exact failed_admission_and_loading.2.2.1
  · rw [failed_admission_and_loading.2.2.2]
    exact close_then_call_execution_fails

theorem close_transaction_projects :
    ProcTx bank accounts closeTx committed (.executed (.ok ())) :=
  close_transaction_commits_cache.toProcTx

theorem close_receipt_nonempty :
    closed.modifiedPrograms.lookup programKey = some (.closed mainnet.slot) ∧
    closed.modifiedPrograms ≠ [] := by
  exact ⟨rfl, by decide⟩

theorem transaction_account_results :
    committed programDataKey = none ∧
    (committed recipientKey).map Account.lamports = some 3000000 ∧
    rollbackAccounts programDataKey = some programDataAccount ∧
    (rollbackAccounts recipientKey).map Account.lamports = some 1000000 ∧
    (rollbackAccounts authorityKey).map Account.lamports = some 2995000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem successful_receipt_changes_next_dispatch :
    committedPrograms bank closed.modifiedPrograms programKey = .notDeployed ∧
    dispatch ((bank.withCommittedPrograms closed.modifiedPrograms).world closeTx)
      initial callFrame = .unsupported := ⟨rfl, rfl⟩

theorem failed_receipt_preserves_next_dispatch :
    committedPrograms bank [] = bank.programs ∧
    dispatch ((bank.withCommittedPrograms []).world failedTx) initial callFrame =
      .sbf .v1 zeroProgram := ⟨rfl, rfl⟩

theorem no_failed_receipt_keeps_close :
    ¬ ProcTxWithCache bank accounts failedTx rollbackAccounts
      (.executed (.error (.InstructionError 1 .UnsupportedProgramId)))
      closed.modifiedPrograms := by
  intro execution
  have empty := execution.failure_changes (by intro impossible; cases impossible)
  exact close_receipt_nonempty.2 empty

theorem committed_other_key_unchanged (key : Pubkey) (different : key ≠ programKey) :
    committedPrograms bank closed.modifiedPrograms key = bank.programs key := by
  apply committedPrograms_unchanged
  change ProgramCacheChanges.lookup [(programKey, .closed mainnet.slot)] key = none
  simp [ProgramCacheChanges.lookup, different]

/-- A later write to the same key hides all older entries for that key. -/
theorem newest_write_shadows :
    ((closed.modifiedPrograms.store programKey (.unloaded (mainnet.slot + 1))).store
      programKey (.closed (mainnet.slot + 2))).lookup programKey =
      some (.closed (mainnet.slot + 2)) := by
  simp

theorem writing_other_key_preserves_close :
    (closed.modifiedPrograms.store recipientKey (.unloaded mainnet.slot)).lookup programKey =
      some (.closed mainnet.slot) := by
  rfl

theorem unrelated_overlay_preserves_loaded_dispatch :
    dispatch world { initial with modifiedPrograms := [(recipientKey, .closed mainnet.slot)] }
      callFrame = .sbf .v1 zeroProgram := rfl

/-! The following frames exercise only cache-effect classification. A source
success still requires all remaining loader accounts and validation conditions. -/

def deployFrame : Frame :=
  ⟨4, [⟨0, true, true⟩, ⟨2, false, true⟩, ⟨1, false, true⟩], u32le 2 ++ u64le 64⟩

def upgradeFrame : Frame :=
  ⟨4, [⟨2, false, true⟩, ⟨1, false, true⟩], u32le 3⟩

def extendFrame : Frame :=
  ⟨4, [⟨2, false, true⟩, ⟨1, false, true⟩], u32le 6 ++ u32le 64⟩

theorem deploy_upgrade_extend_classified :
    loaderV3CacheEffect mainnet.slot initial deployFrame =
      some (programKey, .unloaded mainnet.slot) ∧
    loaderV3CacheEffect mainnet.slot initial upgradeFrame =
      some (programKey, .unloaded mainnet.slot) ∧
    loaderV3CacheEffect mainnet.slot initial extendFrame =
      some (programKey, .unloaded mainnet.slot) := ⟨rfl, rfl, rfl⟩

/-- Each successful classified return overwrites a prior entry with `Unloaded`. -/
theorem deploy_upgrade_extend_finish (after : TxState) :
    (applyLoaderV3Effect mainnet.slot initial deployFrame after).modifiedPrograms.lookup
      programKey = some (.unloaded mainnet.slot) ∧
    (applyLoaderV3Effect mainnet.slot initial upgradeFrame after).modifiedPrograms.lookup
      programKey = some (.unloaded mainnet.slot) ∧
    (applyLoaderV3Effect mainnet.slot initial extendFrame after).modifiedPrograms.lookup
      programKey = some (.unloaded mainnet.slot) :=
  ⟨applyLoaderV3Effect_lookup deploy_upgrade_extend_classified.1,
    applyLoaderV3Effect_lookup deploy_upgrade_extend_classified.2.1,
    applyLoaderV3Effect_lookup deploy_upgrade_extend_classified.2.2⟩

theorem unloaded_dispatch_rejected :
    dispatch world (applyLoaderV3Effect mainnet.slot initial deployFrame initial) callFrame =
      .unsupported ∧
    dispatch world (applyLoaderV3Effect mainnet.slot initial upgradeFrame initial) callFrame =
      .unsupported ∧
    dispatch world (applyLoaderV3Effect mainnet.slot initial extendFrame initial) callFrame =
      .unsupported := ⟨rfl, rfl, rfl⟩

theorem unloaded_visibility :
    (ModifiedProgram.unloaded mainnet.slot).effectiveSlot = mainnet.slot + 1 ∧
    (ModifiedProgram.unloaded mainnet.slot).delayedAt mainnet.slot = true ∧
    (ModifiedProgram.unloaded mainnet.slot).delayedAt (mainnet.slot + 1) = false ∧
    (ModifiedProgram.closed mainnet.slot).delayedAt mainnet.slot = false := by
  decide

theorem unloaded_visibility_saturates :
    (ModifiedProgram.unloaded U64_MAX).effectiveSlot = U64_MAX ∧
    (ModifiedProgram.unloaded U64_MAX).delayedAt U64_MAX = false := by
  decide

def missingTargetClose : Frame := { closeFrame with accounts := closeFrame.accounts.take 3 }

/-- Missing the Program account cannot turn a successful ProgramData close into preservation. -/
theorem missing_close_target_rejects_success :
    ¬ LoaderV3ResultContract mainnet.slot beforeClose missingTargetClose (.ok closedData) := by
  unfold LoaderV3ResultContract
  decide

/-- Failed opaque outcomes keep their errors; cache classification adds no new precedence. -/
theorem failed_loader_preserves_error :
    finishLoaderV3 mainnet.slot beforeClose missingTargetClose (.error .InvalidInstructionData) =
      .error .InvalidInstructionData ∧
    LoaderV3ResultContract mainnet.slot beforeClose missingTargetClose
      (.error .InvalidInstructionData) := ⟨rfl, trivial⟩

end SolanalibTest.Runtime.ProgramCacheTest
