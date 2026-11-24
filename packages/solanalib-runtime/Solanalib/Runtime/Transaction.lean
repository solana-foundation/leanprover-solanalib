/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Nonce

@[expose] public section

/-!
# Transactions

The transaction pipeline of Agave 4.3.2: bank admission, nonce revalidation,
fee-payer validation, account loading, execution of the message, rent and
lamport checks after execution, and commit or rollback.
The fee is a bank input consumed by validation before execution; computing it
from signatures and compute-budget instructions remains outside this model
(`svm/src/transaction_processor.rs:694-831`). The current source review is
[`agave-4.3.2.md`](../../source-notes/agave-4.3.2.md).
-/

namespace Solanalib.Runtime

/-- The account state of a bank. A zero-lamport account denotes absence;
`AccountLoader::do_load` filters deallocated cached accounts
(Agave 4.3.2, `svm/src/account_loader.rs:278-297`). -/
abbrev Accounts := Pubkey → Option Account

/-- The initialized nonce-account classification used by fee-payer validation.
Both legacy and current nonce versions have an 80-byte representation with
u32 version tag 0 or 1 followed by the initialized-state tag 1
(`solana-nonce-account::get_system_account_kind`, used by Agave 4.3.2). -/
def isInitializedNonceAccount (account : Account) : Bool :=
  account.owner == Ids.systemProgram && account.data.length == 80 &&
    (leNat (slice account.data 0 4) == 0 || leNat (slice account.data 0 4) == 1) &&
    leNat (slice account.data 4 4) == 1

/-- The environment of the transactions of a bank. -/
structure BankEnv where
  prof : Profile
  prims : Prims
  sysvars : Sysvars
  epochStake : Option Pubkey → Nat
  builtins : Pubkey → Option Builtin
  programs : Pubkey → ProgramEntry
  /-- The bytes that SIMD-0186 counts besides the accounts: program data of loader-v3
  programs and address lookup tables. This is an external size input covering
  `svm/src/account_loader.rs:535-583`. -/
  extraLoadedSize : Message → Nat
  /-- Whether the message blockhash is in the bank queue within the maximum
  accepted age. This is an explicit bank-admission boundary. -/
  isRecentBlockhash : Bytes → Bool
  /-- The current bank blockhash used by `DurableNonce::from_blockhash`. -/
  environmentBlockhash : Pubkey
  /-- The signature fee stored in the next nonce state. -/
  nextLamportsPerSignature : UInt64
  /-- The transaction-processing size check, independent of the account codec. -/
  strictNonceSizeCheck : Bool

/-- Nonce-account classification uses the initialized nonce decoder. -/
def BankEnv.isNonceAccount (_bank : BankEnv) : Account → Bool := isInitializedNonceAccount

structure BankEnv.WF (bank : BankEnv) : Prop where
  profile : bank.prof.WF
  sysvars : bank.sysvars.WF
  rent : bank.sysvars.rent = bank.prof.rent.toSysvar
  builtins : BuiltinsWF bank.builtins

/-- The durable nonce that `nextDurableNonce` computes has 32 bytes, by the width law of
`Prims` (`Prims.sha256_length`). -/
theorem BankEnv.WF.nonceHash {bank : BankEnv} (_valid : bank.WF) :
    (bank.prims.sha256
      (strBytes "DURABLE_NONCE" ++ bank.environmentBlockhash.bytes)).length = 32 :=
  bank.prims.sha256_length _

/-- A transaction at the sanitized-message boundary with bank inputs.
This structure does not certify complete message sanitization or signatures;
the nonce choice is checked explicitly by `validateNonce`. -/
structure Tx where
  message : Message
  fee : Nat
  /-- The loaded-data limit: `SetLoadedAccountsDataSizeLimit`, capped at 64 MiB. -/
  loadedDataLimit : Nat
  /-- The heap size: `RequestHeapFrame`, or 32 KiB. -/
  heapSize : Nat
  /-- The bank-selected nonce index, checked against `isRecentBlockhash` and
  the marker instruction by `validateNonce`. The advanced state is computed
  from the stored account; it is never supplied by the transaction. -/
  nonce : Option Nat
  /-- The result of the checks of the bank before the SVM: account locks, compute budget
  instructions, fixed-root nonce admission and status cache. A successful result
  is an external boundary condition; blockhash-mode consistency and current
  nonce state are also checked by `validateNonce`
  (`runtime/src/bank/check_transactions.rs:109-299`). -/
  bankCheck : Option TxError

/-- The transaction outcomes distinguished by account loading and storage
(`svm/src/account_loader.rs:423-471`, `runtime/src/account_saver.rs:52-108`). -/
inductive TxOutcome where
  /-- Rejected before loading: nothing is committed and no fee is charged. -/
  | notLoaded (e : TxError)
  /-- A load failure after fee-payer validation: the rollback accounts are committed. -/
  | feesOnly (e : TxError)
  /-- Executed: on success the writable accounts are committed, and on failure the
  rollback accounts. -/
  | executed (r : Except TxError Unit)

/-- The world of the instructions of a transaction. -/
def BankEnv.world (B : BankEnv) (tx : Tx) : World :=
  { prof := B.prof, prims := B.prims, sysvars := B.sysvars, epochStake := B.epochStake,
    heapSize := tx.heapSize, builtins := B.builtins, programs := B.programs }

theorem BankEnv.world_wf {bank : BankEnv} (valid : bank.WF) (tx : Tx) : (bank.world tx).WF :=
  ⟨valid.profile, valid.sysvars, valid.rent, valid.builtins⟩

/-- The fee payer: the first account key. -/
def Tx.payerKey (tx : Tx) : Pubkey := tx.message.keys.headD default

/-- Revalidate a bank-selected nonce against the current loaded account state,
before validating or charging the fee payer. The current account may differ
from the fixed-root account read by the earlier bank check.

The order after selection is account existence, strict size, current nonce
decoding and blockhash match, freshness and authority. Only a successful check
constructs the keyed advanced account used by rollback
(`svm/src/transaction_processor.rs:694-737, 833-897`). -/
def validateNonce (B : BankEnv) (accts : Accounts) (tx : Tx) :
    Except TxError (Option (Pubkey × Account)) := do
  let selected ← checkNonceSelection B.prof B.isRecentBlockhash tx.message tx.nonce
  match selected with
  | none => .ok none
  | some index =>
    match tx.message.keys[index]? with
    | none => .error .BlockhashNotFound
    | some address =>
      match accts address with
      | none => .error .AccountNotFound
      | some account =>
        if account.lamports = 0 then .error .AccountNotFound
        else if B.strictNonceSizeCheck && account.data.length != 80 then
          .error .BlockhashNotFound
        else match decodeCurrentNonce account with
          | none => .error .BlockhashNotFound
          | some data =>
            if data.durableNonce.bytes != tx.message.recentBlockhash then
              .error .BlockhashNotFound
            else
              let next := nextDurableNonce B.prims.toCryptoPrimitives B.environmentBlockhash
              if data.durableNonce = next || !tx.message.nonceAuthoritySigned data.authority then
                .error .BlockhashNotFound
              else .ok (some (address,
                advanceNonceAccount account data.authority next B.nextLamportsPerSignature))

/-- A successful durable admission computes the advanced account from the
account actually read at the returned address. No supplied account value can
replace its balance, owner, executable flag or rent epoch. -/
theorem validateNonce_advanced {B : BankEnv} {accts : Accounts} {tx : Tx}
    {address : Pubkey} {advanced : Account}
    (valid : validateNonce B accts tx = .ok (some (address, advanced))) :
    ∃ account data, accts address = some account ∧ decodeCurrentNonce account = some data ∧
      advanced = advanceNonceAccount account data.authority
        (nextDurableNonce B.prims.toCryptoPrimitives B.environmentBlockhash)
        B.nextLamportsPerSignature := by
  unfold validateNonce at valid
  cases selected : checkNonceSelection B.prof B.isRecentBlockhash tx.message tx.nonce with
  | error error => simp [selected, Bind.bind, Except.bind] at valid
  | ok nonce =>
    cases nonce with
    | none => simp [selected, Bind.bind, Except.bind] at valid
    | some index =>
      simp only [selected, Bind.bind, Except.bind] at valid
      split at valid
      · cases valid
      · rename_i key hkey
        split at valid
        · cases valid
        · rename_i account haccount
          split at valid
          · cases valid
          · split at valid
            · cases valid
            · split at valid
              · cases valid
              · rename_i data hdata
                split at valid
                · cases valid
                · split at valid
                  · cases valid
                  · cases valid
                    exact ⟨account, data, haccount, hdata, rfl⟩

/-- The nonce admission step preserves every account field outside the
serialized state, independently of the validity of any proposed replacement. -/
theorem validateNonce_preserves_fields {B : BankEnv} {accts : Accounts} {tx : Tx}
    {address : Pubkey} {advanced : Account}
    (valid : validateNonce B accts tx = .ok (some (address, advanced))) :
    ∃ account, accts address = some account ∧ advanced.lamports = account.lamports ∧
      advanced.owner = account.owner ∧ advanced.executable = account.executable ∧
      advanced.rentEpoch = account.rentEpoch := by
  obtain ⟨account, data, stored, _, rfl⟩ := validateNonce_advanced valid
  exact ⟨account, stored, advanceNonceAccount_fields ..⟩

theorem validateNonce_preserves_length {B : BankEnv} {accts : Accounts} {tx : Tx}
    {address : Pubkey} {advanced : Account}
    (valid : validateNonce B accts tx = .ok (some (address, advanced))) :
    ∃ account, accts address = some account ∧ advanced.data.length = account.data.length := by
  obtain ⟨account, data, stored, decoded, rfl⟩ := validateNonce_advanced valid
  exact ⟨account, stored, advanceNonceAccount_length _ _ _ _ (decodeCurrentNonce_size decoded)⟩

/-- The rent epoch of a loaded account that is rent-exempt: `u64::MAX`
(`svm/src/account_loader.rs:355-364`). -/
def maskExemptRentEpoch (r : RentParams) (a : Account) : Account :=
  if r.isExempt a.lamports a.data.length then { a with rentEpoch := U64_MAX } else a

/-- The validation of the fee payer, which returns the payer after the fee
(`svm/src/transaction_processor.rs:763-809`, `svm/src/account_loader.rs:373-420`). -/
def validateFeePayer (B : BankEnv) (accts : Accounts) (tx : Tx) : Except TxError Account :=
  match accts tx.payerKey with
  | none => .error .AccountNotFound
  | some a0 =>
    let a := maskExemptRentEpoch B.prof.rent a0
    if a.lamports = 0 then .error .AccountNotFound
    else if !((a.owner == Ids.systemProgram && a.data.isEmpty) || B.isNonceAccount a) then
      .error .InvalidAccountForFee
    else
      let minBal := if B.isNonceAccount a then B.prof.rent.minBalance a.data.length else 0
      if a.lamports < minBal + tx.fee then .error .InsufficientFundsForFee
      else
        let a' := { a with lamports := a.lamports - tx.fee }
        if !feePayerRentCheck B.prof tx.payerKey a a' then .error (.InsufficientFundsForRent 0)
        else .ok a'

/-- The account at index `i` after loading: the fee payer after the fee, the constructed
Instructions sysvar, the stored account, or the default account for a missing address
(`svm/src/account_loader.rs:593-610, 622-654`). -/
def loadedAccount (B : BankEnv) (accts : Accounts) (tx : Tx) (payer : Account) (i : Nat)
    (k : Pubkey) : Account :=
  if i = 0 then payer
  else if k = Ids.sysvarInstructions then ixSysvarAccount B.prof tx.message
  else match accts k with
    | some a =>
      if tx.message.isWritable B.prof i then maskExemptRentEpoch B.prof.rent a else a
    | none => Account.missing

/-- The loaded accounts, in key order. -/
def loadedAccounts (B : BankEnv) (accts : Accounts) (tx : Tx) (payer : Account) : List Account :=
  tx.message.keys.mapIdx (loadedAccount B accts tx payer)

/-- The loaded data size under SIMD-0186: 64 bytes plus the data length per existing
account, the Instructions sysvar counting zero. Program-data and lookup-table
contributions are supplied by `extraLoadedSize`
(`svm/src/account_loader.rs:245-248, 535-583, 632-639`). -/
def loadedSize (B : BankEnv) (accts : Accounts) (tx : Tx) : Nat :=
  (tx.message.keys.map fun k =>
    if k = Ids.sysvarInstructions then 0
    else match accts k with
      | some a => 64 + a.data.length
      | none => 0).sum + B.extraLoadedSize tx.message

/-- The checks of account loading: the size limit, then each program account exists and
is owned by the native loader or a BPF loader; the executable flag is not read
(`svm/src/account_loader.rs:484-507, 596-617`). -/
def checkLoad (B : BankEnv) (accts : Accounts) (tx : Tx) : Except TxError Unit :=
  if B.prof.release = .agave_4_3_2 && tx.message.keys.contains Ids.sysvarInstructions &&
      !ixSysvarOffsetsFit B.prof tx.message then .error .MaxLoadedAccountsDataSizeExceeded
  else if tx.loadedDataLimit < loadedSize B accts tx then .error .MaxLoadedAccountsDataSizeExceeded
  else
    let check (ix : CompiledIx) : Except TxError Unit :=
      match accts (tx.message.keys.getD ix.programIdIndex default) with
      | none => .error .ProgramAccountNotFound
      | some a =>
        if a.owner = Ids.nativeLoader ∨ a.owner ∈ Ids.bpfLoaders then .ok ()
        else .error .InvalidProgramForExecution
    tx.message.instructions.forM check

/-- The transaction context at the start of execution
(`svm/src/transaction_processor.rs:1065-1072`). -/
def initTxState (keys : List Pubkey) (accts : List Account) : TxState :=
  { keys := keys, accts := accts, lamportsDelta := 0, resizeDelta := 0, stack := [],
    trace := [], returnData := (default, []), topIndex := 0 }

/-- The rent check of every writable account between its loaded and its final state; the
first failure gives its index (`svm/src/transaction_account_state_info.rs`,
`svm/src/transaction_processor.rs:1116-1135`). -/
def rentCheckAll (p : Profile) (m : Message) (pre post : List Account) : Except TxError Unit :=
  match (List.range m.keys.length).find? fun i =>
      m.isWritable p i && !rentCheck p (m.keys.getD i default) (pre.getD i default)
        (post.getD i default) with
  | some i => .error (.InsufficientFundsForRent i)
  | none => .ok ()

/-- The data of all top-level instructions, which the precompiles read. -/
def Tx.allData (tx : Tx) : List Bytes := tx.message.instructions.map (·.data)

/-- The execution of a loaded transaction (`execute_loaded_transaction`,
`svm/src/transaction_processor.rs:1033-1191`). -/
inductive Execute (B : BankEnv) (tx : Tx) : List Account → Except TxError TxState → Prop
  | ok {loaded : List Account} {ts : TxState} :
      ProcMessage (B.world tx) tx.allData (initTxState tx.message.keys loaded)
        (tx.message.frames B.prof) 0 (.ok ts) →
      rentCheckAll B.prof tx.message loaded ts.accts = .ok () →
      ts.lamportSum = (initTxState tx.message.keys loaded).lamportSum →
      Execute B tx loaded (.ok ts)
  | rentFail {loaded : List Account} {ts : TxState} {e : TxError} :
      ProcMessage (B.world tx) tx.allData (initTxState tx.message.keys loaded)
        (tx.message.frames B.prof) 0 (.ok ts) →
      rentCheckAll B.prof tx.message loaded ts.accts = .error e →
      Execute B tx loaded (.error e)
  | unbalanced {loaded : List Account} {ts : TxState} :
      ProcMessage (B.world tx) tx.allData (initTxState tx.message.keys loaded)
        (tx.message.frames B.prof) 0 (.ok ts) →
      rentCheckAll B.prof tx.message loaded ts.accts = .ok () →
      ts.lamportSum ≠ (initTxState tx.message.keys loaded).lamportSum →
      Execute B tx loaded (.error .UnbalancedTransaction)
  | fail {loaded : List Account} {e : TxError} :
      ProcMessage (B.world tx) tx.allData (initTxState tx.message.keys loaded)
        (tx.message.frames B.prof) 0 (.error e) →
      Execute B tx loaded (.error e)

/-- The account state with an account stored, a zero balance removing it. -/
def storeAccount (accts : Accounts) (k : Pubkey) (a : Account) : Accounts :=
  fun k' => if k' = k then (if a.lamports = 0 then none else some a) else accts k'

/-- Whether index `i` is an instruction account of some top-level instruction. -/
def Message.isInstrAccount (m : Message) (i : Nat) : Bool :=
  m.instructions.any fun ix => ix.accounts.contains i

/-- Static account eligibility for storage after a successful transaction. -/
def Message.eligibleForSave (p : Profile) (m : Message) (i : Nat) : Bool :=
  m.isWritable p i && !(m.isInvoked i && !m.isInstrAccount i)

/-- Agave 4.3.2 stores only touched accounts. The fee payer is marked at execution
completion because fee deduction occurs during loading, outside the invocation.
Earlier supported releases save every statically eligible account. -/
def TxState.saveEligible (p : Profile) (post : TxState) (i : Nat) : Bool :=
  p.release != .agave_4_3_2 || i == 0 || post.touched.contains i

/-- The exact account-saving predicate for the supported profiles. -/
def savesAccount (B : BankEnv) (tx : Tx) (post : TxState) (i : Nat) : Bool :=
  tx.message.eligibleForSave B.prof i && post.saveEligible B.prof i

theorem savesAccount_fee_payer (B : BankEnv) (tx : Tx) (post : TxState) :
    savesAccount B tx post 0 = tx.message.eligibleForSave B.prof 0 := by
  simp [savesAccount, TxState.saveEligible]

theorem savesAccount_untouched {B : BankEnv} {tx : Tx} {post : TxState} {i : Nat}
    (current : B.prof.release = .agave_4_3_2) (notPayer : i ≠ 0) (untouched : i ∉ post.touched) :
    savesAccount B tx post i = false := by
  simp [savesAccount, TxState.saveEligible, current, notPayer, untouched]

/-- Commit successful execution, retaining explicit mutation metadata. In Agave
4.3.2 an untouched write-locked account keeps its stored state, including its
rent epoch (`runtime/src/account_saver.rs`, `svm/src/account_loader.rs:313-333`). -/
def commitSuccess (B : BankEnv) (tx : Tx) (accts : Accounts) (post : TxState) : Accounts :=
  (List.range tx.message.keys.length).foldl (fun acc i =>
    if savesAccount B tx post i then
      storeAccount acc (tx.message.keys.getD i default) (post.acct i)
    else acc) accts

/-- Commit the rollback accounts. Without a nonce, restore the stored rent
epoch. With a nonce, retain the validated payer, including its rent epoch; if
the payer is the nonce account, replace only its data with the advanced nonce
data (Agave 4.3.2, `svm/src/rollback_accounts.rs:65-99`). The nonce argument is
the result of `validateNonce` in every processing rule; this helper does not
perform admission itself. Addresses have already been resolved, so rollback
never substitutes a default key for an invalid index. -/
def commitRollback (tx : Tx) (accts : Accounts) (payer : Account)
    (nonce : Option (Pubkey × Account)) : Accounts :=
  let stored := (accts tx.payerKey).map (·.rentEpoch) |>.getD payer.rentEpoch
  match nonce with
  | none => storeAccount accts tx.payerKey { payer with rentEpoch := stored }
  | some (address, advanced) =>
    if address = tx.payerKey then
      storeAccount accts tx.payerKey { payer with data := advanced.data }
    else storeAccount (storeAccount accts tx.payerKey payer) address advanced

/-- The processing of a transaction against the accounts of a bank. -/
inductive ProcTx (B : BankEnv) : Accounts → Tx → Accounts → TxOutcome → Prop
  | rejected {accts : Accounts} {tx : Tx} {e : TxError} :
      tx.bankCheck = some e → ProcTx B accts tx accts (.notLoaded e)
  | nonceRejected {accts : Accounts} {tx : Tx} {e : TxError} :
      tx.bankCheck = none → validateNonce B accts tx = .error e →
      ProcTx B accts tx accts (.notLoaded e)
  | payerRejected {accts : Accounts} {tx : Tx} {e : TxError}
      {nonce : Option (Pubkey × Account)} :
      tx.bankCheck = none → validateNonce B accts tx = .ok nonce →
      validateFeePayer B accts tx = .error e →
      ProcTx B accts tx accts (.notLoaded e)
  | loadFailed {accts : Accounts} {tx : Tx} {payer : Account} {e : TxError}
      {nonce : Option (Pubkey × Account)} :
      tx.bankCheck = none → validateNonce B accts tx = .ok nonce →
      validateFeePayer B accts tx = .ok payer →
      checkLoad B accts tx = .error e →
      ProcTx B accts tx (commitRollback tx accts payer nonce) (.feesOnly e)
  | executedOk {accts : Accounts} {tx : Tx} {payer : Account} {post : TxState}
      {nonce : Option (Pubkey × Account)} :
      tx.bankCheck = none → validateNonce B accts tx = .ok nonce →
      validateFeePayer B accts tx = .ok payer →
      checkLoad B accts tx = .ok () →
      Execute B tx (loadedAccounts B accts tx payer) (.ok post) →
      ProcTx B accts tx (commitSuccess B tx accts post) (.executed (.ok ()))
  | executedErr {accts : Accounts} {tx : Tx} {payer : Account} {e : TxError}
      {nonce : Option (Pubkey × Account)} :
      tx.bankCheck = none → validateNonce B accts tx = .ok nonce →
      validateFeePayer B accts tx = .ok payer →
      checkLoad B accts tx = .ok () →
      Execute B tx (loadedAccounts B accts tx payer) (.error e) →
      ProcTx B accts tx (commitRollback tx accts payer nonce) (.executed (.error e))

/-- Nonce admission failures have exactly the unchanged, uncharged outcome.
No fee-payer, load or execution rule can bypass this check. -/
theorem ProcTx.nonce_error {B : BankEnv} {accts post : Accounts} {tx : Tx}
    {outcome : TxOutcome} {error : TxError} (bank : tx.bankCheck = none)
    (failed : validateNonce B accts tx = .error error)
    (processed : ProcTx B accts tx post outcome) :
    post = accts ∧ outcome = .notLoaded error := by
  cases processed <;> simp_all

/-- Transaction processing with the cache modifications committed by this same
execution. Agave drains the transaction-local cache entries after execution and
merges them into the batch cache only when the complete transaction succeeds
(`svm/src/transaction_processor.rs:594-603,1230`). Failed and rejected outcomes
therefore export no modifications, including failures of final rent or balance
checks. The account-only `ProcTx` API is exactly its existential projection. -/
inductive ProcTxWithCache (B : BankEnv) :
    Accounts → Tx → Accounts → TxOutcome → ProgramCacheChanges → Prop
  | rejected {accts : Accounts} {tx : Tx} {e : TxError} :
      tx.bankCheck = some e → ProcTxWithCache B accts tx accts (.notLoaded e) []
  | nonceRejected {accts : Accounts} {tx : Tx} {e : TxError} :
      tx.bankCheck = none → validateNonce B accts tx = .error e →
      ProcTxWithCache B accts tx accts (.notLoaded e) []
  | payerRejected {accts : Accounts} {tx : Tx} {e : TxError}
      {nonce : Option (Pubkey × Account)} :
      tx.bankCheck = none → validateNonce B accts tx = .ok nonce →
      validateFeePayer B accts tx = .error e →
      ProcTxWithCache B accts tx accts (.notLoaded e) []
  | loadFailed {accts : Accounts} {tx : Tx} {payer : Account} {e : TxError}
      {nonce : Option (Pubkey × Account)} :
      tx.bankCheck = none → validateNonce B accts tx = .ok nonce →
      validateFeePayer B accts tx = .ok payer →
      checkLoad B accts tx = .error e →
      ProcTxWithCache B accts tx (commitRollback tx accts payer nonce) (.feesOnly e) []
  | executedOk {accts : Accounts} {tx : Tx} {payer : Account} {post : TxState}
      {nonce : Option (Pubkey × Account)} :
      tx.bankCheck = none → validateNonce B accts tx = .ok nonce →
      validateFeePayer B accts tx = .ok payer →
      checkLoad B accts tx = .ok () →
      Execute B tx (loadedAccounts B accts tx payer) (.ok post) →
      ProcTxWithCache B accts tx (commitSuccess B tx accts post)
        (.executed (.ok ())) post.modifiedPrograms
  | executedErr {accts : Accounts} {tx : Tx} {payer : Account} {e : TxError}
      {nonce : Option (Pubkey × Account)} :
      tx.bankCheck = none → validateNonce B accts tx = .ok nonce →
      validateFeePayer B accts tx = .ok payer →
      checkLoad B accts tx = .ok () →
      Execute B tx (loadedAccounts B accts tx payer) (.error e) →
      ProcTxWithCache B accts tx (commitRollback tx accts payer nonce) (.executed (.error e)) []

/-- Erasing the cache receipt preserves the account and outcome semantics. -/
theorem ProcTxWithCache.toProcTx {B : BankEnv} {before after : Accounts} {tx : Tx}
    {outcome : TxOutcome} {changes : ProgramCacheChanges}
    (processed : ProcTxWithCache B before tx after outcome changes) :
    ProcTx B before tx after outcome := by
  cases processed with
  | rejected bank => exact .rejected bank
  | nonceRejected bank nonce => exact .nonceRejected bank nonce
  | payerRejected bank nonce payer => exact .payerRejected bank nonce payer
  | loadFailed bank nonce payer loaded => exact .loadFailed bank nonce payer loaded
  | executedOk bank nonce payer loaded executed =>
    exact .executedOk bank nonce payer loaded executed
  | executedErr bank nonce payer loaded executed =>
    exact .executedErr bank nonce payer loaded executed

/-- Every derivation of the existing API has a receipt from the same execution. -/
theorem ProcTx.withCache {B : BankEnv} {before after : Accounts} {tx : Tx}
    {outcome : TxOutcome} (processed : ProcTx B before tx after outcome) :
    ∃ changes, ProcTxWithCache B before tx after outcome changes := by
  cases processed with
  | rejected bank => exact ⟨[], .rejected bank⟩
  | nonceRejected bank nonce => exact ⟨[], .nonceRejected bank nonce⟩
  | payerRejected bank nonce payer => exact ⟨[], .payerRejected bank nonce payer⟩
  | loadFailed bank nonce payer loaded => exact ⟨[], .loadFailed bank nonce payer loaded⟩
  | executedOk bank nonce payer loaded executed =>
    exact ⟨_, .executedOk bank nonce payer loaded executed⟩
  | executedErr bank nonce payer loaded executed =>
    exact ⟨[], .executedErr bank nonce payer loaded executed⟩

theorem procTx_iff_withCache {B : BankEnv} {before after : Accounts} {tx : Tx}
    {outcome : TxOutcome} :
    ProcTx B before tx after outcome ↔
      ∃ changes, ProcTxWithCache B before tx after outcome changes :=
  ⟨ProcTx.withCache, fun ⟨_, processed⟩ => processed.toProcTx⟩

/-- Any outcome other than complete transaction success discards cache writes. -/
theorem ProcTxWithCache.failure_changes {B : BankEnv} {before after : Accounts} {tx : Tx}
    {outcome : TxOutcome} {changes : ProgramCacheChanges}
    (processed : ProcTxWithCache B before tx after outcome changes)
    (failed : outcome ≠ .executed (.ok ())) : changes = [] := by
  cases processed <;> simp_all

/-- Merge a successful cache receipt into the retained cache for later
transactions of the same batch. Both `Closed` and `Unloaded` reject invocation
through that view. A fresh batch can load a different cache view, even in the
same bank; its actual entries remain bank inputs. This operation does not load,
execute or invent replacement code. Deployment/effective-slot metadata remains
available in the receipt. -/
def committedPrograms (B : BankEnv) (changes : ProgramCacheChanges) : Pubkey → ProgramEntry :=
  fun key => match changes.lookup key with
    | none => B.programs key
    | some _ => .notDeployed

/-- A subsequent transaction using the retained batch cache observes its
committed overlay. Fresh cache loading requires new actual bank inputs. -/
def BankEnv.withCommittedPrograms (B : BankEnv) (changes : ProgramCacheChanges) : BankEnv :=
  { B with programs := committedPrograms B changes }

@[simp] theorem committedPrograms_empty (B : BankEnv) : committedPrograms B [] = B.programs := rfl

theorem committedPrograms_unchanged (B : BankEnv) (changes : ProgramCacheChanges) (key : Pubkey)
    (untouched : changes.lookup key = none) : committedPrograms B changes key = B.programs key := by
  simp [committedPrograms, untouched]

theorem committedPrograms_modified (B : BankEnv) (changes : ProgramCacheChanges) (key : Pubkey)
    (entry : ModifiedProgram) (modified : changes.lookup key = some entry) :
    committedPrograms B changes key = .notDeployed := by
  simp [committedPrograms, modified]

theorem ProcTxWithCache.failure_programs {B : BankEnv} {before after : Accounts} {tx : Tx}
    {outcome : TxOutcome} {changes : ProgramCacheChanges}
    (processed : ProcTxWithCache B before tx after outcome changes)
    (failed : outcome ≠ .executed (.ok ())) : committedPrograms B changes = B.programs := by
  rw [processed.failure_changes failed]
  rfl

end Solanalib.Runtime
