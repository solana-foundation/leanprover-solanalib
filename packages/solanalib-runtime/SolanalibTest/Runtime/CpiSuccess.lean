/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Frame
public import SolanalibTest.Runtime.TransactionSuccess

@[expose] public section

/-!
# A successful CPI with both account synchronization edges

The caller first writes two balances into its serialized input: it credits the
System-owned source by 10 lamports and debits its own destination by 10. CPI
preparation translates both accounts. The entry synchronization applies those
changes through the caller setters. The checked System transfer then moves 25
lamports from the source to the destination. The return synchronization updates
the input buffer, and the continuation loads both final balances before exit.

This is a witness of the runtime model under `mainnet`, ABI v1, configuration L
and checked serialized pointers. It derives the callee behavior from
`systemProcess`; it assumes no successful CPI relation. Any connection to a
deployed caller remains an explicit `Program` behavior contract. No implementation of a callee
program is included.
-/

open Solanalib.Runtime

namespace SolanalibTest.Runtime.CpiSuccess

set_option maxRecDepth 4096

def callerKey : Pubkey := Pubkey.ofNat 101
/-- RFC 8032, Ed25519 test 1, so the source can be an admitted top-level
signer. Signature admission remains outside this instruction-runtime witness. -/
def sourceKey : Pubkey :=
  ⟨[0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7,
    0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64, 0x07, 0x3a,
    0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25,
    0xaf, 0x02, 0x1a, 0x68, 0xf7, 0x07, 0x51, 0x1a], rfl⟩
def destinationKey : Pubkey := Pubkey.ofNat 103
def programDataKey : Pubkey := Pubkey.ofNat 104

/-- The upgradeable `Program` variant points to external program data. The
loaded-cache/image correspondence remains part of the caller contract. -/
def callerProgramData : Bytes := u32le 2 ++ programDataKey.bytes

def sourceAccount : InstrAcct := ⟨0, true, true⟩
def destinationAccount : InstrAcct := ⟨1, false, true⟩
def systemAccount : InstrAcct := ⟨2, false, false⟩

def accounts (sourceBalance destinationBalance : Nat) : List Account :=
  [⟨sourceBalance, [], Ids.systemProgram, false, 0⟩,
   ⟨destinationBalance, [], callerKey, false, 0⟩,
   ⟨1000000, [], Ids.nativeLoader, true, 0⟩,
   ⟨1000000, callerProgramData, Ids.bpfLoaderUpgradeable, true, 0⟩]

def caller : Frame :=
  ⟨3, [sourceAccount, destinationAccount, systemAccount], []⟩

def transferData : Bytes := u32le 2 ++ u64le 25

def callee : Frame := ⟨2, [sourceAccount, destinationAccount], transferData⟩

def initialTx : TxState where
  keys := [sourceKey, destinationKey, Ids.systemProgram, callerKey]
  accts := accounts 2000000 1000000
  lamportsDelta := 0
  resizeDelta := 0
  stack := []
  trace := []
  returnData := (callerKey, [99])
  topIndex := 0

def callerPushed : TxState :=
  { initialTx with stack := [caller], trace := [⟨1, caller⟩] }

def entryTx : TxState := resetReturnData callerPushed

def sourceSer : SerAcct := ⟨0, sourceAccount, .acct sourceAccount, 8, 0⟩
def destinationSer : SerAcct := ⟨1, destinationAccount, .acct destinationAccount, 10344, 0⟩
def systemSer : SerAcct := ⟨2, systemAccount, .acct systemAccount, 20680, 0⟩

def context : InvCtx where
  abi := .v1
  cfg := .L
  frame := caller
  layout := [sourceSer, destinationSer, systemSer]
  heapSize := DEFAULT_HEAP_SIZE

def sourceLamportsAddr : Nat := MM_INPUT_START + 80
def destinationLamportsAddr : Nat := MM_INPUT_START + 10416

def entryState : InvState :=
  ⟨entryTx, serialize .v1 mainnet entryTx caller, 0, []⟩

def afterSourceStore : InvState :=
  { entryState with buf := writeAt entryState.buf 80 (u64le 2000010) }

def beforeCpi : InvState :=
  { afterSourceStore with buf := writeAt afterSourceStore.buf 10416 (u64le 999990) }

/-- The private values are immaterial: all four checked pointers select the
serialized account. Both account-info length words are zero. -/
def info (key : Pubkey) (ser : SerAcct) : CpiAccountInfo where
  key := key
  keyAddr := MM_INPUT_START + ser.offset + 8
  ownerAddr := MM_INPUT_START + ser.offset + 40
  lamportsAddr := MM_INPUT_START + ser.offset + 72
  dataAddr := MM_INPUT_START + ser.offset + 88
  dataLen := 0
  boxesBelowInput := true
  lamportsVal := 0
  ownerVal := Ids.systemProgram
  dataVal := []

def request : CpiReq where
  ix := ⟨Ids.systemProgram,
    [⟨sourceKey, 1, 1⟩, ⟨destinationKey, 0, 1⟩], transferData⟩
  infos := [info sourceKey sourceSer, info destinationKey destinationSer]
  infosBelowInput := true
  signers := []

def translatedSource : Translated :=
  ⟨0, info sourceKey sourceSer, 0, sourceSer, true, true, true⟩

def translatedDestination : Translated :=
  ⟨1, info destinationKey destinationSer, 1, destinationSer, true, true, true⟩

def prepared : CpiPrep := ⟨callee, [translatedSource, translatedDestination]⟩

def afterSourceSyncTx : TxState :=
  { entryTx with accts := accounts 2000010 1000000, lamportsDelta := 10, touched := [0] }

/-- The destination setter also copies its unchanged empty data, recording a
second touch. The temporary balance changes cancel before the callee push. -/
def beforeCalleeTx : TxState :=
  { entryTx with accts := accounts 2000010 999990, touched := [1, 1, 0] }

def beforeCallee : InvState := { beforeCpi with ts := beforeCalleeTx }

def calleePushed : TxState :=
  { beforeCalleeTx with
    stack := [callee, caller]
    trace := [⟨1, caller⟩, ⟨2, callee⟩] }

def calleeEntry : TxState := resetReturnData calleePushed

def afterSystemDebit : TxState :=
  { calleeEntry with
    accts := accounts 1999985 999990
    lamportsDelta := -25
    touched := [0, 1, 1, 0] }

def afterSystemTransfer : TxState :=
  { calleeEntry with accts := accounts 1999985 1000015, touched := [1, 0, 1, 1, 0] }

def returnedTx : TxState := { afterSystemTransfer with stack := [caller] }

/-- The writes performed for an in-region account whose length remains zero. -/
def copyFields (buf : Bytes) (ser : SerAcct) (balance : Nat) (owner : Pubkey) : Bytes :=
  writeAt (writeAt (writeAt buf (ser.offset + 72) (u64le balance))
    (ser.offset + 40) owner.bytes) (ser.offset + 88) []

def afterCpi : InvState :=
  { beforeCallee with
    ts := returnedTx
    buf := copyFields (copyFields beforeCallee.buf sourceSer 1999985 Ids.systemProgram)
      destinationSer 1000015 callerKey }

def lengths : List (Nat × Nat) := [(0, 0), (1, 0)]

def answer : SysAns := ⟨0, [u64le 0, u64le 0]⟩

/-- Exit read-back copies the caller-owned empty data once more. -/
def finalInvocationTx : TxState := { returnedTx with touched := [1, 1, 0, 1, 1, 0] }

def finalTx : TxState := { finalInvocationTx with stack := [], topIndex := 1 }

def continuation : List (Event × Reply) :=
  [(.load sourceLamportsAddr 8, .bytes (u64le 1999985)),
   (.load destinationLamportsAddr 8, .bytes (u64le 1000015))]

def callerRun : Run :=
  ⟨[(.store sourceLamportsAddr (u64le 2000010), .unit),
    (.store destinationLamportsAddr (u64le 999990), .unit),
    (.sys (.invoke request), .sys answer)] ++ continuation, .exit 0⟩

theorem caller_push : push mainnet initialTx caller = .ok callerPushed := rfl

def sourceRecord : Bytes :=
  recordV1 true true sourceKey ⟨2000000, [], Ids.systemProgram, false, 0⟩ U64_MAX

def destinationRecord : Bytes :=
  recordV1 false true destinationKey ⟨1000000, [], callerKey, false, 0⟩ U64_MAX

def systemRecord : Bytes :=
  recordV1 false false Ids.systemProgram ⟨1000000, [], Ids.nativeLoader, true, 0⟩ U64_MAX

theorem caller_records : records .v1 mainnet entryTx caller =
    [sourceRecord, destinationRecord, systemRecord] := rfl

@[simp] theorem source_record_length : sourceRecord.length = 10336 := by
  simp [sourceRecord, length_recordV1, pad8, MAX_PERMITTED_DATA_INCREASE]

@[simp] theorem destination_record_length : destinationRecord.length = 10336 := by
  simp [destinationRecord, length_recordV1, pad8, MAX_PERMITTED_DATA_INCREASE]

@[simp] theorem system_record_length : systemRecord.length = 10336 := by
  simp [systemRecord, length_recordV1, pad8, MAX_PERMITTED_DATA_INCREASE]

theorem source_offset : recordOffset .v1 mainnet entryTx caller 0 = 8 := by
  simp [recordOffset, prefixLen]

theorem destination_offset : recordOffset .v1 mainnet entryTx caller 1 = 10344 := by
  rw [recordOffset, caller_records]
  simp [prefixLen]

theorem system_offset : recordOffset .v1 mainnet entryTx caller 2 = 20680 := by
  rw [recordOffset, caller_records]
  simp [prefixLen]

theorem serialized_layout :
    layout .v1 mainnet entryTx caller = context.layout := by
  change [⟨0, sourceAccount, slotOf caller 0 sourceAccount,
    recordOffset .v1 mainnet entryTx caller 0, 0⟩,
    ⟨1, destinationAccount, slotOf caller 1 destinationAccount,
    recordOffset .v1 mainnet entryTx caller 1, 0⟩,
    ⟨2, systemAccount, slotOf caller 2 systemAccount,
    recordOffset .v1 mainnet entryTx caller 2, 0⟩] = context.layout
  rw [source_offset, destination_offset, system_offset]
  rfl

theorem serialized_length : entryState.buf.length = 31056 := by
  change (serializeBody .v1 mainnet entryTx caller).length = 31056
  unfold serializeBody
  rw [caller_records]
  simp [u64le, caller, sourceAccount, destinationAccount, systemAccount, Pubkey.length_eq]

theorem source_store_bounds : 80 + (u64le 2000010).length ≤ entryState.buf.length := by
  rw [serialized_length]
  decide

theorem after_source_length : afterSourceStore.buf.length = 31056 := by
  change (writeAt entryState.buf 80 (u64le 2000010)).length = 31056
  rw [length_writeAt source_store_bounds, serialized_length]

theorem destination_store_bounds :
    10416 + (u64le 999990).length ≤ afterSourceStore.buf.length := by
  rw [after_source_length]
  decide

theorem before_cpi_length : beforeCpi.buf.length = 31056 := by
  change (writeAt afterSourceStore.buf 10416 (u64le 999990)).length = 31056
  rw [length_writeAt destination_store_bounds, after_source_length]

theorem source_store :
    storeRegion context entryState sourceLamportsAddr (u64le 2000010) =
      .ok afterSourceStore := by
  have valid : inRegion entryState sourceLamportsAddr (u64le 2000010).length = true := by
    rw [inRegion, serialized_length]
    decide
  unfold storeRegion
  rw [ite_eq_right (by decide), valid]
  rfl

theorem destination_store :
    storeRegion context afterSourceStore destinationLamportsAddr (u64le 999990) =
      .ok beforeCpi := by
  have valid : inRegion afterSourceStore destinationLamportsAddr (u64le 999990).length = true := by
    rw [inRegion, after_source_length]
    decide
  unfold storeRegion
  rw [ite_eq_right (by decide), valid]
  rfl

private theorem entry_source_slice (off len : Nat) (fits : off + len ≤ 10336) :
    slice entryState.buf (8 + off) len = slice sourceRecord off len := by
  have index : 0 < (records .v1 mainnet entryTx caller).length := by
    rw [caller_records]
    decide
  have bound : off + len ≤ (records .v1 mainnet entryTx caller)[0].length := by
    simpa only [caller_records, List.getElem_cons_zero, source_record_length] using fits
  have field := slice_serialize_record index bound
  simp only [source_offset, caller_records, List.getElem_cons_zero] at field
  exact field

private theorem entry_destination_slice (off len : Nat) (fits : off + len ≤ 10336) :
    slice entryState.buf (10344 + off) len = slice destinationRecord off len := by
  have index : 1 < (records .v1 mainnet entryTx caller).length := by
    rw [caller_records]
    decide
  have bound : off + len ≤ (records .v1 mainnet entryTx caller)[1].length := by
    simpa only [caller_records, List.getElem_cons_succ, List.getElem_cons_zero,
      destination_record_length] using fits
  have field := slice_serialize_record index bound
  simp only [destination_offset, caller_records, List.getElem_cons_succ,
    List.getElem_cons_zero] at field
  exact field

private theorem entry_system_slice (off len : Nat) (fits : off + len ≤ 10336) :
    slice entryState.buf (20680 + off) len = slice systemRecord off len := by
  have index : 2 < (records .v1 mainnet entryTx caller).length := by
    rw [caller_records]
    decide
  have bound : off + len ≤ (records .v1 mainnet entryTx caller)[2].length := by
    simpa only [caller_records, List.getElem_cons_succ, List.getElem_cons_zero,
      system_record_length] using fits
  have field := slice_serialize_record index bound
  simp only [system_offset, caller_records, List.getElem_cons_succ,
    List.getElem_cons_zero] at field
  exact field

private theorem source_initial_fields :
    slice entryState.buf 48 32 = Ids.systemProgram.bytes ∧
    slice entryState.buf 80 8 = u64le 2000000 ∧ slice entryState.buf 88 8 = u64le 0 := by
  have fields := recordV1_fields true true sourceKey
    ⟨2000000, [], Ids.systemProgram, false, 0⟩ U64_MAX
  exact ⟨(entry_source_slice 40 32 (by decide)).trans fields.2.2.1,
    (entry_source_slice 72 8 (by decide)).trans fields.2.2.2.1,
    (entry_source_slice 80 8 (by decide)).trans fields.2.2.2.2.1⟩

private theorem destination_initial_fields :
    slice entryState.buf 10384 32 = callerKey.bytes ∧
    slice entryState.buf 10416 8 = u64le 1000000 ∧ slice entryState.buf 10424 8 = u64le 0 := by
  have fields := recordV1_fields false true destinationKey
    ⟨1000000, [], callerKey, false, 0⟩ U64_MAX
  exact ⟨(entry_destination_slice 40 32 (by decide)).trans fields.2.2.1,
    (entry_destination_slice 72 8 (by decide)).trans fields.2.2.2.1,
    (entry_destination_slice 80 8 (by decide)).trans fields.2.2.2.2.1⟩

private theorem system_initial_fields :
    slice entryState.buf 20720 32 = Ids.nativeLoader.bytes ∧
    slice entryState.buf 20752 8 = u64le 1000000 ∧ slice entryState.buf 20760 8 = u64le 0 := by
  have fields := recordV1_fields false false Ids.systemProgram
    ⟨1000000, [], Ids.nativeLoader, true, 0⟩ U64_MAX
  exact ⟨(entry_system_slice 40 32 (by decide)).trans fields.2.2.1,
    (entry_system_slice 72 8 (by decide)).trans fields.2.2.2.1,
    (entry_system_slice 80 8 (by decide)).trans fields.2.2.2.2.1⟩

private theorem before_slice (off len : Nat)
    (sourceDisjoint : off + len ≤ 80 ∨ 88 ≤ off)
    (destinationDisjoint : off + len ≤ 10416 ∨ 10424 ≤ off) :
    slice beforeCpi.buf off len = slice entryState.buf off len := by
  have destinationUnchanged : slice beforeCpi.buf off len = slice afterSourceStore.buf off len := by
    rcases destinationDisjoint with before | after
    · exact slice_writeAt_left destination_store_bounds before
    · exact slice_writeAt_right destination_store_bounds after
  rw [destinationUnchanged]
  rcases sourceDisjoint with before | after
  · exact slice_writeAt_left source_store_bounds before
  · exact slice_writeAt_right source_store_bounds after

private theorem before_source_lamports : slice beforeCpi.buf 80 8 = u64le 2000010 := by
  change slice (writeAt afterSourceStore.buf 10416 (u64le 999990)) 80 8 = _
  rw [slice_writeAt_left destination_store_bounds (by decide)]
  exact slice_writeAt_self source_store_bounds

private theorem before_destination_lamports : slice beforeCpi.buf 10416 8 = u64le 999990 :=
  slice_writeAt_self destination_store_bounds

theorem prepare_accounts : prepareCallee beforeCpi.ts caller request.ix [] = .ok callee := rfl

theorem translate_accounts :
    translateInfos mainnet context beforeCpi.ts request callee = .ok prepared.translated := rfl

theorem preparation (prims : Prims) :
    cpiPrepare mainnet prims context beforeCpi.ts request = .ok prepared := rfl

theorem nonempty_translation : prepared.translated.length = 2 := rfl

theorem source_caller_view :
    callerView context beforeCpi translatedSource = (2000010, Ids.systemProgram, 0, []) := by
  change (leNat (slice beforeCpi.buf 80 8), Pubkey.ofBytes (slice beforeCpi.buf 48 32), 0, []) = _
  rw [before_source_lamports,
    before_slice 48 32 (Or.inl (by decide)) (Or.inl (by decide)), source_initial_fields.1,
    Pubkey.ofBytes_bytes]
  rfl

theorem destination_caller_view :
    callerView context beforeCpi translatedDestination = (999990, callerKey, 0, []) := by
  change (leNat (slice beforeCpi.buf 10416 8), Pubkey.ofBytes (slice beforeCpi.buf 10384 32), 0,
    []) = _
  rw [before_destination_lamports,
    before_slice 10384 32 (Or.inr (by decide)) (Or.inl (by decide)), destination_initial_fields.1,
    Pubkey.ofBytes_bytes]
  rfl

theorem source_credit :
    setLamports entryTx ⟨callerKey, 0, true, .agave_4_3_2⟩ 2000010 =
      .ok afterSourceSyncTx := rfl

theorem source_synchronization :
    updateCalleeOne mainnet context beforeCpi translatedSource =
      .ok { beforeCpi with ts := afterSourceSyncTx } := by
  unfold updateCalleeOne
  rw [source_caller_view]
  rfl

theorem destination_synchronization :
    updateCalleeOne mainnet context { beforeCpi with ts := afterSourceSyncTx }
      translatedDestination =
      .ok beforeCallee := by
  unfold updateCalleeOne
  rw [show callerView context { beforeCpi with ts := afterSourceSyncTx } translatedDestination =
    (999990, callerKey, 0, []) from destination_caller_view]
  rfl

theorem callee_synchronization :
    updateCallee mainnet context beforeCpi prepared.translated = .ok beforeCallee := by
  simp only [prepared, updateCallee, source_synchronization, destination_synchronization]

theorem callee_push : push mainnet beforeCalleeTx callee = .ok calleePushed := rfl

theorem system_debit :
    checkedSubLamports calleeEntry ⟨Ids.systemProgram, 0, true, .agave_4_3_2⟩ 25 =
      .ok afterSystemDebit := rfl

theorem system_credit :
    checkedAddLamports afterSystemDebit ⟨Ids.systemProgram, 1, true, .agave_4_3_2⟩ 25 =
      .ok afterSystemTransfer := by
  change (Except.ok { calleeEntry with
    accts := accounts 1999985 1000015
    lamportsDelta := (-25 : Int) + ((1000015 : Int) - 999990)
    touched := [1, 0, 1, 1, 0] } : Except InstrError TxState) = .ok afterSystemTransfer
  rw [show (-25 : Int) + ((1000015 : Int) - 999990) = 0 by omega]
  rfl

theorem system_transfer (prims : Prims) :
    systemProcess mainnet prims calleeEntry callee = some (.ok afterSystemTransfer) := by
  change some (match checkedSubLamports calleeEntry
      ⟨Ids.systemProgram, 0, true, .agave_4_3_2⟩ 25 with
    | .error error => Except.error error
    | .ok state => checkedAddLamports state
        ⟨Ids.systemProgram, 1, true, .agave_4_3_2⟩ 25) = _
  rw [system_debit]
  exact congrArg some system_credit

theorem callee_pop : pop afterSystemTransfer = .ok returnedTx := rfl

theorem caller_synchronization :
    updateCaller mainnet context { beforeCallee with ts := returnedTx } prepared.translated =
      .ok (afterCpi, lengths) := rfl

theorem cpi_answer : cpiAnswer afterCpi request lengths prepared.translated = answer := rfl

private theorem write_empty (buf : Bytes) (off : Nat) : writeAt buf off [] = buf := by
  simp [writeAt]

private theorem copy_lamports_bound (buf : Bytes) (ser : SerAcct) (balance : Nat)
    (fits : ser.offset + 80 ≤ buf.length) :
    ser.offset + 72 + (u64le balance).length ≤ buf.length := by
  simpa only [u64le, length_leBytes, Nat.add_assoc] using fits

private theorem copy_owner_bound (buf : Bytes) (ser : SerAcct) (balance : Nat) (owner : Pubkey)
    (fits : ser.offset + 80 ≤ buf.length) :
    ser.offset + 40 + owner.bytes.length ≤
      (writeAt buf (ser.offset + 72) (u64le balance)).length := by
  rw [length_writeAt (copy_lamports_bound buf ser balance fits), owner.length_eq]
  omega

private theorem copy_fields_length (buf : Bytes) (ser : SerAcct) (balance : Nat) (owner : Pubkey)
    (fits : ser.offset + 80 ≤ buf.length) :
    (copyFields buf ser balance owner).length = buf.length := by
  unfold copyFields
  rw [write_empty, length_writeAt (copy_owner_bound buf ser balance owner fits),
    length_writeAt (copy_lamports_bound buf ser balance fits)]

private theorem copy_fields_lamports (buf : Bytes) (ser : SerAcct) (balance : Nat) (owner : Pubkey)
    (fits : ser.offset + 80 ≤ buf.length) :
    slice (copyFields buf ser balance owner) (ser.offset + 72) 8 = u64le balance := by
  unfold copyFields
  rw [write_empty, slice_writeAt_right (copy_owner_bound buf ser balance owner fits)
    (by rw [owner.length_eq]; omega)]
  exact slice_writeAt_self (copy_lamports_bound buf ser balance fits)

private theorem copy_fields_owner (buf : Bytes) (ser : SerAcct) (balance : Nat) (owner : Pubkey)
    (fits : ser.offset + 80 ≤ buf.length) :
    slice (copyFields buf ser balance owner) (ser.offset + 40) 32 = owner.bytes := by
  unfold copyFields
  rw [write_empty]
  simpa only [owner.length_eq] using slice_writeAt_self (copy_owner_bound buf ser balance owner
    fits)

private theorem copy_fields_other (buf : Bytes) (ser : SerAcct) (balance : Nat) (owner : Pubkey)
    (fits : ser.offset + 80 ≤ buf.length) (off len : Nat)
    (disjoint : off + len ≤ ser.offset + 40 ∨ ser.offset + 80 ≤ off) :
    slice (copyFields buf ser balance owner) off len = slice buf off len := by
  unfold copyFields
  rw [write_empty]
  rcases disjoint with before | after
  · rw [slice_writeAt_left (copy_owner_bound buf ser balance owner fits) before,
      slice_writeAt_left (copy_lamports_bound buf ser balance fits) (by omega)]
  · rw [slice_writeAt_right (copy_owner_bound buf ser balance owner fits)
        (by rw [owner.length_eq]; omega),
      slice_writeAt_right (copy_lamports_bound buf ser balance fits)
        (by simp only [u64le, length_leBytes]; omega)]

private theorem source_copy_bounds : sourceSer.offset + 80 ≤ beforeCallee.buf.length := by
  change 88 ≤ beforeCpi.buf.length
  rw [before_cpi_length]
  decide

private theorem source_copy_length :
    (copyFields beforeCallee.buf sourceSer 1999985 Ids.systemProgram).length = 31056 := by
  rw [copy_fields_length _ _ _ _ source_copy_bounds]
  exact before_cpi_length

private theorem destination_copy_bounds : destinationSer.offset + 80 ≤
    (copyFields beforeCallee.buf sourceSer 1999985 Ids.systemProgram).length := by
  rw [source_copy_length]
  decide

theorem after_cpi_length : afterCpi.buf.length = 31056 := by
  change (copyFields (copyFields beforeCallee.buf sourceSer 1999985 Ids.systemProgram)
    destinationSer 1000015 callerKey).length = 31056
  rw [copy_fields_length _ _ _ _ destination_copy_bounds, source_copy_length]

private theorem after_source_lamports : slice afterCpi.buf 80 8 = u64le 1999985 := by
  calc
    slice afterCpi.buf 80 8 =
        slice (copyFields beforeCallee.buf sourceSer 1999985 Ids.systemProgram) 80 8 :=
      copy_fields_other _ _ _ _ destination_copy_bounds 80 8 (Or.inl (by decide))
    _ = u64le 1999985 := copy_fields_lamports _ _ _ _ source_copy_bounds

private theorem after_destination_lamports : slice afterCpi.buf 10416 8 = u64le 1000015 :=
  copy_fields_lamports _ _ _ _ destination_copy_bounds

private theorem after_source_owner : slice afterCpi.buf 48 32 = Ids.systemProgram.bytes := by
  calc
    slice afterCpi.buf 48 32 =
        slice (copyFields beforeCallee.buf sourceSer 1999985 Ids.systemProgram) 48 32 :=
      copy_fields_other _ _ _ _ destination_copy_bounds 48 32 (Or.inl (by decide))
    _ = Ids.systemProgram.bytes := copy_fields_owner _ _ _ _ source_copy_bounds

private theorem after_destination_owner : slice afterCpi.buf 10384 32 = callerKey.bytes :=
  copy_fields_owner _ _ _ _ destination_copy_bounds

private theorem unaltered_slice (off len : Nat)
    (sourceDisjoint : off + len ≤ 48 ∨ 88 ≤ off)
    (destinationDisjoint : off + len ≤ 10384 ∨ 10424 ≤ off) :
    slice afterCpi.buf off len = slice entryState.buf off len := by
  calc
    slice afterCpi.buf off len =
        slice (copyFields beforeCallee.buf sourceSer 1999985 Ids.systemProgram) off len :=
      copy_fields_other _ _ _ _ destination_copy_bounds off len destinationDisjoint
    _ = slice beforeCpi.buf off len :=
      copy_fields_other _ _ _ _ source_copy_bounds off len sourceDisjoint
    _ = slice entryState.buf off len := before_slice off len (by omega) (by omega)

theorem source_observation :
    loadRegion context afterCpi sourceLamportsAddr 8 = .ok (u64le 1999985) := by
  have valid : inRegion afterCpi sourceLamportsAddr 8 = true := by
    rw [inRegion, after_cpi_length]
    decide
  unfold loadRegion
  rw [ite_eq_right (by decide), valid]
  exact congrArg Except.ok after_source_lamports

theorem destination_observation :
    loadRegion context afterCpi destinationLamportsAddr 8 = .ok (u64le 1000015) := by
  have valid : inRegion afterCpi destinationLamportsAddr 8 = true := by
    rw [inRegion, after_cpi_length]
    decide
  unfold loadRegion
  rw [ite_eq_right (by decide), valid]
  exact congrArg Except.ok after_destination_lamports

private theorem source_final_values :
    bufVals .v1 afterCpi.buf sourceSer = ⟨1999985, 0, [], Ids.systemProgram⟩ := by
  unfold bufVals
  change (⟨leNat (slice afterCpi.buf 80 8), leNat (slice afterCpi.buf 88 8),
    slice afterCpi.buf 96 (leNat (slice afterCpi.buf 88 8)),
    Pubkey.ofBytes (slice afterCpi.buf 48 32)⟩ : BufVals) = _
  rw [after_source_lamports, after_source_owner,
    unaltered_slice 88 8 (Or.inr (by decide)) (Or.inl (by decide)), source_initial_fields.2.2,
    Pubkey.ofBytes_bytes]
  rfl

private theorem destination_final_values :
    bufVals .v1 afterCpi.buf destinationSer = ⟨1000015, 0, [], callerKey⟩ := by
  unfold bufVals
  change (⟨leNat (slice afterCpi.buf 10416 8), leNat (slice afterCpi.buf 10424 8),
    slice afterCpi.buf 10432 (leNat (slice afterCpi.buf 10424 8)),
    Pubkey.ofBytes (slice afterCpi.buf 10384 32)⟩ : BufVals) = _
  rw [after_destination_lamports, after_destination_owner,
    unaltered_slice 10424 8 (Or.inr (by decide)) (Or.inr (by decide)),
      destination_initial_fields.2.2,
    Pubkey.ofBytes_bytes]
  rfl

private theorem system_final_values :
    bufVals .v1 afterCpi.buf systemSer = ⟨1000000, 0, [], Ids.nativeLoader⟩ := by
  unfold bufVals
  change (⟨leNat (slice afterCpi.buf 20752 8), leNat (slice afterCpi.buf 20760 8),
    slice afterCpi.buf 20768 (leNat (slice afterCpi.buf 20760 8)),
    Pubkey.ofBytes (slice afterCpi.buf 20720 32)⟩ : BufVals) = _
  rw [unaltered_slice 20752 8 (Or.inr (by decide)) (Or.inr (by decide)), system_initial_fields.2.1,
    unaltered_slice 20760 8 (Or.inr (by decide)) (Or.inr (by decide)), system_initial_fields.2.2,
    unaltered_slice 20720 32 (Or.inr (by decide)) (Or.inr (by decide)), system_initial_fields.1,
    Pubkey.ofBytes_bytes]
  rfl

private theorem readback_head (state next : TxState) (ser : SerAcct) (account : InstrAcct)
    (rest : List SerAcct) (slot : ser.slot = .acct account)
    (step : readBackAcct .v1 .L state (setterCtxOf state 3 account .agave_4_3_2)
      (bufVals .v1 afterCpi.buf ser) ser.entryLen = .ok next) :
    readBack .v1 .L 3 afterCpi.buf state (ser :: rest) .agave_4_3_2 =
      readBack .v1 .L 3 afterCpi.buf next rest .agave_4_3_2 := by
  rw [readBack, slot]
  simp only [step]

theorem successful_readback :
    readBack context.abi context.cfg context.frame.programIdx afterCpi.buf afterCpi.ts
      context.layout context.release = .ok finalInvocationTx := by
  have source : readBackAcct .v1 .L returnedTx
      (setterCtxOf returnedTx 3 sourceAccount .agave_4_3_2)
      (bufVals .v1 afterCpi.buf sourceSer) sourceSer.entryLen = .ok returnedTx := by
    rw [source_final_values]
    rfl
  have destination : readBackAcct .v1 .L returnedTx
      (setterCtxOf returnedTx 3 destinationAccount .agave_4_3_2)
      (bufVals .v1 afterCpi.buf destinationSer) destinationSer.entryLen = .ok finalInvocationTx :=
        by
    rw [destination_final_values]
    rfl
  have system : readBackAcct .v1 .L finalInvocationTx
      (setterCtxOf finalInvocationTx 3 systemAccount .agave_4_3_2)
      (bufVals .v1 afterCpi.buf systemSer) systemSer.entryLen = .ok finalInvocationTx := by
    rw [system_final_values]
    rfl
  change readBack .v1 .L 3 afterCpi.buf returnedTx [sourceSer, destinationSer, systemSer]
    .agave_4_3_2 = _
  rw [readback_head _ _ _ _ _ rfl source, readback_head _ _ _ _ _ rfl destination,
    readback_head _ _ _ _ _ rfl system]
  rfl

theorem caller_pop : pop finalInvocationTx = .ok finalTx := rfl

/-- The System result is derived from its checked transfer semantics, including
the actual debit, credit, balanced pop and return to the caller stack. -/
theorem callee_execution (world : World) (profile : world.prof = mainnet)
    (nativeSystem : world.builtins Ids.systemProgram = some .system) :
    ProcInstr world beforeCalleeTx callee (.ok returnedTx) := by
  have dispatched : dispatch world calleeEntry callee = .builtin .system := by
    change (match world.builtins Ids.systemProgram with
      | some builtin => Dispatch.builtin builtin
      | none => Dispatch.unsupported) = .builtin .system
    rw [nativeSystem]
  have processed : systemProcess world.prof world.prims calleeEntry callee =
      some (.ok afterSystemTransfer) := by
    rw [profile]
    exact system_transfer world.prims
  have pushed : push world.prof beforeCalleeTx callee = .ok calleePushed := by
    rw [profile]
    exact callee_push
  exact Exec.run pushed (Exec.system dispatched processed)

theorem continuation_execution (world : World) :
    Invoke world context afterCpi continuation (.exit 0) (.ok finalInvocationTx) :=
  Exec.load source_observation (Exec.load destination_observation (Exec.exit0 successful_readback))

/-- A successful `Exec.cpi` with two translated accounts and observable writes
on both synchronization edges. -/
theorem cpi_execution (world : World) (profile : world.prof = mainnet)
    (nativeSystem : world.builtins Ids.systemProgram = some .system) :
    Invoke world context beforeCpi
      ((.sys (.invoke request), .sys answer) :: continuation) (.exit 0)
      (.ok finalInvocationTx) := by
  have prepare : cpiPrepare world.prof world.prims context beforeCpi.ts request =
      .ok prepared := by
    rw [profile]
    exact preparation world.prims
  have synchronizeIn : updateCallee world.prof context beforeCpi prepared.translated =
      .ok beforeCallee := by
    rw [profile]
    exact callee_synchronization
  have synchronizeOut : updateCaller world.prof context
      { beforeCallee with ts := returnedTx } prepared.translated = .ok (afterCpi, lengths) := by
    rw [profile]
    exact caller_synchronization
  have executed := Exec.cpi prepare synchronizeIn
    (callee_execution world profile nativeSystem) synchronizeOut (continuation_execution world)
  simpa only [cpi_answer] using executed

/-- The initial caller stores, complete CPI, final observations and successful
read-back form one admitted invocation trace. -/
theorem run_execution (world : World) (profile : world.prof = mainnet)
    (nativeSystem : world.builtins Ids.systemProgram = some .system) :
    Invoke world context entryState callerRun.steps callerRun.final (.ok finalInvocationTx) :=
  Exec.store source_store (Exec.store destination_store (cpi_execution world profile nativeSystem))

theorem invocation_context (world : World) (profile : world.prof = mainnet)
    (heap : world.heapSize = DEFAULT_HEAP_SIZE) :
    invCtxOf world .v1 entryTx caller = context := by
  simp only [invCtxOf, profile, heap, serialized_layout]
  rfl

theorem invocation_state (world : World) (profile : world.prof = mainnet) :
    invStateOf world .v1 entryTx caller = entryState := by
  simp only [invStateOf, profile, entryState]

/-- The only external program contract is that the loaded caller admits
`callerRun` at these entry registers. All runtime replies and the entire System
callee are checked above. This does not identify any deployed caller binary. -/
theorem complete_caller (world : World) (profile : world.prof = mainnet)
    (heap : world.heapSize = DEFAULT_HEAP_SIZE)
    (nativeSystem : world.builtins Ids.systemProgram = some .system)
    (program : Program)
    (loaded : dispatch world entryTx caller = .sbf .v1 program)
    (admits : program (entryOf world .v1 entryTx caller) callerRun) :
    ProcInstr world initialTx caller (.ok finalTx) := by
  have invoke : Invoke world (invCtxOf world .v1 entryTx caller)
      (invStateOf world .v1 entryTx caller) callerRun.steps callerRun.final
      (.ok finalInvocationTx) := by
    rw [invocation_context world profile heap, invocation_state world profile]
    exact run_execution world profile nativeSystem
  have pushed : push world.prof initialTx caller = .ok callerPushed := by
    rw [profile]
    exact caller_push
  exact Exec.run pushed (Exec.sbf loaded (by rfl) admits invoke)

theorem frame_flags : caller.FlagsConsistent ∧ callee.FlagsConsistent := by
  simp [Frame.FlagsConsistent, caller, callee, sourceAccount, destinationAccount, systemAccount]

/-- The caller and callee use different program identities and the correct
owner for every debit. The System source has no data and is a signer. -/
theorem ownership_and_authority :
    sourceKey ≠ destinationKey ∧ callerKey ≠ Ids.systemProgram ∧
    (entryTx.acct 0).owner = Ids.systemProgram ∧
    (entryTx.acct 1).owner = callerKey ∧
    (entryTx.acct 2).owner = Ids.nativeLoader ∧
    (entryTx.acct 3).owner = Ids.bpfLoaderUpgradeable ∧
    (entryTx.acct 3).data = u32le 2 ++ programDataKey.bytes ∧
    sourceAccount.signer = true ∧ sourceAccount.writable = true ∧
    destinationAccount.writable = true ∧ (entryTx.acct 0).data = [] := by decide

theorem frame_indices :
    ∀ frame ∈ [caller, callee], frame.programIdx < initialTx.accts.length ∧
      (∀ account ∈ frame.accounts, account.txIdx < initialTx.accts.length) ∧
      frame.accounts.length ≤ MAX_ACCOUNTS_PER_INSTRUCTION := by decide

theorem mainnet_configuration :
    mainnet.WF ∧ mainnet.features.pointerChecks = true ∧ mainnet.memConfig = .L ∧
      context.release = mainnet.release := by
  exact ⟨mainnet_wf, rfl, rfl, rfl⟩

theorem pointer_bounds :
    request.infosBelowInput = true ∧
      ∀ translated ∈ prepared.translated,
        translated.inRegion = true ∧ translated.info.boxesBelowInput = true ∧
        translated.info.key = entryTx.key translated.t ∧
        (translated.info.keyAddr, translated.info.ownerAddr,
          translated.info.lamportsAddr, translated.info.dataAddr) =
          serAddrs context translated.ser ∧
        translated.info.lamportsAddr % 8 = 0 ∧
        translated.info.dataLen = translated.ser.entryLen ∧
        translated.info.dataLen ≤ translated.ser.entryLen + callerMaxIncrease mainnet context ∧
        translated.info.dataAddr + translated.info.dataLen ≤ MM_INPUT_START + entryState.buf.length
          := by
  rw [serialized_length]
  decide

def boundaryStates : List TxState :=
  [initialTx, callerPushed, entryTx, afterSourceSyncTx, beforeCalleeTx,
    calleePushed, calleeEntry, afterSystemDebit, afterSystemTransfer,
    returnedTx, finalInvocationTx, finalTx]

/-- Every represented account and counter stays within the runtime integer and
account-data bounds, including the temporary nonzero balance deltas. -/
theorem state_bounds :
    ∀ state ∈ boundaryStates,
      state.keys.Nodup ∧ state.keys.length = state.accts.length ∧
      state.accts.length ≤ MAX_TX_ACCOUNTS ∧
      (∀ account ∈ state.accts, account.WF) ∧
      state.lamportSum < 2^128 ∧ -(2^127 : Int) ≤ state.lamportsDelta ∧
      state.lamportsDelta < 2^127 ∧ state.resizeDelta = 0 := by
  intro state member
  simp only [boundaryStates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold Account.WF
    decide

theorem transfer_observations :
    ((entryTx.acct 0).lamports, (entryTx.acct 1).lamports) = (2000000, 1000000) ∧
    ((beforeCalleeTx.acct 0).lamports, (beforeCalleeTx.acct 1).lamports) = (2000010, 999990) ∧
    ((returnedTx.acct 0).lamports, (returnedTx.acct 1).lamports) = (1999985, 1000015) ∧
    ((finalTx.acct 0).lamports, (finalTx.acct 1).lamports) = (1999985, 1000015) := by decide

theorem final_invariants :
    finalTx.lamportSum = initialTx.lamportSum ∧ finalTx.lamportsDelta = 0 ∧
    finalTx.resizeDelta = 0 ∧ finalTx.stack = [] ∧ finalTx.topIndex = 1 ∧
    finalTx.trace = [⟨1, caller⟩, ⟨2, callee⟩] ∧
    finalTx.returnData = (Ids.systemProgram, []) ∧
    finalTx.acct 2 = initialTx.acct 2 ∧ finalTx.acct 3 = initialTx.acct 3 ∧
    finalTx.touched = [1, 1, 0, 1, 1, 0] := by decide

/-- The complete witness also instantiates the general instruction frame
theorem; only the two writable accounts can change. -/
theorem complete_caller_frame (world : World) (profile : world.prof = mainnet)
    (heap : world.heapSize = DEFAULT_HEAP_SIZE)
    (nativeSystem : world.builtins Ids.systemProgram = some .system)
    (program : Program)
    (loaded : dispatch world entryTx caller = .sbf .v1 program)
    (admits : program (entryOf world .v1 entryTx caller) callerRun) :
    ExecChanges initialTx finalTx (MayChange initialTx.keys caller) :=
  (complete_caller world profile heap nativeSystem program loaded admits).frame finalTx rfl

/-- A supplied caller behavior contract with exactly the concrete run. This is
an opaque program contract, not a claim about a deployed executable image. -/
def callerProgram : Program := fun _ run => run = callerRun

/-- Reuse the checked bank configuration, sysvars and unused primitive fields
of the transaction witness. Supply only the explicit caller behavior in the
initial cache; no execution result is stored in the environment. -/
def witnessWorld : World :=
  { TransactionSuccessTest.bank.world TransactionSuccessTest.tx with
    programs := fun key => if key = callerKey then .sbf callerProgram else .notDeployed }

theorem witness_world_wf : witnessWorld.WF :=
  ⟨TransactionSuccessTest.world_well_formed.profile,
    TransactionSuccessTest.world_well_formed.sysvars,
    TransactionSuccessTest.world_well_formed.rent,
    TransactionSuccessTest.world_well_formed.builtins⟩

theorem witness_program_loaded :
    dispatch witnessWorld entryTx caller = .sbf .v1 callerProgram := rfl

theorem witness_run_admitted :
    callerProgram (entryOf witnessWorld .v1 entryTx caller) callerRun := rfl

/-- A closed successful instruction witness. In particular, the loaded caller
and admitted run premises of `complete_caller` are inhabited here. -/
theorem closed_execution : ProcInstr witnessWorld initialTx caller (.ok finalTx) :=
  complete_caller witnessWorld rfl rfl rfl callerProgram witness_program_loaded witness_run_admitted

theorem closed_cpi_execution :
    Invoke witnessWorld context beforeCpi
      ((.sys (.invoke request), .sys answer) :: continuation) (.exit 0)
      (.ok finalInvocationTx) :=
  cpi_execution witnessWorld rfl rfl

theorem closed_frame : ExecChanges initialTx finalTx (MayChange initialTx.keys caller) :=
  closed_execution.frame finalTx rfl

/-- The successful case simultaneously inhabits the runtime relation, translates
both accounts and observes the actual 25-lamport transfer after synchronization. -/
theorem successful_cpi_witness :
    witnessWorld.WF ∧ ProcInstr witnessWorld initialTx caller (.ok finalTx) ∧
    prepared.translated.length = 2 ∧
    loadRegion context afterCpi sourceLamportsAddr 8 = .ok (u64le 1999985) ∧
    loadRegion context afterCpi destinationLamportsAddr 8 = .ok (u64le 1000015) ∧
    finalTx.lamportSum = initialTx.lamportSum ∧ finalTx.lamportsDelta = 0 :=
  ⟨witness_world_wf, closed_execution, nonempty_translation, source_observation,
    destination_observation, final_invariants.1, final_invariants.2.1⟩

end SolanalibTest.Runtime.CpiSuccess
