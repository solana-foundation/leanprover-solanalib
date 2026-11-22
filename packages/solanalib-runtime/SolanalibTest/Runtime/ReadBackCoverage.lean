/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.WritesLegal

@[expose] public section

/-!
# Composed read-back witnesses

Closed examples check the complete `readBack` traversal, its write obligations,
duplicate handling and the data paths of the three memory configurations. The
S/D examples concern the represented read-back operation; source memory mapping
still has the correspondence premises recorded by the model.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

open Solanalib.Runtime

namespace SolanalibTest.Runtime.ReadBackCoverageTest

def address : Pubkey := Pubkey.ofNat 10
def program : Pubkey := Pubkey.ofNat 20
def newOwner : Pubkey := Pubkey.ofNat 30

def instructionAccount : InstrAcct := ⟨0, true, true⟩

def singleFrame : Frame :=
  { programIdx := 1, accounts := [instructionAccount], data := [] }

def duplicateFrame : Frame :=
  { singleFrame with accounts := [instructionAccount, instructionAccount] }

def entryAccount : Account := ⟨1000000, [9], program, false, 7⟩
def programAccount : Account := ⟨1, [], Ids.bpfLoaderUpgradeable, true, 0⟩

def entryState (frame : Frame) : TxState :=
  { keys := [address, program], accts := [entryAccount, programAccount],
    lamportsDelta := 0, resizeDelta := 0, stack := [frame], trace := [⟨1, frame⟩],
    returnData := (program, []), topIndex := 0 }

def singleState : TxState := entryState singleFrame
def duplicateState : TxState := entryState duplicateFrame

def singleLayout : List SerAcct := layout .v1 mainnet singleState singleFrame
def duplicateLayout : List SerAcct := layout .v1 mainnet duplicateState duplicateFrame

def firstSlot : SerAcct :=
  { pos := 0, ia := instructionAccount, slot := .acct instructionAccount,
    offset := 8, entryLen := 1 }

def repeatedSlot : SerAcct :=
  { pos := 1, ia := instructionAccount, slot := .dup 0, offset := 10352, entryLen := 1 }

/-- The original serialized buffer is edited in place. The new zero data allows
the same owned account to change balance, data length and owner at read-back. -/
def edited (owner : Pubkey) (state : TxState) (frame : Frame) : Bytes :=
  writeAt
    (writeAt
      (writeAt
        (writeAt (serialize .v1 mainnet state frame) 80 (u64le 1000005))
        88 (u64le 3))
      96 [0, 0, 0])
    48 owner.bytes

def changedBuffer : Bytes := edited newOwner singleState singleFrame
def duplicateBuffer : Bytes := edited program duplicateState duplicateFrame

def changedValues : BufVals := ⟨1000005, 3, [0, 0, 0], newOwner⟩
def duplicateValues : BufVals := ⟨1000005, 3, [0, 0, 0], program⟩

def changedAccount : Account := applied entryAccount changedValues
def duplicateAccount : Account := applied entryAccount duplicateValues

def changedState : TxState :=
  { singleState with
    accts := [changedAccount, programAccount]
    lamportsDelta := 5
    resizeDelta := 2
    touched := [0, 0, 0] }

def duplicateResult : TxState :=
  { duplicateState with
    accts := [duplicateAccount, programAccount]
    lamportsDelta := 5
    resizeDelta := 2
    touched := [0, 0] }

theorem configuration_l : mainnet.memConfig = .L := rfl

theorem entry_invariants :
    singleState.keys.Nodup ∧ singleState.keys.length = singleState.accts.length ∧
    entryAccount.WF ∧ programAccount.WF ∧ singleFrame.FlagsConsistent ∧
    singleFrame.programIdx < singleState.keys.length ∧
    instructionAccount.txIdx < singleState.accts.length := by
  refine ⟨by decide, rfl, by unfold Account.WF; decide,
    by unfold Account.WF; decide, ?_, by decide, by decide⟩
  intro left hl right hr _
  simp only [singleFrame, List.mem_singleton] at hl hr
  exact hl.trans hr.symm

theorem single_layout : singleLayout = [firstSlot] := rfl

theorem duplicate_layout : duplicateLayout = [firstSlot, repeatedSlot] := by
  simp [duplicateLayout, layout, duplicateFrame, singleFrame, instructionAccount,
    slotOf, Frame.firstIdx, List.findIdx?_cons, recordOffset, records, slots, prefixLen,
    slotRecord, length_recordV1, entryState, duplicateState, TxState.acct, entryAccount,
    pad8, MAX_PERMITTED_DATA_INCREASE, firstSlot, repeatedSlot]

theorem duplicate_invariants :
    duplicateFrame.FlagsConsistent ∧ duplicateState.keys.Nodup ∧
    NonDupDistinct duplicateLayout := by
  refine ⟨?_, by decide, layout_nonDupDistinct .v1 mainnet duplicateState duplicateFrame⟩
  intro left hl right hr _
  simp only [duplicateFrame, singleFrame, List.mem_cons, List.not_mem_nil,
    or_false, or_self] at hl hr
  exact hl.trans hr.symm

theorem serialized_extent :
    (serialize .v1 mainnet singleState singleFrame).length = 10392 := by
  change (serializeBody .v1 mainnet singleState singleFrame).length = 10392
  simp [serializeBody, records, slots, singleFrame, instructionAccount, slotOf,
    Frame.firstIdx, List.findIdx?_cons, slotRecord, length_recordV1, singleState,
    entryState, TxState.acct, entryAccount, pad8, MAX_PERMITTED_DATA_INCREASE,
    u64le, TxState.key, Pubkey.length_eq]

/-- Every edit stays inside the buffer allocated at entry. No successful slice
or shorter replacement buffer is assumed by the legality witness. -/
theorem edited_extent : changedBuffer.length = 10392 := by
  have keep (bytes : Bytes) (length : bytes.length = 10392) (offset : Nat) (data : Bytes)
      (bounded : offset + data.length ≤ 10392) : (writeAt bytes offset data).length = 10392 := by
    rw [length_writeAt (by simpa only [length] using bounded), length]
  unfold changedBuffer edited
  apply keep
  · apply keep
    · apply keep
      · apply keep
        · exact serialized_extent
        · decide
      · decide
    · decide
  · decide

theorem changed_values : bufVals .v1 changedBuffer firstSlot = changedValues := rfl

theorem duplicate_values :
    bufVals .v1 duplicateBuffer firstSlot = duplicateValues := rfl

theorem changed_account_legal :
    AcctLegal (singleState.acct 0) (singleState.key 1) true 1 changedValues := by
  refine ⟨Or.inr ⟨rfl, Or.inl rfl⟩, by decide, rfl,
    Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl, rfl⟩⟩

theorem duplicate_account_legal :
    AcctLegal (duplicateState.acct 0) (duplicateState.key 1) true 1 duplicateValues := by
  refine ⟨Or.inr ⟨rfl, Or.inl rfl⟩, by decide, rfl,
    Or.inr ⟨rfl, rfl⟩, Or.inl rfl⟩

theorem changed_writes_legal : WritesLegalL 1 changedBuffer singleState singleLayout := by
  rw [single_layout]
  refine ⟨?_, ?_⟩
  · intro slot member ia same
    have : slot = firstSlot := List.mem_singleton.mp member
    subst slot
    cases same
    rw [changed_values]
    exact changed_account_legal
  · simp only [growth, firstSlot]
    decide

theorem duplicate_writes_legal :
    WritesLegalL 1 duplicateBuffer duplicateState duplicateLayout := by
  rw [duplicate_layout]
  refine ⟨?_, ?_⟩
  · intro slot member ia same
    rcases List.mem_cons.mp member with rfl | member
    · cases same
      rw [duplicate_values]
      exact duplicate_account_legal
    · have : slot = repeatedSlot := List.mem_singleton.mp member
      subst slot
      cases same
  · simp only [growth, firstSlot, repeatedSlot]
    decide

theorem single_indices_valid :
    ∀ slot ∈ singleLayout, ∀ ia, slot.slot = .acct ia → ia.txIdx < singleState.accts.length := by
  rw [single_layout]
  intro slot member ia same
  have : slot = firstSlot := List.mem_singleton.mp member
  subst slot
  cases same
  decide

theorem duplicate_indices_valid :
    ∀ slot ∈ duplicateLayout, ∀ ia,
      slot.slot = .acct ia → ia.txIdx < duplicateState.accts.length := by
  rw [duplicate_layout]
  intro slot member ia same
  rcases List.mem_cons.mp member with rfl | member
  · cases same
    decide
  · have : slot = repeatedSlot := List.mem_singleton.mp member
    subst slot
    cases same

/-- The general composition theorem is instantiated with proved legality,
actual generated-layout distinctness and valid account indices. -/
theorem changed_from_legal :
    ∃ result, readBack .v1 .L 1 changedBuffer singleState singleLayout = .ok result ∧
      result.acct 0 = changedAccount := by
  obtain ⟨result, run, accounts, _, _, _⟩ :=
    readBackL_of_legal singleLayout singleState
      (layout_nonDupDistinct .v1 mainnet singleState singleFrame)
      single_indices_valid changed_writes_legal
  refine ⟨result, run, ?_⟩
  have effect := accounts firstSlot (by rw [single_layout]; simp) instructionAccount rfl
  simpa [changed_values, instructionAccount, changedAccount, singleState, entryState,
    TxState.acct] using effect

theorem duplicate_from_legal :
    ∃ result, readBack .v1 .L 1 duplicateBuffer duplicateState duplicateLayout = .ok result ∧
      result.acct 0 = duplicateAccount := by
  obtain ⟨result, run, accounts, _, _, _⟩ :=
    readBackL_of_legal duplicateLayout duplicateState
      (layout_nonDupDistinct .v1 mainnet duplicateState duplicateFrame)
      duplicate_indices_valid duplicate_writes_legal
  refine ⟨result, run, ?_⟩
  have effect := accounts firstSlot (by rw [duplicate_layout]; simp) instructionAccount rfl
  simpa [duplicate_values, instructionAccount, duplicateAccount, duplicateState, entryState,
    TxState.acct] using effect

/-- All three changed account fields and all bookkeeping fields are checked
against a concrete final state, not an assumed successful result. -/
theorem changed_readBack :
    readBack .v1 .L 1 changedBuffer singleState singleLayout = .ok changedState := rfl

theorem changed_effects :
    changedState.acct 0 = ⟨1000005, [0, 0, 0], newOwner, false, 7⟩ ∧
    changedState.acct 1 = programAccount ∧ changedState.lamportsDelta = 5 ∧
    changedState.resizeDelta = 2 ∧ changedState.touched = [0, 0, 0] ∧
    (changedState.lamportSum : Int) - changedState.lamportsDelta =
      (singleState.lamportSum : Int) - singleState.lamportsDelta := by
  decide

theorem duplicate_readBack :
    readBack .v1 .L 1 duplicateBuffer duplicateState duplicateLayout = .ok duplicateResult := by
  rw [duplicate_layout]
  rfl

/-- A repeated instruction reference causes no second data setter or second
resize/balance delta. Keeping the same owner makes an accidental repeated data
setter observable through an additional touch. -/
theorem duplicate_is_single_application :
    readBack .v1 .L 1 duplicateBuffer duplicateState duplicateLayout =
      readBack .v1 .L 1 duplicateBuffer duplicateState [firstSlot] ∧
    growth duplicateState duplicateBuffer duplicateLayout = 2 ∧
    duplicateResult.lamportsDelta = 5 ∧ duplicateResult.resizeDelta = 2 ∧
    duplicateResult.touched = [0, 0] := by
  rw [duplicate_layout]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def splitProfile : Profile :=
  { mainnet with features := { mainnet.features with addressSpace := true, directMapping := false }
    }

def directProfile : Profile :=
  { mainnet with features := { mainnet.features with addressSpace := true, directMapping := true } }

theorem alternate_configurations :
    splitProfile.memConfig = .S ∧ directProfile.memConfig = .D ∧
    splitProfile.WF ∧ directProfile.WF := by
  exact ⟨rfl, rfl, mainnet_wf, mainnet_wf⟩

/-- The complete split-region read-back copies owned data and then changes the
owner, producing the same concrete state as configuration L. -/
theorem split_readBack :
    readBack .v1 splitProfile.memConfig 1 changedBuffer singleState
      (layout .v1 splitProfile singleState singleFrame) = .ok changedState := rfl

def directBefore : TxState :=
  { singleState with
    accts := [{ entryAccount with data := [7, 8] }, programAccount]
    resizeDelta := 1
    touched := [0] }

def directBuffer : Bytes :=
  writeAt (writeAt (serialize .v1 mainnet singleState singleFrame) 80 (u64le 1000005))
    88 (u64le 3)

def directAccount : Account := { entryAccount with lamports := 1000005, data := [7, 8, 0] }

def directResult : TxState :=
  { directBefore with
    accts := [directAccount, programAccount]
    lamportsDelta := 5
    resizeDelta := 2
    touched := [0, 0, 0] }

/-- The live direct-mapped data state is itself produced by an actual checked
mutation. Its bytes differ from the preserved serialized buffer. -/
theorem direct_before_reachable :
    setDataFromSlice singleState (setterCtxOf singleState 1 instructionAccount) [7, 8] =
      .ok directBefore := rfl

/-- Direct read-back resizes the live account, zero-fills one byte and does not
replace its bytes with the stale serialized data. -/
theorem direct_readBack :
    readBack .v1 directProfile.memConfig 1 directBuffer directBefore
      (layout .v1 directProfile singleState singleFrame) = .ok directResult := rfl

theorem direct_effects :
    (bufVals .v1 directBuffer firstSlot).data = [9, 0, 0] ∧
    (directResult.acct 0).data = [7, 8, 0] ∧ directResult.resizeDelta = 2 ∧
    directResult.lamportsDelta = 5 ∧ directResult.touched = [0, 0, 0] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def deprecatedState : TxState :=
  { singleState with accts := [entryAccount,
    { programAccount with owner := Ids.bpfLoaderDeprecated }] }

def deprecatedBuffer : Bytes :=
  writeAt
    (writeAt
      (writeAt
        (writeAt (serialize .v0 mainnet deprecatedState singleFrame) 43 (u64le 1000005))
        51 (u64le U64_MAX))
      59 [5])
    60 newOwner.bytes

def deprecatedResult : TxState :=
  { deprecatedState with
    accts := [{ entryAccount with lamports := 1000005, data := [5] },
      { programAccount with owner := Ids.bpfLoaderDeprecated }]
    lamportsDelta := 5
    touched := [0, 0] }

theorem deprecated_abi : abiOfOwner (deprecatedState.acct 1).owner = .v0 := rfl

/-- ABI v0 has no realloc reserve: the owner immediately follows the one data
byte, and the buffer for the single instruction account is only 141 bytes. -/
theorem deprecated_no_padding :
    (serialize .v0 mainnet deprecatedState singleFrame).length = 141 ∧
    Abi.reserved .v0 1 = 1 ∧ Abi.maxIncrease .v0 = 0 ∧ Abi.ownerOff .v0 1 = 52 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Even a maximal encoded length and a changed owner are ignored by ABI v0.
The original one-byte data extent is retained and its contents are updated. -/
theorem deprecated_readBack :
    readBack .v0 .L 1 deprecatedBuffer deprecatedState
      (layout .v0 mainnet deprecatedState singleFrame) = .ok deprecatedResult := rfl

theorem deprecated_effects :
    (deprecatedResult.acct 0).owner = program ∧
    (deprecatedResult.acct 0).data = [5] ∧ deprecatedResult.resizeDelta = 0 ∧
    deprecatedResult.lamportsDelta = 5 ∧ deprecatedResult.touched = [0, 0] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end SolanalibTest.Runtime.ReadBackCoverageTest
