/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.ReadBack

@[expose] public section

/-!
# The input region

The program accesses its input region through loads and stores, which the runtime
answers according to the represented memory configuration:

- In configuration L the region is one writable byte string.
- In configurations S and D each account has a data region whose length is the current
  data length of the account, writable when `can_data_be_changed` succeeds.
  A store past that length within the reserved space grows the account through the
  access-violation handler, and every other access past it faults.
- In configuration D the data region is the storage of the account in the transaction
  context, so stores reach the account at once.

A fault inside the reserved data range of an account becomes an instruction error, as
`execute` maps it in Agave 4.3.2, `program-runtime/src/vm.rs`; any
other fault becomes `ProgramFailedToComplete`.
The current source correspondence selects configuration L. Configurations S and D
also require the translation-time mutation behavior described in
[memory](../../source-notes/agave-4.3.2.md#memory); in particular, syscall destinations
can trigger account growth before the syscall writes its result.
-/

namespace Solanalib.Runtime

/-- The context of one program invocation, fixed when the loader serializes the input. -/
structure InvCtx where
  abi : Abi
  cfg : MemConfig
  frame : Frame
  layout : List SerAcct
  /-- The heap size of the transaction: 32 KiB, or the value of `RequestHeapFrame`. -/
  heapSize : Nat
  release : Release := .agave_4_3_2
  deriving Repr

/-- The state of an invocation. -/
structure InvState where
  ts : TxState
  /-- The bytes of the input region in the layout of configuration L. In configuration D
  the data bytes of the region are those of the accounts, and these bytes are unused. -/
  buf : Bytes
  /-- The position of the bump allocator of `sol_alloc_free_`. -/
  heapPos : Nat
  /-- The log messages, in order; the model keeps their arguments and no formatting. -/
  logs : List Bytes
  deriving Repr

namespace InvCtx

/-- The offset of the data of position `s`. -/
def dataStart (c : InvCtx) (s : SerAcct) : Nat := s.offset + c.abi.dataOff

/-- The address space reserved for the data of position `s`. -/
def reserved (c : InvCtx) (s : SerAcct) : Nat := c.abi.reserved s.entryLen

/-- Whether offset `o` lies in the reserved data range of a non-duplicate position. -/
def inData (c : InvCtx) (o : Nat) (s : SerAcct) : Bool :=
  match s.slot with
  | .acct _ => decide (c.dataStart s ≤ o ∧ o < c.dataStart s + c.reserved s)
  | .dup _ => false

/-- The non-duplicate position whose reserved data range contains offset `o`. -/
def dataAreaOf (c : InvCtx) (o : Nat) : Option SerAcct := c.layout.find? (c.inData o)

/-- Whether the bytes `[o, o + n)` meet the reserved data range of some position. -/
def overlapsData (c : InvCtx) (o n : Nat) : Bool :=
  c.layout.any fun s => match s.slot with
    | .acct _ => decide (o < c.dataStart s + c.reserved s ∧ c.dataStart s < o + n)
    | .dup _ => false

/-- The setter context of instruction account `ia` in the current instruction. -/
def setterCtx (c : InvCtx) (ts : TxState) (ia : InstrAcct) : SetterCtx :=
  setterCtxOf ts c.frame.programIdx ia c.release

end InvCtx

/-- Whether the VM range `[addr, addr + n)` lies in the input region of `st`. -/
def inRegion (st : InvState) (addr n : Nat) : Bool :=
  decide (MM_INPUT_START ≤ addr ∧ addr - MM_INPUT_START + n ≤ st.buf.length)

/-- The error of a fault inside the reserved data range of an account: for a store, the
error of `can_data_be_changed`, or `InvalidRealloc`; for a load, `AccountDataTooSmall`
when the data cannot change, or `InvalidRealloc`. -/
def dataFault (ts : TxState) (sc : SetterCtx) (isStore : Bool) : InstrError :=
  match canDataBeChanged ts sc, isStore with
  | .error e, true => e
  | .ok (), true => .InvalidRealloc
  | .error _, false => .AccountDataTooSmall
  | .ok (), false => .InvalidRealloc

/-- A load of `n` bytes at VM address `addr` from the input region. -/
def loadRegion (c : InvCtx) (st : InvState) (addr n : Nat) : Except InstrError Bytes :=
  if n = 0 then .ok []
  else if inRegion st addr n = false then .error .ProgramFailedToComplete
  else
    let o := addr - MM_INPUT_START
    match c.cfg with
    | .L => .ok (slice st.buf o n)
    | cfg =>
      match c.dataAreaOf o with
      | none =>
        if c.overlapsData o n then .error .ProgramFailedToComplete else .ok (slice st.buf o n)
      | some s =>
        match s.slot with
        | .dup _ => .error .ProgramFailedToComplete
        | .acct ia =>
          let a := st.ts.acct ia.txIdx
          if o + n ≤ c.dataStart s + a.data.length then
            .ok (if cfg = .D then slice a.data (o - c.dataStart s) n else slice st.buf o n)
          else if o + n ≤ c.dataStart s + c.reserved s then
            .error (dataFault st.ts (c.setterCtx st.ts ia) false)
          else .error .ProgramFailedToComplete

/-- The growth of the access-violation handler: the account grows to the end of its
reserved space, bounded by 10 MiB and by the remaining transaction allowance, with
zero fill, following `TransactionContext::access_violation_handler` in Agave 4.3.2,
`transaction-context/src/transaction.rs`. -/
def handlerGrow (ts : TxState) (t reserved : Nat) : TxState :=
  let a := ts.acct t
  let remaining := ((MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION : Int) - ts.resizeDelta).toNat
  let newLen := min (min reserved MAX_ACCOUNT_DATA_LEN) (a.data.length + remaining)
  { ts.setAcct t { a with data := resizeZero a.data newLen } with
    resizeDelta := ts.resizeDelta + ((newLen : Int) - a.data.length) }

/-- The data of account `t` with `bs` written at offset `off`, as configuration D
performs a store: the region maps the account storage, and the handler has made that
storage unique. -/
def writeAcctData (ts : TxState) (t off : Nat) (bs : Bytes) : TxState :=
  ts.setAcct t { ts.acct t with data := writeAt (ts.acct t).data off bs }

/-- The handler growth that a store ending past the current length triggers. -/
def growIfNeeded (c : InvCtx) (ts : TxState) (o : Nat) (bs : Bytes) (s : SerAcct)
    (ia : InstrAcct) : TxState :=
  if (ts.acct ia.txIdx).data.length < o + bs.length - c.dataStart s then
    handlerGrow ts ia.txIdx (c.reserved s)
  else ts

/-- The store after the handler: it faults with `InvalidRealloc` when the grown length
still does not cover it. -/
def storeGrown (c : InvCtx) (st : InvState) (ts1 : TxState) (o : Nat) (bs : Bytes)
    (s : SerAcct) (ia : InstrAcct) : Except InstrError InvState :=
  if (ts1.acct ia.txIdx).data.length < o + bs.length - c.dataStart s then .error .InvalidRealloc
  else if c.cfg = .D then .ok { st with ts := writeAcctData ts1 ia.txIdx (o - c.dataStart s) bs }
  else .ok { st with ts := ts1, buf := writeAt st.buf o bs }

/-- A store into the reserved data range of position `s`, in configurations S and D. -/
def storeData (c : InvCtx) (st : InvState) (o : Nat) (bs : Bytes) (s : SerAcct)
    (ia : InstrAcct) : Except InstrError InvState :=
  if c.dataStart s + c.reserved s < o + bs.length then .error .ProgramFailedToComplete
  else
    match canDataBeChanged st.ts (c.setterCtx st.ts ia) with
    | .error e => .error e
    | .ok () => storeGrown c st (growIfNeeded c st.ts o bs s ia) o bs s ia

/-- A store at offset `o` of the input region. -/
def storeAt (c : InvCtx) (st : InvState) (o : Nat) (bs : Bytes) : Except InstrError InvState :=
  match c.cfg with
  | .L => .ok { st with buf := writeAt st.buf o bs }
  | _ =>
    match c.dataAreaOf o with
    | none =>
      if c.overlapsData o bs.length then .error .ProgramFailedToComplete
      else .ok { st with buf := writeAt st.buf o bs }
    | some s =>
      match s.slot with
      | .dup _ => .error .ProgramFailedToComplete
      | .acct ia => storeData c st o bs s ia

/-- A store of `bs` at VM address `addr` into the input region. -/
def storeRegion (c : InvCtx) (st : InvState) (addr : Nat) (bs : Bytes) : Except InstrError InvState
  :=
  if bs.length = 0 then .ok st
  else if inRegion st addr bs.length = false then .error .ProgramFailedToComplete
  else storeAt c st (addr - MM_INPUT_START) bs

/-! ## What a store changes -/

/-- The replacement of account `t` by an account with the same balance. -/
theorem Changes.of_setAcct {ts ts' : TxState} {t : Nat} {a : Account}
    (hk : ts'.keys = ts.keys) (ha : ts'.accts = ts.accts.set t a)
    (hd : ts'.lamportsDelta = ts.lamportsDelta) (hs : ts'.stack = ts.stack)
    (htr : ts'.trace = ts.trace) (hr : ts'.returnData = ts.returnData)
    (ht : ts'.topIndex = ts.topIndex) (hl : a.lamports = (ts.acct t).lamports)
    (touches : TouchChanges ts ts') :
    Changes ts ts' (· = t) := by
  refine ⟨hk, hs, htr, hr, ht, by simp [ha], fun j hj => ?_, ?_, touches⟩
  · have := TxState.acct_setAcct_ne ts t j a (Ne.symm hj)
    simp only [TxState.acct, TxState.setAcct] at this ⊢
    rw [ha]; exact this
  · simp only [TxState.lamportSum] at ⊢
    rw [ha, hd]
    by_cases hi : t < ts.accts.length
    · have := lamportSum_setAcct ts t a hi
      simp only [TxState.lamportSum, TxState.setAcct] at this
      omega
    · rw [List.set_eq_of_length_le (by omega)]

theorem Changes.of_handlerGrow (ts : TxState) (t r : Nat) :
    Changes ts (handlerGrow ts t r) (· = t) :=
  Changes.of_setAcct rfl rfl rfl rfl rfl rfl rfl rfl (TouchChanges.of_update rfl rfl rfl)

theorem Changes.of_writeAcctData (ts : TxState) (t off : Nat) (bs : Bytes) :
    Changes ts (writeAcctData ts t off bs) (· = t) :=
  Changes.of_setAcct rfl rfl rfl rfl rfl rfl rfl rfl (TouchChanges.of_update rfl rfl rfl)

theorem Changes.of_growIfNeeded (c : InvCtx) (ts : TxState) (o : Nat) (bs : Bytes) (s : SerAcct)
    (ia : InstrAcct) : Changes ts (growIfNeeded c ts o bs s ia) (· = ia.txIdx) := by
  unfold growIfNeeded
  split
  · exact Changes.of_handlerGrow _ _ _
  · exact Changes.refl _ _

theorem Changes.of_storeData {c : InvCtx} {st st' : InvState} {o : Nat} {bs : Bytes}
    {s : SerAcct} {ia : InstrAcct} (h : storeData c st o bs s ia = .ok st') :
    Changes st.ts st'.ts (fun j => j = ia.txIdx ∧ ia.writable = true) := by
  unfold storeData at h
  split at h
  · cases h
  · cases hc : canDataBeChanged st.ts (c.setterCtx st.ts ia) with
    | error e => simp [hc] at h
    | ok u =>
      have hc' : canDataBeChanged st.ts (c.setterCtx st.ts ia) = .ok () := hc
      have hw : ia.writable = true := canDataBeChanged_writable hc'
      simp only [hc'] at h
      have hg := (Changes.of_growIfNeeded c st.ts o bs s ia).mono
        (W' := fun j => j = ia.txIdx ∧ ia.writable = true) (fun j hj => ⟨hj, hw⟩)
      unfold storeGrown at h
      split at h
      · cases h
      · split at h
        · cases h
          exact hg.trans ((Changes.of_writeAcctData _ _ _ _).mono fun j hj => ⟨hj, hw⟩)
        · cases h; exact hg

/-- A store changes only accounts whose data the current program may change: the
growth of the handler and the stores of configuration D require `can_data_be_changed`. -/
theorem Changes.of_storeRegion {c : InvCtx} {st st' : InvState} {addr : Nat} {bs : Bytes}
    (h : storeRegion c st addr bs = .ok st') : Changes st.ts st'.ts (WritableIn c.layout) := by
  unfold storeRegion at h
  split at h
  · cases h; exact Changes.refl _ _
  · split at h
    · cases h
    · unfold storeAt at h
      split at h
      · cases h; exact Changes.refl _ _
      · split at h
        · split at h
          · cases h
          · cases h; exact Changes.refl _ _
        · rename_i s hs
          split at h
          · cases h
          · rename_i ia hslot
            have hmem : s ∈ c.layout := List.mem_of_find?_eq_some hs
            exact (Changes.of_storeData h).mono fun j ⟨hj, hw⟩ => ⟨s, hmem, ia, hslot, hj.symm, hw⟩

end Solanalib.Runtime
