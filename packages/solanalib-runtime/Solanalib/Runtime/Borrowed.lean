/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Context

@[expose] public section

/-!
# The checks of `BorrowedAccount`

The setters through which the runtime applies program mutations of an account: read-back
at the end of an instruction, both edges of a CPI, and the builtin programs.
Each function follows the account setters in Agave 4.3.2. The setter context retains
the release so that 3.1.12 and 4.1.2 keep their earlier resize-error precedence.
The source mapping and the required bounded-state premises are in
[account mutation](../../source-notes/agave-4.3.2.md#account-mutation).

The main results are the lemmas `SetterStep.of_*`: a setter that succeeds changes only
its own account, required the writable flag, and keeps the balance invariant
`lamportSum - lamportsDelta`.
-/

namespace Solanalib.Runtime

/-- `set_lamports`. A call on an account outside the transaction fails with
`MissingAccount`, as `try_borrow_instruction_account` does. `SetterStep.balance`
proves the invariant for mathematical integers; the correspondence with the
runtime `i128` counter also requires bounded account counts and `u64` balances. -/
def setLamports (ts : TxState) (sc : SetterCtx) (v : Nat) : Except InstrError TxState :=
  if sc.txIdx < ts.accts.length then
    if sc.owned ts = false ∧ v < (ts.acct sc.txIdx).lamports then .error
      .ExternalAccountLamportSpend
    else if sc.writable = false then .error .ReadonlyLamportChange
    else if v = (ts.acct sc.txIdx).lamports then .ok ts
    else .ok { ts.setAcct sc.txIdx { ts.acct sc.txIdx with lamports := v } with
      lamportsDelta := ts.lamportsDelta + ((v : Int) - (ts.acct sc.txIdx).lamports) }
  else .error .MissingAccount

/-- `checked_add_lamports`. -/
def checkedAddLamports (ts : TxState) (sc : SetterCtx) (n : Nat) : Except InstrError TxState :=
  if U64_LIMIT ≤ (ts.acct sc.txIdx).lamports + n then .error .ArithmeticOverflow
  else setLamports ts sc ((ts.acct sc.txIdx).lamports + n)

/-- `checked_sub_lamports`. -/
def checkedSubLamports (ts : TxState) (sc : SetterCtx) (n : Nat) : Except InstrError TxState :=
  if (ts.acct sc.txIdx).lamports < n then .error .ArithmeticOverflow
  else setLamports ts sc ((ts.acct sc.txIdx).lamports - n)

/-- `can_data_be_changed`. -/
def canDataBeChanged (ts : TxState) (sc : SetterCtx) : Except InstrError Unit :=
  if sc.writable = false then .error .ReadonlyDataModified
  else if sc.owned ts = false then .error .ExternalAccountDataModified
  else .ok ()

/-- The transaction-wide part of `can_data_be_resized` in Agave 4.3.2,
`transaction-context/src/transaction_accounts.rs`. -/
def txCanDataBeResized (ts : TxState) (oldLen newLen : Nat) : Except InstrError Unit :=
  if MAX_ACCOUNT_DATA_LEN < newLen then .error .InvalidRealloc
  else if (MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION : Int) < ts.resizeDelta + ((newLen : Int) -
    oldLen)
    then .error .MaxAccountsDataAllocationsExceeded
  else .ok ()

/-- `can_data_be_resized`. -/
def canDataBeResized (ts : TxState) (sc : SetterCtx) (newLen : Nat) : Except InstrError Unit :=
  if sc.release ≠ .agave_4_3_2 ∧
      newLen ≠ (ts.acct sc.txIdx).data.length ∧ sc.owned ts = false then .error
        .AccountDataSizeChanged
  else match txCanDataBeResized ts (ts.acct sc.txIdx).data.length newLen with
    | .error e => .error e
    | .ok () => canDataBeChanged ts sc

/-- `set_data_from_slice`. -/
def setDataFromSlice (ts : TxState) (sc : SetterCtx) (d : Bytes) : Except InstrError TxState :=
  if sc.txIdx < ts.accts.length then
    match canDataBeResized ts sc d.length with
    | .error e => .error e
    | .ok () => .ok { ts.setAcct sc.txIdx { ts.acct sc.txIdx with data := d } with
        resizeDelta := ts.resizeDelta + ((d.length : Int) - (ts.acct sc.txIdx).data.length) }
  else .error .MissingAccount

/-- `set_data_length`. -/
def setDataLength (ts : TxState) (sc : SetterCtx) (n : Nat) : Except InstrError TxState :=
  if sc.txIdx < ts.accts.length then
    match canDataBeResized ts sc n with
    | .error e => .error e
    | .ok () =>
      if (ts.acct sc.txIdx).data.length = n then .ok ts
      else .ok { ts.setAcct sc.txIdx { ts.acct sc.txIdx with
          data := resizeZero (ts.acct sc.txIdx).data n } with
        resizeDelta := ts.resizeDelta + ((n : Int) - (ts.acct sc.txIdx).data.length) }
  else .error .MissingAccount

/-- `set_owner`. -/
def setOwner (ts : TxState) (sc : SetterCtx) (o : Pubkey) : Except InstrError TxState :=
  if sc.txIdx < ts.accts.length then
    if sc.owned ts = false then .error .ModifiedProgramId
    else if sc.writable = false then .error .ModifiedProgramId
    else if isZeroed (ts.acct sc.txIdx).data = false then .error .ModifiedProgramId
    else if (ts.acct sc.txIdx).owner = o then .ok ts
    else .ok (ts.setAcct sc.txIdx { ts.acct sc.txIdx with owner := o })
  else .error .MissingAccount

/-- `set_executable`. -/
def setExecutable (ts : TxState) (r : RentParams) (sc : SetterCtx) (b : Bool) :
    Except InstrError TxState :=
  if sc.txIdx < ts.accts.length then
    if r.isExempt (ts.acct sc.txIdx).lamports (ts.acct sc.txIdx).data.length = false then
      .error .ExecutableAccountNotRentExempt
    else if sc.owned ts = false then .error .ExecutableModified
    else if sc.writable = false then .error .ExecutableModified
    else if (ts.acct sc.txIdx).executable = b then .ok ts
    else .ok (ts.setAcct sc.txIdx { ts.acct sc.txIdx with executable := b })
  else .error .MissingAccount

/-! ## What a successful setter changes -/

theorem sum_map_set {α : Type} (f : α → Nat) (l : List α) (i : Nat) (a : α) (h : i < l.length) :
    ((l.set i a).map f).sum + f l[i] = (l.map f).sum + f a := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp; omega
    | succ i =>
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      have := ih i (by simp at h; omega)
      omega

theorem lamportSum_setAcct (ts : TxState) (i : Nat) (a : Account) (h : i < ts.accts.length) :
    ((ts.setAcct i a).lamportSum : Int) = ts.lamportSum - (ts.acct i).lamports + a.lamports := by
  have hs := sum_map_set Account.lamports ts.accts i a h
  have he : ts.acct i = ts.accts[i] := by
    simp [TxState.acct, List.getD_eq_getElem?_getD, h]
  simp only [TxState.lamportSum, TxState.setAcct] at hs ⊢
  rw [he]
  omega

/-- The effect of a successful setter call: only the account `sc.txIdx` changes, the
call required the writable flag, and the balance invariant holds. -/
structure SetterStep (ts ts' : TxState) (sc : SetterCtx) : Prop where
  writable : sc.writable = true
  keys : ts'.keys = ts.keys
  stack : ts'.stack = ts.stack
  trace : ts'.trace = ts.trace
  returnData : ts'.returnData = ts.returnData
  topIndex : ts'.topIndex = ts.topIndex
  length : ts'.accts.length = ts.accts.length
  other : ∀ j, j ≠ sc.txIdx → ts'.acct j = ts.acct j
  balance : (ts'.lamportSum : Int) - ts'.lamportsDelta = ts.lamportSum - ts.lamportsDelta
  touches : TouchChanges ts ts'

theorem SetterStep.refl {ts : TxState} {sc : SetterCtx} (h : sc.writable = true) :
    SetterStep ts ts sc :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, TouchChanges.refl ts⟩

theorem SetterStep.trans {ts ts' ts'' : TxState} {sc : SetterCtx}
    (h1 : SetterStep ts ts' sc) (h2 : SetterStep ts' ts'' sc) : SetterStep ts ts'' sc :=
  ⟨h1.writable, h2.keys.trans h1.keys, h2.stack.trans h1.stack, h2.trace.trans h1.trace,
    h2.returnData.trans h1.returnData, h2.topIndex.trans h1.topIndex,
    h2.length.trans h1.length, fun j hj => (h2.other j hj).trans (h1.other j hj),
    h2.balance.trans h1.balance, h1.touches.trans h2.touches⟩

/-- A replacement of account `sc.txIdx` that changes the balance by `d` and the
counter `lamportsDelta` by the same amount. -/
theorem SetterStep.of_update {ts ts' : TxState} {sc : SetterCtx} {a : Account} {d : Int}
    (hw : sc.writable = true) (hi : sc.txIdx < ts.accts.length)
    (hk : ts'.keys = ts.keys) (ha : ts'.accts = ts.accts.set sc.txIdx a)
    (hd : ts'.lamportsDelta = ts.lamportsDelta + d) (hs : ts'.stack = ts.stack)
    (htr : ts'.trace = ts.trace) (hr : ts'.returnData = ts.returnData)
    (ht : ts'.topIndex = ts.topIndex)
    (hl : (a.lamports : Int) = (ts.acct sc.txIdx).lamports + d)
    (touches : ts'.touched = (ts.setAcct sc.txIdx a).touched) : SetterStep ts ts' sc := by
  refine ⟨hw, hk, hs, htr, hr, ht, by simp [ha], fun j hj => ?_, ?_,
    TouchChanges.of_update hk ha touches⟩
  · have := TxState.acct_setAcct_ne ts _ j a (Ne.symm hj)
    simp only [TxState.acct, TxState.setAcct] at this ⊢
    rw [ha]; exact this
  · have := lamportSum_setAcct ts sc.txIdx a hi
    simp only [TxState.setAcct, TxState.lamportSum] at this ⊢
    rw [ha, hd]
    omega

theorem canDataBeChanged_writable {ts : TxState} {sc : SetterCtx}
    (h : canDataBeChanged ts sc = .ok ()) : sc.writable = true := by
  unfold canDataBeChanged at h
  split at h
  · cases h
  · rename_i hw; simpa using hw

theorem canDataBeChanged_owned {ts : TxState} {sc : SetterCtx}
    (h : canDataBeChanged ts sc = .ok ()) : sc.owned ts = true := by
  unfold canDataBeChanged at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i ho; simpa using ho

theorem canDataBeResized_changed {ts : TxState} {sc : SetterCtx} {n : Nat}
    (h : canDataBeResized ts sc n = .ok ()) : canDataBeChanged ts sc = .ok () := by
  unfold canDataBeResized at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact h

theorem canDataBeResized_tx {ts : TxState} {sc : SetterCtx} {n : Nat}
    (h : canDataBeResized ts sc n = .ok ()) :
    txCanDataBeResized ts (ts.acct sc.txIdx).data.length n = .ok () := by
  unfold canDataBeResized at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hr; exact hr

theorem canDataBeResized_writable {ts : TxState} {sc : SetterCtx} {n : Nat}
    (h : canDataBeResized ts sc n = .ok ()) : sc.writable = true :=
  canDataBeChanged_writable (canDataBeResized_changed h)

theorem SetterStep.of_setLamports {ts ts' : TxState} {sc : SetterCtx} {v : Nat}
    (h : setLamports ts sc v = .ok ts') : SetterStep ts ts' sc := by
  unfold setLamports at h
  split at h
  · rename_i hi
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hw
        have hw : sc.writable = true := by simpa using hw
        split at h
        · cases h; exact SetterStep.refl hw
        · cases h
          exact SetterStep.of_update (a := { ts.acct sc.txIdx with lamports := v })
            (d := (v : Int) - (ts.acct sc.txIdx).lamports) hw hi rfl rfl rfl rfl rfl rfl rfl
            (by simp only; omega) rfl
  · cases h

theorem SetterStep.of_setDataFromSlice {ts ts' : TxState} {sc : SetterCtx} {d : Bytes}
    (h : setDataFromSlice ts sc d = .ok ts') : SetterStep ts ts' sc := by
  unfold setDataFromSlice at h
  split at h
  · rename_i hi
    split at h
    · cases h
    · rename_i hr
      cases h
      have hw := canDataBeResized_writable hr
      exact SetterStep.of_update (a := { ts.acct sc.txIdx with data := d }) (d := 0) hw hi
        rfl rfl (by simp [TxState.setAcct]) rfl rfl rfl rfl (by simp) rfl
  · cases h

theorem SetterStep.of_setDataLength {ts ts' : TxState} {sc : SetterCtx} {n : Nat}
    (h : setDataLength ts sc n = .ok ts') : SetterStep ts ts' sc := by
  unfold setDataLength at h
  split at h
  · rename_i hi
    split at h
    · cases h
    · rename_i hr
      have hw := canDataBeResized_writable hr
      split at h
      · cases h; exact SetterStep.refl hw
      · cases h
        exact SetterStep.of_update
          (a := { ts.acct sc.txIdx with data := resizeZero (ts.acct sc.txIdx).data n }) (d := 0)
          hw hi rfl rfl (by simp [TxState.setAcct]) rfl rfl rfl rfl (by simp) rfl
  · cases h

theorem SetterStep.of_setOwner {ts ts' : TxState} {sc : SetterCtx} {o : Pubkey}
    (h : setOwner ts sc o = .ok ts') : SetterStep ts ts' sc := by
  unfold setOwner at h
  split at h
  · rename_i hi
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hw
        have hw : sc.writable = true := by simpa using hw
        split at h
        · cases h
        · split at h
          · cases h; exact SetterStep.refl hw
          · cases h
            exact SetterStep.of_update (a := { ts.acct sc.txIdx with owner := o }) (d := 0)
              hw hi rfl rfl (by simp [TxState.setAcct]) rfl rfl rfl rfl (by simp) rfl
  · cases h

theorem SetterStep.of_setExecutable {ts ts' : TxState} {r : RentParams} {sc : SetterCtx}
    {b : Bool} (h : setExecutable ts r sc b = .ok ts') : SetterStep ts ts' sc := by
  unfold setExecutable at h
  split at h
  · rename_i hi
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hw
          have hw : sc.writable = true := by simpa using hw
          split at h
          · cases h; exact SetterStep.refl hw
          · cases h
            exact SetterStep.of_update (a := { ts.acct sc.txIdx with executable := b }) (d := 0)
                hw hi rfl rfl (by simp [TxState.setAcct]) rfl rfl rfl rfl (by simp) rfl
  · cases h

theorem SetterStep.of_checkedAddLamports {ts ts' : TxState} {sc : SetterCtx} {n : Nat}
    (h : checkedAddLamports ts sc n = .ok ts') : SetterStep ts ts' sc := by
  unfold checkedAddLamports at h
  split at h
  · cases h
  · exact SetterStep.of_setLamports h

theorem SetterStep.of_checkedSubLamports {ts ts' : TxState} {sc : SetterCtx} {n : Nat}
    (h : checkedSubLamports ts sc n = .ok ts') : SetterStep ts ts' sc := by
  unfold checkedSubLamports at h
  split at h
  · cases h
  · exact SetterStep.of_setLamports h

end Solanalib.Runtime
