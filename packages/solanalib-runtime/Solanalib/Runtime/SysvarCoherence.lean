/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Frame

@[expose] public section

namespace Solanalib.Runtime

/-- The administrative index update already agrees with the current account data. -/
def IndexCoherent (state : TxState) : Prop := writeIxSysvarIndex state = .ok state

theorem list_set_getD_self {α : Type} (items : List α) (index : Nat) (fallback : α) :
    items.set index (items.getD index fallback) = items := by
  induction items generalizing index with
  | nil => rfl
  | cons item rest ih =>
    cases index with
    | zero => rfl
    | succ index =>
      simpa [List.getD_eq_getElem?_getD] using congrArg (List.cons item) (ih index)

/-- Coherence depends on the current index and the selected sysvar account,
not on unrelated account values or execution metadata. -/
theorem IndexCoherent.preserve {before after : TxState}
    (coherent : IndexCoherent before)
    (keys : after.keys = before.keys)
    (index : after.topIndex = before.topIndex)
    (sysvar : ∀ position, before.ixSysvarIdx = some position → after.acct position = before.acct
      position) :
    IndexCoherent after := by
  have selectedAfter : after.ixSysvarIdx = before.ixSysvarIdx := by
    simp only [TxState.ixSysvarIdx, keys]
  cases selected : before.ixSysvarIdx with
  | none => simp only [IndexCoherent, writeIxSysvarIndex, selectedAfter, selected]
  | some position =>
    have same := sysvar position selected
    unfold IndexCoherent writeIxSysvarIndex at coherent
    rw [selected] at coherent
    dsimp only at coherent
    by_cases owner : (before.acct position).owner = Ids.sysvarOwner
    · by_cases enough : 2 ≤ (before.acct position).data.length
      · have present : position < before.accts.length := by
          by_cases bound : position < before.accts.length
          · exact bound
          · have missing : before.acct position = default := by
              simp [TxState.acct, List.getD_eq_getElem?_getD, bound]
            have wrong : (default : Account).owner ≠ Ids.sysvarOwner := by decide
            exact False.elim (wrong (missing ▸ owner))
        let updated := { before.acct position with
          data := writeAt (before.acct position).data ((before.acct position).data.length - 2)
            (u16le before.topIndex) }
        have stateSame : { before with accts := before.accts.set position updated } = before := by
          have normalized := coherent
          rw [ite_eq_right (fun different => different owner), ite_eq_right (Nat.not_lt.mpr
            enough)] at normalized
          exact Except.ok.inj normalized
        have accountSame : updated = before.acct position := by
          have observed : ((before.setAcct position updated).acct position) = before.acct position
            :=
            congrArg (fun state => state.acct position) stateSame
          rwa [TxState.acct_setAcct_self before position updated present] at observed
        have afterOwner : (after.acct position).owner = Ids.sysvarOwner := by
          rw [same, owner]
        have afterEnough : 2 ≤ (after.acct position).data.length := by
          rwa [same]
        have afterUpdated : { after.acct position with
            data := writeAt (after.acct position).data ((after.acct position).data.length - 2)
              (u16le after.topIndex) } = after.acct position := by
          simpa only [same, index, updated] using accountSame
        unfold IndexCoherent writeIxSysvarIndex
        rw [selectedAfter, selected]
        dsimp only
        rw [ite_eq_right (fun different => different afterOwner), ite_eq_right (Nat.not_lt.mpr
          afterEnough)]
        rw [afterUpdated]
        simp only [TxState.acct, list_set_getD_self]
      · simp [owner, Nat.lt_of_not_ge enough] at coherent
    · simp [owner] at coherent

theorem IndexCoherent.preserve_at {before after : TxState} {position : Nat}
    (coherent : IndexCoherent before) (selected : before.ixSysvarIdx = some position)
    (keys : after.keys = before.keys)
    (index : after.topIndex = before.topIndex) (account : after.acct position = before.acct
      position) :
    IndexCoherent after := by
  apply coherent.preserve keys index
  intro other chosen
  have same : other = position := Option.some.inj (chosen.symm.trans selected)
  simpa [same] using account

/-- A bounded overwrite is idempotent when repeated with the same bytes. -/
theorem writeAt_idempotent_of_le {bytes source : Bytes} {offset : Nat}
    (bounded : offset + source.length ≤ bytes.length) :
    writeAt (writeAt bytes offset source) offset source = writeAt bytes offset source := by
  have frontLength : (bytes.take offset).length = offset := by
    simp only [List.length_take]
    omega
  have writtenLength : (bytes.take offset ++ source).length = offset + source.length := by
    simp only [List.length_append, frontLength]
  have front : (bytes.take offset ++ source ++ bytes.drop (offset + source.length)).take offset =
      bytes.take offset := by
    rw [List.append_assoc, List.take_left' frontLength]
  have back : (bytes.take offset ++ source ++ bytes.drop (offset + source.length)).drop
      (offset + source.length) = bytes.drop (offset + source.length) :=
    List.drop_left' writtenLength
  simp only [writeAt, front, back]

/-- A correctly encoded selected sysvar makes the administrative write a no-op. -/
theorem IndexCoherent.of_bytes {state : TxState} {position : Nat}
    (selected : state.ixSysvarIdx = some position)
    (owner : (state.acct position).owner = Ids.sysvarOwner)
    (enough : 2 ≤ (state.acct position).data.length)
    (encoded : writeAt (state.acct position).data ((state.acct position).data.length - 2)
      (u16le state.topIndex) = (state.acct position).data) : IndexCoherent state := by
  have accountSame : { state.acct position with
      data := writeAt (state.acct position).data ((state.acct position).data.length - 2)
        (u16le state.topIndex) } = state.acct position := by rw [encoded]
  unfold IndexCoherent writeIxSysvarIndex
  rw [selected]
  dsimp only
  rw [ite_eq_right (fun different => different owner), ite_eq_right (Nat.not_lt.mpr enough),
    accountSame]
  simp only [TxState.acct, list_set_getD_self]

/-- The actual successful index write establishes the current-index invariant. -/
theorem writeIxSysvarIndex_coherent {before after : TxState}
    (written : writeIxSysvarIndex before = .ok after) : IndexCoherent after := by
  cases selected : before.ixSysvarIdx with
  | none =>
    have same : before = after := by
      simpa only [writeIxSysvarIndex, selected, Except.ok.injEq] using written
    subst after
    exact written
  | some position =>
    have input := written
    unfold writeIxSysvarIndex at input
    rw [selected] at input
    dsimp only at input
    by_cases owner : (before.acct position).owner = Ids.sysvarOwner
    · by_cases enough : 2 ≤ (before.acct position).data.length
      · have present : position < before.accts.length := by
          by_cases bound : position < before.accts.length
          · exact bound
          · have missing : before.acct position = default := by
              simp [TxState.acct, List.getD_eq_getElem?_getD, bound]
            have wrong : (default : Account).owner ≠ Ids.sysvarOwner := by decide
            exact False.elim (wrong (missing ▸ owner))
        rw [ite_eq_right (fun different => different owner), ite_eq_right (Nat.not_lt.mpr enough)]
          at input
        let updated : Account := { before.acct position with
          data := writeAt (before.acct position).data ((before.acct position).data.length - 2)
            (u16le before.topIndex) }
        have afterEq : after = { before with accts := before.accts.set position updated } :=
          (Except.ok.inj input).symm
        have afterAccount : after.acct position = updated := by
          rw [afterEq]
          exact TxState.acct_setAcct_self before position updated present
        have afterSelected : after.ixSysvarIdx = some position := by
          simpa only [afterEq, TxState.ixSysvarIdx] using selected
        have afterIndex : after.topIndex = before.topIndex := by rw [afterEq]
        have room : (before.acct position).data.length - 2 + (u16le before.topIndex).length ≤
            (before.acct position).data.length := by
          simp only [u16le, length_leBytes]
          omega
        apply IndexCoherent.of_bytes afterSelected
        · simpa only [afterAccount, updated] using owner
        · rw [afterAccount]
          dsimp only [updated]
          rw [length_writeAt room]
          exact enough
        · rw [afterAccount, afterIndex]
          dsimp only [updated]
          rw [length_writeAt room]
          exact writeAt_idempotent_of_le room
      · simp [owner, Nat.lt_of_not_ge enough] at input
    · simp [owner] at input

/-- Push establishes index coherence by performing the administrative write.
The subsequent stack and trace updates do not change that invariant. -/
theorem IndexCoherent.of_push {profile : Profile} {before after : TxState} {frame : Frame}
    (pushed : push profile before frame = .ok after) : IndexCoherent after := by
  unfold push at pushed
  split at pushed
  · cases pushed
  · split at pushed
    · cases pushed
    · split at pushed
      · cases pushed
      · split at pushed
        · cases pushed
        · split at pushed
          · cases pushed
          · rename_i written writtenEq
            cases pushed
            exact (writeIxSysvarIndex_coherent writtenEq).preserve rfl rfl (fun _ _ => rfl)

end Solanalib.Runtime
