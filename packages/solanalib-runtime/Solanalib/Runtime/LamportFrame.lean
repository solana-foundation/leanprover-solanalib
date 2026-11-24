/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Frame

@[expose] public section

namespace Solanalib.Runtime

/-- A balance observation is unchanged outside the specified writable indices. -/
def LamportFrame (before after : TxState) (writable : Nat → Prop) : Prop :=
  ∀ index, ¬ writable index → (after.acct index).lamports = (before.acct index).lamports

namespace LamportFrame

theorem refl (state : TxState) (writable : Nat → Prop) : LamportFrame state state writable :=
  fun _ _ => rfl

theorem trans {first middle last : TxState} {writable : Nat → Prop}
    (left : LamportFrame first middle writable) (right : LamportFrame middle last writable) :
    LamportFrame first last writable :=
  fun index readonly => (right index readonly).trans (left index readonly)

theorem mono {before after : TxState} {small large : Nat → Prop}
    (frame : LamportFrame before after small) (included : ∀ index, small index → large index) :
    LamportFrame before after large :=
  fun index readonly => frame index (fun member => readonly (included index member))

theorem of_changes {before after : TxState} {writable : Nat → Prop}
    (changes : Changes before after writable) : LamportFrame before after writable :=
  fun index readonly => congrArg Account.lamports (changes.other index readonly)

theorem of_accounts {before after : TxState} {writable : Nat → Prop}
    (accounts : after.accts = before.accts) : LamportFrame before after writable := by
  intro index _
  simp only [TxState.acct, accounts]

end LamportFrame

/-- Replacing the data of an account, including administrative sysvar data,
cannot change any balance. -/
theorem account_update_lamports (state : TxState) (changed index : Nat) (account : Account)
    (balance : account.lamports = (state.acct changed).lamports) :
    ((state.setAcct changed account).acct index).lamports = (state.acct index).lamports := by
  by_cases same : changed = index
  · subst index
    by_cases present : changed < state.accts.length
    · rw [TxState.acct_setAcct_self state changed account present]
      exact balance
    · simp only [TxState.setAcct, TxState.acct]
      rw [List.set_eq_of_length_le (by omega)]
  · rw [TxState.acct_setAcct_ne state changed index account same]

theorem writeIxSysvarIndex_lamports {before after : TxState}
    (written : writeIxSysvarIndex before = .ok after) (index : Nat) :
    (after.acct index).lamports = (before.acct index).lamports := by
  unfold writeIxSysvarIndex at written
  dsimp only at written
  split at written
  · cases written; rfl
  · rename_i changed selected
    split at written
    · cases written
    · split at written
      · cases written
      · cases written
        exact account_update_lamports before changed index _ rfl

theorem push_lamports {profile : Profile} {before after : TxState} {frame : Frame}
    (pushed : push profile before frame = .ok after) (index : Nat) :
    (after.acct index).lamports = (before.acct index).lamports := by
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
            exact writeIxSysvarIndex_lamports writtenEq index

/-- A nested push accepts only a balanced caller. -/
theorem push_entry_balanced {profile : Profile} {before after : TxState} {frame : Frame}
    (pushed : push profile before frame = .ok after) (active : before.stack ≠ []) :
    before.lamportsDelta = 0 := by
  have nonempty : before.stack.isEmpty = false := by
    cases selected : before.stack <;> simp_all
  by_cases balanced : before.lamportsDelta = 0
  · exact balanced
  · unfold push at pushed
    split at pushed
    · cases pushed
    · simp [nonempty, balanced] at pushed

/-- The balance frame has no administrative-sysvar exception. -/
def LamportFrameProp : Judgment → Prop
  | .procInstr before frame result | .runProgram before frame result | .havoc before frame result =>
    ∀ after, result = .ok after → LamportFrame before after (WritableTx frame)
  | .invoke context before _ _ result =>
    LayoutIn context → ∀ after, result = .ok after →
      LamportFrame before.ts after (WritableTx context.frame)

theorem Exec.lamportFrame {world : World} {judgment : Judgment} (execution : Exec world judgment) :
    LamportFrameProp judgment := by
  induction execution with
  | pushFail _ => intro after result; cases result
  | @run before pushed frame result entered _ ih =>
    intro after returned
    obtain ⟨finished, programResult, popped⟩ := afterProgram_ok returned
    have entryChange : LamportFrame before (resetReturnData pushed) (WritableTx frame) :=
      fun index _ => push_lamports entered index
    have returnChange : LamportFrame finished after (WritableTx frame) :=
      LamportFrame.of_accounts (pop_spec popped).2.1
    exact entryChange.trans ((ih finished programResult).trans returnChange)
  | compute _ => intro after result; cases result
  | unsupported _ => intro after result; cases result
  | serializationFailed _ _ => intro after result; cases result
  | system _ stepped =>
    intro after result
    subst result
    exact LamportFrame.of_changes (systemProcess_changes stepped)
  | systemNonce _ _ _ ih => exact ih
  | computeBudget _ => intro after result; cases result; exact LamportFrame.refl _ _
  | unmodelled _ _ _ ih => exact ih
  | loaderV3 _ _ completed _ ih =>
    intro after returned
    obtain ⟨finished, finishedResult, rfl⟩ := finishLoaderV3_ok (completed.trans returned)
    exact (ih finished finishedResult).trans
      (LamportFrame.of_accounts (applyLoaderV3Effect_accts _ _ _ _))
  | sbf _ _ _ _ ih =>
    intro after result
    exact ih (layoutIn_invCtxOf _ _ _ _) after result
  | havocDone => intro after result; cases result; exact LamportFrame.refl _ _
  | havocFail => intro after result; cases result
  | havocReturnData _ _ _ ih => exact ih
  | @havocSetter before middle frame result operation account member step _ ih =>
    intro after returned
    have changed := Changes.of_setterStep (applySetter_step step)
    have first := (LamportFrame.of_changes changed).mono (large := WritableTx frame)
      (fun index ⟨same, writable⟩ => ⟨account, member, same.symm, writable⟩)
    exact first.trans (ih after returned)
  | @havocInvoke before middle frame callee result instruction seeds signers _ prepared _ _ ihp ihr
    =>
    intro after returned
    have first := (ihp middle rfl).mono (large := WritableTx frame) (by
      rintro index ⟨account, member, same, writable⟩
      exact same ▸ prepareCallee_writable prepared account member writable)
    exact first.trans (ihr after returned)
  | @exit0 context before result readback =>
    intro layout after returned
    subst returned
    exact (LamportFrame.of_changes (Changes.of_readBack readback)).mono
      (fun index writable => writableIn_of_layoutIn layout writable)
  | exitErr _ => intro _ after result; cases result
  | fault => intro _ after result; cases result
  | invCompute _ => intro _ after result; cases result
  | load _ _ ih => exact ih
  | loadFail _ => intro _ after result; cases result
  | @store context before middle address bytes rest final result stored _ ih =>
    intro layout after returned
    have first := (LamportFrame.of_changes (Changes.of_storeRegion stored)).mono
      (large := WritableTx context.frame)
      (fun index writable => writableIn_of_layoutIn layout writable)
    exact first.trans (ih layout after returned)
  | storeFail _ => intro _ after result; cases result
  | unregistered _ => intro _ after result; cases result
  | @sys context before middle request answer rest final result _ step _ ih =>
    intro layout after returned
    have first : LamportFrame before.ts middle.ts (WritableTx context.frame) :=
      LamportFrame.of_accounts (sysStep_accts step).1
    exact first.trans (ih layout after returned)
  | sysFail _ _ _ _ => intro _ after result; cases result
  | remainingComputeUnits _ _ ih => exact ih
  | @cpi context before synced copied request prepared calleeFinal lengths rest final result
      preparedEq syncedEq _ copiedEq _ ihp ihr =>
    intro layout after returned
    obtain ⟨calleeWritable, callerWritable⟩ := cpiPrepare_spec preparedEq
    have first := (LamportFrame.of_changes (Changes.of_updateCallee syncedEq)).mono
      (large := WritableTx context.frame) (by
        rintro index ⟨entry, member, same, writable⟩
        exact same ▸ callerWritable entry member writable)
    have second := (ihp calleeFinal rfl).mono (large := WritableTx context.frame) (by
      rintro index ⟨account, member, same, writable⟩
      exact same ▸ calleeWritable account member writable)
    have last := ihr layout after returned
    rw [updateCaller_ts copiedEq] at last
    exact first.trans (second.trans last)
  | cpiPrepareFail _ => intro _ after result; cases result
  | cpiCalleeSyncFail _ _ => intro _ after result; cases result
  | cpiCalleeFail _ _ _ _ => intro _ after result; cases result
  | cpiCallerSyncFail _ _ _ _ _ => intro _ after result; cases result

theorem ProcInstr.readonly_lamports {world : World} {before after : TxState} {frame : Frame}
    (execution : ProcInstr world before frame (.ok after)) (index : Nat)
    (readonly : ¬ WritableTx frame index) :
    (after.acct index).lamports = (before.acct index).lamports :=
  Exec.lamportFrame execution after rfl index readonly

theorem ProcInstr.entry_balanced {world : World} {before after : TxState} {frame : Frame}
    (execution : ProcInstr world before frame (.ok after)) (active : before.stack ≠ []) :
    before.lamportsDelta = 0 := by
  change Exec world (.procInstr before frame (.ok after)) at execution
  generalize selected : Judgment.procInstr before frame (.ok after) = judgment at execution
  cases execution with
  | run pushed _ =>
    injection selected with stateEq _ _
    cases stateEq
    exact push_entry_balanced pushed active
  | _ => cases selected

end Solanalib.Runtime
