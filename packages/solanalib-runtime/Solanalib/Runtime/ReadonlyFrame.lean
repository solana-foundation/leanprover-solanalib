/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.StackFrame
public import Solanalib.Runtime.SysvarCoherence

@[expose] public section

namespace Solanalib.Runtime

/-- An active invocation with its actual Instructions-sysvar index already installed. -/
structure ActiveIndex (state : TxState) (position : Nat) : Prop where
  active : state.stack ≠ []
  selected : state.ixSysvarIdx = some position
  coherent : IndexCoherent state

namespace ActiveIndex

theorem preserve {before after : TxState} {position : Nat} (initial : ActiveIndex before position)
    (keys : after.keys = before.keys) (stack : after.stack = before.stack)
    (index : after.topIndex = before.topIndex) (account : after.acct position = before.acct
      position) :
    ActiveIndex after position := by
  refine ⟨?_, ?_, initial.coherent.preserve_at initial.selected keys index account⟩
  · rw [stack]; exact initial.active
  · simpa only [TxState.ixSysvarIdx, keys] using initial.selected

theorem of_changes {before after : TxState} {position : Nat} {writable : Nat → Prop}
    (initial : ActiveIndex before position) (changes : Changes before after writable)
    (readonly : ¬ writable position) : ActiveIndex after position :=
  initial.preserve changes.keys changes.stack changes.topIndex (changes.other position readonly)

end ActiveIndex

theorem push_accounts_of_coherent {profile : Profile} {before after : TxState} {frame : Frame}
    (pushed : push profile before frame = .ok after) (coherent : IndexCoherent before) :
    after.accts = before.accts := by
  unfold push at pushed
  rw [coherent] at pushed
  dsimp only at pushed
  (repeat' split at pushed) <;> cases pushed <;> rfl

/-- Readonly framing of the administrative sysvar. Coherence is an input condition
and is transported through the actual execution, rather than assumed of its result. -/
def IndexFrameProp : Judgment → Prop
  | .procInstr before frame result =>
    ∀ after, result = .ok after → ∀ position,
      before.ixSysvarIdx = some position → IndexCoherent before →
      ¬ WritableTx frame position → after.acct position = before.acct position
  | .runProgram before frame result | .havoc before frame result =>
    ∀ after, result = .ok after → ∀ position, ActiveIndex before position →
      ¬ WritableTx frame position → after.acct position = before.acct position
  | .invoke context before _ _ result =>
    LayoutIn context → ∀ after, result = .ok after → ∀ position, ActiveIndex before.ts position →
      ¬ WritableTx context.frame position → after.acct position = before.ts.acct position

theorem Exec.indexFrame {world : World} {judgment : Judgment} (execution : Exec world judgment) :
    IndexFrameProp judgment := by
  induction execution with
  | pushFail _ => intro after result; cases result
  | @run before pushed frame result entered body ih =>
    intro after returned position selected coherent readonly
    obtain ⟨finished, bodyResult, popped⟩ := afterProgram_ok returned
    have accountEq := push_accounts_of_coherent entered coherent
    have keys := (push_spec entered).1.keys
    obtain ⟨stack, index⟩ := push_stack entered
    have initial : ActiveIndex (resetReturnData pushed) position := by
      refine ⟨?_, ?_, ?_⟩
      · change pushed.stack ≠ []
        rw [stack]
        simp
      · simpa only [TxState.ixSysvarIdx, resetReturnData, keys] using selected
      · apply coherent.preserve (after := resetReturnData pushed) keys index
        intro other chosen
        exact congrArg (fun accounts => accounts.getD other default) accountEq
    have value := ih finished bodyResult position initial readonly
    have finalEq := congrArg (fun accounts => accounts.getD position default) (pop_spec popped).2.1
    exact finalEq.trans (value.trans (congrArg (fun accounts => accounts.getD position default)
      accountEq))
  | compute _ => intro after result; cases result
  | unsupported _ => intro after result; cases result
  | serializationFailed _ _ => intro after result; cases result
  | system _ step =>
    intro after result position initial readonly
    subst result
    exact (systemProcess_changes step).other position readonly
  | systemNonce _ _ _ ih => exact ih
  | computeBudget _ => intro after result; cases result; intro _ _ _; rfl
  | unmodelled _ _ _ ih => exact ih
  | loaderV3 _ _ completed _ ih =>
    intro after returned position initial readonly
    obtain ⟨finished, finishedResult, rfl⟩ := finishLoaderV3_ok (completed.trans returned)
    have accountEq := ih finished finishedResult position initial readonly
    simpa only [TxState.acct, applyLoaderV3Effect_accts] using accountEq
  | sbf _ _ _ _ ih =>
    intro after result position initial readonly
    exact ih (layoutIn_invCtxOf _ _ _ _) after result position initial readonly
  | havocDone => intro after result; cases result; intro _ _ _; rfl
  | havocFail => intro after result; cases result
  | @havocReturnData before frame result programId data _ ih =>
    intro after returned position initial readonly
    have next : ActiveIndex (setNativeReturnData before programId data) position :=
      initial.preserve rfl rfl rfl rfl
    exact ih after returned position next readonly
  | @havocSetter before middle frame result operation account member step _ ih =>
    intro after returned position initial readonly
    have changed := Changes.of_setterStep (applySetter_step step)
    have forbidden : ¬ (position = account.txIdx ∧ account.writable = true) := by
      rintro ⟨same, writable⟩
      exact readonly ⟨account, member, same.symm, writable⟩
    have next := initial.of_changes changed forbidden
    exact (ih after returned position next readonly).trans (changed.other position forbidden)
  | @havocInvoke before middle frame callee result instruction seeds signers _ prepared called _
    ihp ihr =>
    intro after returned position initial readonly
    have calleeReadonly : ¬ WritableTx callee position := by
      rintro ⟨account, member, same, writable⟩
      exact readonly (same ▸ prepareCallee_writable prepared account member writable)
    have value := ihp middle rfl position initial.selected initial.coherent calleeReadonly
    have next := initial.preserve (ProcInstr.frame called middle rfl).keys
      (ProcInstr.stack called) (ProcInstr.topIndex_of_active called initial.active) value
    exact (ihr after returned position next readonly).trans value
  | @exit0 context before result readback =>
    intro layout after returned position initial readonly
    subst returned
    apply (Changes.of_readBack readback).other position
    exact fun writable => readonly (writableIn_of_layoutIn layout writable)
  | exitErr _ => intro _ after result; cases result
  | fault => intro _ after result; cases result
  | invCompute _ => intro _ after result; cases result
  | load _ _ ih => exact ih
  | loadFail _ => intro _ after result; cases result
  | @store context before middle address bytes rest final result stored _ ih =>
    intro layout after returned position initial readonly
    have changed := Changes.of_storeRegion stored
    have forbidden : ¬ WritableIn context.layout position :=
      fun writable => readonly (writableIn_of_layoutIn layout writable)
    have next := initial.of_changes changed forbidden
    exact (ih layout after returned position next readonly).trans (changed.other position forbidden)
  | storeFail _ => intro _ after result; cases result
  | unregistered _ => intro _ after result; cases result
  | @sys context before middle request answer rest final result _ step _ ih =>
    intro layout after returned position initial readonly
    obtain ⟨accounts, keys, _, _, stack, _, index, _⟩ := sysStep_accts step
    have value : middle.ts.acct position = before.ts.acct position :=
      congrArg (fun accounts => accounts.getD position default) accounts
    have next := initial.preserve keys stack index value
    exact (ih layout after returned position next readonly).trans value
  | sysFail _ _ _ _ => intro _ after result; cases result
  | remainingComputeUnits _ _ ih => exact ih
  | @cpi context before synced copied request prepared calleeFinal lengths rest final result
      preparedEq syncedEq called copiedEq _ ihp ihr =>
    intro layout after returned position initial readonly
    obtain ⟨calleeWritable, callerWritable⟩ := cpiPrepare_spec preparedEq
    have changed := Changes.of_updateCallee syncedEq
    have forbidden : ¬ CallerWritable prepared.translated position := by
      rintro ⟨entry, member, same, writable⟩
      exact readonly (same ▸ callerWritable entry member writable)
    have synchronized := initial.of_changes changed forbidden
    have calleeReadonly : ¬ WritableTx prepared.callee position := by
      rintro ⟨account, member, same, writable⟩
      exact readonly (same ▸ calleeWritable account member writable)
    have value := ihp calleeFinal rfl position synchronized.selected synchronized.coherent
      calleeReadonly
    have next := synchronized.preserve (ProcInstr.frame called calleeFinal rfl).keys
      (ProcInstr.stack called) (ProcInstr.topIndex_of_active called synchronized.active) value
    have current : ActiveIndex copied.ts position := by
      rw [updateCaller_ts copiedEq]
      exact next
    have finalValue := ihr layout after returned position current readonly
    rw [updateCaller_ts copiedEq] at finalValue
    exact finalValue.trans (value.trans (changed.other position forbidden))
  | cpiPrepareFail _ => intro _ after result; cases result
  | cpiCalleeSyncFail _ _ => intro _ after result; cases result
  | cpiCalleeFail _ _ _ _ => intro _ after result; cases result
  | cpiCallerSyncFail _ _ _ _ _ => intro _ after result; cases result

/-- With the actual input index installed, successful execution preserves every
readonly account in full, including the Instructions sysvar. The final top-level
index may advance after a top-level call, but that pop does not rewrite accounts. -/
theorem ProcInstr.readonly_account {world : World} {before after : TxState} {frame : Frame}
    (execution : ProcInstr world before frame (.ok after)) (coherent : IndexCoherent before)
    (position : Nat) (readonly : ¬ WritableTx frame position) :
    after.acct position = before.acct position := by
  by_cases selected : IsIxSysvar before.keys position
  · exact Exec.indexFrame execution after rfl position selected coherent readonly
  · apply (ProcInstr.frame execution after rfl).other position
    rintro (writable | sysvar)
    · exact readonly writable
    · exact selected sysvar

end Solanalib.Runtime
