/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Frame

@[expose] public section

namespace Solanalib.Runtime

/-- Program execution preserves the invocation stack. While an invocation is
active it also preserves the index of the top-level instruction. -/
structure StackPreserved (before after : TxState) : Prop where
  stack : after.stack = before.stack
  topIndex : before.stack ≠ [] → after.topIndex = before.topIndex

namespace StackPreserved

theorem refl (state : TxState) : StackPreserved state state := ⟨rfl, fun _ => rfl⟩

theorem trans {first middle last : TxState} (left : StackPreserved first middle)
    (right : StackPreserved middle last) : StackPreserved first last := by
  refine ⟨right.stack.trans left.stack, ?_⟩
  intro active
  have middleActive : middle.stack ≠ [] := by rw [left.stack]; exact active
  exact (right.topIndex middleActive).trans (left.topIndex active)

theorem of_eq {before after : TxState} (stack : after.stack = before.stack)
    (topIndex : after.topIndex = before.topIndex) : StackPreserved before after :=
  ⟨stack, fun _ => topIndex⟩

theorem of_changes {before after : TxState} {writable : Nat → Prop}
    (changes : Changes before after writable) : StackPreserved before after :=
  of_eq changes.stack changes.topIndex

end StackPreserved

/-- Completing a top-level instruction advances the index once. Completing a
nested instruction restores the caller stack and retains the current index. -/
structure InstructionStack (before after : TxState) : Prop where
  stack : after.stack = before.stack
  topIndex : after.topIndex =
    if before.stack = [] then before.topIndex + 1 else before.topIndex

theorem InstructionStack.preserved {before after : TxState}
    (shape : InstructionStack before after) : StackPreserved before after := by
  refine ⟨shape.stack, ?_⟩
  intro active
  simpa only [active, ite_false] using shape.topIndex

theorem writeIxSysvarIndex_stack {before after : TxState}
    (written : writeIxSysvarIndex before = .ok after) :
    after.stack = before.stack ∧ after.topIndex = before.topIndex := by
  unfold writeIxSysvarIndex at written
  dsimp only at written
  split at written
  · cases written; exact ⟨rfl, rfl⟩
  · split at written
    · cases written
    · split at written
      · cases written
      · cases written; exact ⟨rfl, rfl⟩

theorem push_stack {profile : Profile} {before after : TxState} {frame : Frame}
    (pushed : push profile before frame = .ok after) :
    after.stack = frame :: before.stack ∧ after.topIndex = before.topIndex := by
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
            obtain ⟨stack, topIndex⟩ := writeIxSysvarIndex_stack writtenEq
            exact ⟨congrArg (List.cons frame) stack, topIndex⟩

theorem pop_stack {before after : TxState} (popped : pop before = .ok after) :
    after.stack = before.stack.tail ∧ after.topIndex =
      if before.stack.length = 1 then before.topIndex + 1 else before.topIndex := by
  unfold pop at popped
  dsimp only at popped
  by_cases balanced : before.lamportsDelta = 0
  · simp only [balanced, ne_eq, not_true_eq_false, ite_false, Except.ok.injEq] at popped
    subst popped
    exact ⟨rfl, rfl⟩
  · simp [balanced] at popped

/-- Metadata effects for each judgment of the runtime execution relation. -/
def StackShapeProp : Judgment → Prop
  | .procInstr before _ result => ∀ after, result = .ok after → InstructionStack before after
  | .runProgram before _ result | .havoc before _ result =>
    ∀ after, result = .ok after → StackPreserved before after
  | .invoke _ before _ _ result =>
    ∀ after, result = .ok after → StackPreserved before.ts after

theorem Exec.stackShape {world : World} {judgment : Judgment} (execution : Exec world judgment) :
    StackShapeProp judgment := by
  induction execution with
  | pushFail _ => intro after returned; cases returned
  | @run before pushed frame result entered _ ih =>
    intro after returned
    obtain ⟨finished, programResult, popped⟩ := afterProgram_ok returned
    obtain ⟨enteredStack, enteredIndex⟩ := push_stack entered
    have body := ih finished programResult
    have active : (resetReturnData pushed).stack ≠ [] := by
      intro empty
      have impossible : frame :: before.stack = [] := enteredStack.symm.trans empty
      cases impossible
    have finishedStack : finished.stack = frame :: before.stack := body.stack.trans enteredStack
    have finishedIndex : finished.topIndex = before.topIndex := (body.topIndex active).trans
      enteredIndex
    obtain ⟨returnedStack, returnedIndex⟩ := pop_stack popped
    refine ⟨?_, ?_⟩
    · rw [returnedStack, finishedStack]
      rfl
    · rw [returnedIndex, finishedStack, finishedIndex]
      by_cases empty : before.stack = [] <;> simp [empty]
  | compute _ => intro after returned; cases returned
  | unsupported _ => intro after returned; cases returned
  | serializationFailed _ _ => intro after returned; cases returned
  | system _ stepped =>
    intro after returned
    subst returned
    exact StackPreserved.of_changes (systemProcess_changes stepped)
  | systemNonce _ _ _ ih => exact ih
  | computeBudget _ => intro after returned; cases returned; exact StackPreserved.refl _
  | unmodelled _ _ _ ih => exact ih
  | loaderV3 _ _ completed _ ih =>
    intro after returned
    obtain ⟨finished, finishedResult, rfl⟩ := finishLoaderV3_ok (completed.trans returned)
    have preserved := ih finished finishedResult
    refine ⟨(applyLoaderV3Effect_stack _ _ _ _).trans preserved.stack, ?_⟩
    intro active
    exact (applyLoaderV3Effect_topIndex _ _ _ _).trans (preserved.topIndex active)
  | sbf _ _ _ _ ih =>
    intro after returned
    exact ih after returned
  | havocDone => intro after returned; cases returned; exact StackPreserved.refl _
  | havocFail => intro after returned; cases returned
  | havocReturnData _ _ _ ih =>
    intro after returned
    have preserved := ih after returned
    exact ⟨preserved.stack, preserved.topIndex⟩
  | @havocSetter before middle frame result operation account member stepped _ ih =>
    intro after returned
    have first := StackPreserved.of_changes (Changes.of_setterStep (applySetter_step stepped))
    exact first.trans (ih after returned)
  | @havocInvoke before middle frame callee result instruction seeds signers _ prepared _ _ ihp ihr
    =>
    intro after returned
    exact (ihp middle rfl).preserved.trans (ihr after returned)
  | @exit0 context before result readback =>
    intro after returned
    subst returned
    exact StackPreserved.of_changes (Changes.of_readBack readback)
  | exitErr _ => intro after returned; cases returned
  | fault => intro after returned; cases returned
  | invCompute _ => intro after returned; cases returned
  | load _ _ ih => exact ih
  | loadFail _ => intro after returned; cases returned
  | @store context before middle address bytes rest final result stored _ ih =>
    intro after returned
    exact (StackPreserved.of_changes (Changes.of_storeRegion stored)).trans (ih after returned)
  | storeFail _ => intro after returned; cases returned
  | unregistered _ => intro after returned; cases returned
  | @sys context before middle request answer rest final result _ step _ ih =>
    intro after returned
    obtain ⟨_, _, _, _, stack, _, topIndex, _⟩ := sysStep_accts step
    exact (StackPreserved.of_eq stack topIndex).trans (ih after returned)
  | sysFail _ _ _ _ => intro after returned; cases returned
  | remainingComputeUnits _ _ ih => exact ih
  | @cpi context before synced copied request prepared calleeFinal lengths rest final result
      preparedEq syncedEq _ copiedEq _ ihp ihr =>
    intro after returned
    have first := StackPreserved.of_changes (Changes.of_updateCallee syncedEq)
    have second := (ihp calleeFinal rfl).preserved
    have last := ihr after returned
    rw [updateCaller_ts copiedEq] at last
    exact first.trans (second.trans last)
  | cpiPrepareFail _ => intro after returned; cases returned
  | cpiCalleeSyncFail _ _ => intro after returned; cases returned
  | cpiCalleeFail _ _ _ _ => intro after returned; cases returned
  | cpiCallerSyncFail _ _ _ _ _ => intro after returned; cases returned

theorem ProcInstr.stack {world : World} {before after : TxState} {frame : Frame}
    (execution : ProcInstr world before frame (.ok after)) : after.stack = before.stack :=
  (Exec.stackShape execution after rfl).stack

theorem ProcInstr.topIndex {world : World} {before after : TxState} {frame : Frame}
    (execution : ProcInstr world before frame (.ok after)) :
    after.topIndex = if before.stack = [] then before.topIndex + 1 else before.topIndex :=
  (Exec.stackShape execution after rfl).topIndex

theorem ProcInstr.topIndex_of_active {world : World} {before after : TxState} {frame : Frame}
    (execution : ProcInstr world before frame (.ok after)) (active : before.stack ≠ []) :
    after.topIndex = before.topIndex :=
  (Exec.stackShape execution after rfl).preserved.topIndex active

theorem RunProgram.stack {world : World} {before after : TxState} {frame : Frame}
    (execution : RunProgram world before frame (.ok after)) : after.stack = before.stack :=
  (Exec.stackShape execution after rfl).stack

theorem RunProgram.topIndex_of_active {world : World} {before after : TxState} {frame : Frame}
    (execution : RunProgram world before frame (.ok after)) (active : before.stack ≠ []) :
    after.topIndex = before.topIndex :=
  (Exec.stackShape execution after rfl).topIndex active

theorem Havoc.stack {world : World} {before after : TxState} {frame : Frame}
    (execution : Havoc world before frame (.ok after)) : after.stack = before.stack :=
  (Exec.stackShape execution after rfl).stack

theorem Havoc.topIndex_of_active {world : World} {before after : TxState} {frame : Frame}
    (execution : Havoc world before frame (.ok after)) (active : before.stack ≠ []) :
    after.topIndex = before.topIndex :=
  (Exec.stackShape execution after rfl).topIndex active

theorem Invoke.stack {world : World} {context : InvCtx} {before : InvState} {after : TxState}
    {events : List (Event × Reply)} {final : Final}
    (execution : Invoke world context before events final (.ok after)) : after.stack =
      before.ts.stack :=
  (Exec.stackShape execution after rfl).stack

theorem Invoke.topIndex_of_active {world : World} {context : InvCtx} {before : InvState} {after :
  TxState}
    {events : List (Event × Reply)} {final : Final}
    (execution : Invoke world context before events final (.ok after)) (active : before.ts.stack ≠
      []) :
    after.topIndex = before.ts.topIndex :=
  (Exec.stackShape execution after rfl).topIndex active

end Solanalib.Runtime
