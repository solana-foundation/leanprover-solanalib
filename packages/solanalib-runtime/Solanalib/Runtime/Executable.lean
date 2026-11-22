/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Frame

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Runtime

/-- Equality of the actual executable flags in two transaction states.
This is a field observation of the ledger, independent of any caller view. -/
def ExecutableEq (before after : TxState) : Prop :=
  ∀ index, (after.acct index).executable = (before.acct index).executable

/-- Executable preservation restricted to the accounts of one invoked frame.
This can be required of a particular callee without restricting arbitrary programs. -/
def FrameExecutableEq (before : TxState) (frame : Frame) (after : TxState) : Prop :=
  ∀ account ∈ frame.accounts,
    (after.acct account.txIdx).executable = (before.acct account.txIdx).executable

namespace ExecutableEq

theorem refl (state : TxState) : ExecutableEq state state := fun _ => rfl

theorem trans {before middle after : TxState}
    (first : ExecutableEq before middle) (second : ExecutableEq middle after) :
    ExecutableEq before after := fun index => (second index).trans (first index)

theorem onFrame {before after : TxState} (same : ExecutableEq before after) (frame : Frame) :
    FrameExecutableEq before frame after := fun account _ => same account.txIdx

theorem of_accounts {before after : TxState} (same : after.accts = before.accts) :
    ExecutableEq before after := by
  intro index
  simp only [TxState.acct, same]

theorem setAcct (before : TxState) (index : Nat) (value : Account)
    (same : value.executable = (before.acct index).executable) :
    ExecutableEq before (before.setAcct index value) := by
  intro other
  by_cases equal : other = index
  · subst other
    by_cases bound : index < before.accts.length
    · rw [TxState.acct_setAcct_self _ _ _ bound]
      exact same
    · simp only [TxState.setAcct, List.set_eq_of_length_le (Nat.le_of_not_lt bound), TxState.acct]
  · rw [TxState.acct_setAcct_ne _ _ _ _ (Ne.symm equal)]

theorem of_setLamports {before after : TxState} {context : SetterCtx} {value : Nat}
    (step : setLamports before context value = .ok after) : ExecutableEq before after := by
  unfold setLamports at step
  (repeat' split at step) <;> cases step
  all_goals first | exact refl _ | exact setAcct _ _ _ rfl

theorem of_setOwner {before after : TxState} {context : SetterCtx} {owner : Pubkey}
    (step : setOwner before context owner = .ok after) : ExecutableEq before after := by
  unfold setOwner at step
  (repeat' split at step) <;> cases step
  all_goals first | exact refl _ | exact setAcct _ _ _ rfl

theorem of_setDataLength {before after : TxState} {context : SetterCtx} {length : Nat}
    (step : setDataLength before context length = .ok after) : ExecutableEq before after := by
  unfold setDataLength at step
  (repeat' split at step) <;> cases step
  all_goals first | exact refl _ | exact setAcct _ _ _ rfl

theorem of_setDataFromSlice {before after : TxState} {context : SetterCtx} {data : Bytes}
    (step : setDataFromSlice before context data = .ok after) : ExecutableEq before after := by
  unfold setDataFromSlice at step
  (repeat' split at step) <;> cases step
  all_goals exact setAcct _ _ _ rfl

theorem of_checkedAddLamports {before after : TxState} {context : SetterCtx} {value : Nat}
    (step : checkedAddLamports before context value = .ok after) : ExecutableEq before after := by
  unfold checkedAddLamports at step
  split at step
  · cases step
  · exact of_setLamports step

theorem of_checkedSubLamports {before after : TxState} {context : SetterCtx} {value : Nat}
    (step : checkedSubLamports before context value = .ok after) : ExecutableEq before after := by
  unfold checkedSubLamports at step
  split at step
  · cases step
  · exact of_setLamports step

theorem of_lamportStep {before after : TxState} {context : SetterCtx} {value : Nat}
    (step : lamportStep before context value = .ok after) : ExecutableEq before after := by
  unfold lamportStep at step
  split at step
  · cases step; exact refl _
  · exact of_setLamports step

theorem of_ownerStep {before after : TxState} {context : SetterCtx} {value : Pubkey}
    (step : ownerStep before context value = .ok after) : ExecutableEq before after := by
  unfold ownerStep at step
  split at step
  · cases step; exact refl _
  · exact of_setOwner step

theorem of_dataStep {configuration : MemConfig} {before after : TxState} {context : SetterCtx}
    {data : Bytes} {length : Nat}
    (step : dataStep configuration before context data length = .ok after) : ExecutableEq before
      after := by
  cases configuration with
  | L =>
    simp only [dataStep, dataStepL] at step
    cases resized : canDataBeResized before context length with
    | ok value =>
      simp only [resized] at step
      exact of_setDataFromSlice step
    | error error =>
      simp only [resized] at step
      split at step
      · cases step; exact refl _
      · cases step
  | S =>
    simp only [dataStep, dataStepS] at step
    cases changed : canDataBeChanged before context with
    | ok value =>
      simp only [changed] at step
      exact of_setDataFromSlice step
    | error error =>
      simp only [changed] at step
      split at step
      · cases step; exact refl _
      · exact of_setDataLength step
  | D =>
    simp only [dataStep, dataStepD] at step
    split at step
    · cases step; exact refl _
    · exact of_setDataLength step

theorem of_readBackAcct {abi : Abi} {configuration : MemConfig} {before after : TxState}
    {context : SetterCtx} {values : BufVals} {length : Nat}
    (step : readBackAcct abi configuration before context values length = .ok after) :
    ExecutableEq before after := by
  unfold readBackAcct at step
  split at step
  · cases step
  · rename_i balance balanceStep
    split at step
    · cases step
    · split at step
      · cases step
      · rename_i data dataStep
        have first := of_lamportStep balanceStep
        have second := of_dataStep dataStep
        cases abi with
        | v1 => exact first.trans (second.trans (of_ownerStep step))
        | v0 => cases step; exact first.trans second

/-- Loader read-back never writes the executable field of a ledger account. -/
theorem of_readBack {abi : Abi} {configuration : MemConfig} {program : Nat}
    {buffer : Bytes} {release : Release} :
    ∀ {layout : List SerAcct} {before after : TxState},
      readBack abi configuration program buffer before layout release = .ok after → ExecutableEq
        before after
  | [], before, after, step => by cases step; exact refl _
  | slot :: rest, before, after, step => by
    unfold readBack at step
    split at step
    · exact of_readBack step
    · split at step
      · cases step
      · rename_i middle first
        exact (of_readBackAcct first).trans (of_readBack step)

/-- Caller synchronization copies balances, owner and data. It has no operation
that writes the executable flag, in any supported memory configuration. -/
theorem of_updateCalleeOne {profile : Profile} {context : InvCtx} {before after : InvState}
    {entry : Translated} (step : updateCalleeOne profile context before entry = .ok after) :
    ExecutableEq before.ts after.ts := by
  unfold updateCalleeOne at step
  simp only at step
  split at step
  · cases step
  · rename_i balance balanceStep
    have first := of_lamportStep balanceStep
    split at step
    · cases step
    · rename_i data dataStep
      have second : ExecutableEq balance data.ts := by
        split at dataStep
        · split at dataStep
          · cases dataStep
          · rename_i dataState copied
            cases dataStep
            exact of_dataStep (configuration := .L) (by simpa only [Solanalib.Runtime.dataStep]
              using copied)
        · split at dataStep
          · cases dataStep
          · split at dataStep
            · cases dataStep
            · rename_i resized resizedStep
              have resizedEq : ExecutableEq balance resized := by
                split at resizedStep
                · cases resizedStep; exact refl _
                · exact of_setDataLength resizedStep
              split at dataStep
              · split at dataStep
                · split at dataStep
                  · cases dataStep
                  · rename_i copied copiedStep
                    cases dataStep
                    exact resizedEq.trans (of_setDataFromSlice copiedStep)
                · cases dataStep; exact resizedEq
              · cases dataStep; exact resizedEq
      split at step
      · cases step
      · rename_i result ownerStep
        cases step
        exact first.trans (second.trans (of_ownerStep ownerStep))

theorem of_updateCallee {profile : Profile} {context : InvCtx} :
    ∀ {entries : List Translated} {before after : InvState},
      updateCallee profile context before entries = .ok after → ExecutableEq before.ts after.ts
  | [], before, after, step => by cases step; exact refl _
  | entry :: rest, before, after, step => by
    unfold updateCallee at step
    split at step
    · cases step
    · rename_i middle first
      exact (of_updateCalleeOne first).trans (of_updateCallee step)

theorem of_sysAllocate {context : SysCtx} {before after : TxState} {index : Nat}
    {address : Pubkey × Option Pubkey} {space : Nat}
    (step : sysAllocate context before index address space = .ok after) : ExecutableEq before after
      := by
  unfold sysAllocate at step
  dsimp only at step
  (repeat' split at step) <;> first | cases step | exact of_setDataLength step

theorem of_sysAssign {context : SysCtx} {before after : TxState} {index : Nat}
    {address : Pubkey × Option Pubkey} {owner : Pubkey}
    (step : sysAssign context before index address owner = .ok after) : ExecutableEq before after
      := by
  unfold sysAssign at step
  split at step
  · cases step; exact refl _
  · split at step
    · cases step
    · exact of_setOwner step

theorem of_sysAllocateAndAssign {context : SysCtx} {before after : TxState} {index : Nat}
    {address : Pubkey × Option Pubkey} {space : Nat} {owner : Pubkey}
    (step : sysAllocateAndAssign context before index address space owner = .ok after) :
    ExecutableEq before after := by
  unfold sysAllocateAndAssign at step
  split at step
  · cases step
  · rename_i middle first
    exact (of_sysAllocate first).trans (of_sysAssign step)

theorem of_sysTransferVerified {context : SysCtx} {before after : TxState} {source destination
  amount : Nat}
    (step : sysTransferVerified context before source destination amount = .ok after) :
    ExecutableEq before after := by
  unfold sysTransferVerified at step
  dsimp only at step
  split at step
  · cases step
  · split at step
    · cases step
    · split at step
      · cases step
      · rename_i middle first
        exact (of_checkedSubLamports first).trans (of_checkedAddLamports step)

theorem of_sysTransfer {context : SysCtx} {before after : TxState} {source destination amount : Nat}
    (step : sysTransfer context before source destination amount = .ok after) : ExecutableEq before
      after := by
  unfold sysTransfer at step
  split at step
  · cases step
  · exact of_sysTransferVerified step

theorem of_sysCreateAccount {context : SysCtx} {before after : TxState}
    {address : Pubkey × Option Pubkey} {lamports space : Nat} {owner : Pubkey}
    (step : sysCreateAccount context before address lamports space owner = .ok after) :
    ExecutableEq before after := by
  unfold sysCreateAccount at step
  split at step
  · cases step
  · split at step
    · cases step
    · rename_i middle first
      exact (of_sysAllocateAndAssign first).trans (of_sysTransfer step)

/-- Every interpreted successful native System operation preserves actual
executable flags. Opaque nonce execution is outside this theorem. -/
theorem of_systemProcess {profile : Profile} {primitives : Prims} {before after : TxState} {frame :
  Frame}
    (step : systemProcess profile primitives before frame = some (.ok after)) : ExecutableEq before
      after := by
  unfold systemProcess at step
  split at step
  · cases step
  · split at step <;> (try cases step) <;> (simp only [Option.some.injEq] at step) <;>
      (repeat' split at step) <;> (try cases step) <;>
      first
        | exact refl _
        | exact of_sysCreateAccount (context := ⟨before, frame, profile.release⟩) step
        | exact of_sysAssign (context := ⟨before, frame, profile.release⟩) step
        | exact of_sysTransfer (context := ⟨before, frame, profile.release⟩) step
        | exact of_sysTransferVerified (context := ⟨before, frame, profile.release⟩) step
        | exact of_sysAllocate (context := ⟨before, frame, profile.release⟩) step
        | exact of_sysAllocateAndAssign (context := ⟨before, frame, profile.release⟩) step
        | (refine ExecutableEq.trans ?_ (of_sysTransfer (context := ⟨before, frame,
          profile.release⟩) step)
           exact of_sysAllocateAndAssign (context := ⟨before, frame, profile.release⟩) (by
             assumption))
        | exact of_sysAllocateAndAssign (context := ⟨before, frame, profile.release⟩) (by
          assumption)

theorem of_writeIxSysvarIndex {before after : TxState}
    (step : writeIxSysvarIndex before = .ok after) : ExecutableEq before after := by
  unfold writeIxSysvarIndex at step
  split at step
  · cases step; exact refl _
  · dsimp only at step
    split at step
    · cases step
    · split at step
      · cases step
      · cases step
        exact setAcct _ _ _ rfl

theorem of_push {profile : Profile} {before after : TxState} {frame : Frame}
    (step : push profile before frame = .ok after) : ExecutableEq before after := by
  unfold push at step
  split at step
  · cases step
  · split at step
    · cases step
    · split at step
      · cases step
      · split at step
        · cases step
        · split at step
          · cases step
          · rename_i indexed written
            cases step
            have flags := of_writeIxSysvarIndex written
            exact flags

theorem of_pop {before after : TxState} (step : pop before = .ok after) : ExecutableEq before after
  :=
  of_accounts (pop_spec step).2.1

/-- Compose the actual push, interpreted native System body, and pop.
There is no executable-preservation claim for an arbitrary `ProcInstr`. -/
theorem of_nativeSystem {world : World} {before entered returned after : TxState} {frame : Frame}
    (pushed : push world.prof before frame = .ok entered)
    (body : systemProcess world.prof world.prims (resetReturnData entered) frame = some (.ok
      returned))
    (popped : pop returned = .ok after) : ExecutableEq before after :=
  (of_push pushed).trans ((of_accounts rfl).trans ((of_systemProcess body).trans (of_pop popped)))

end ExecutableEq
end Solanalib.Runtime
