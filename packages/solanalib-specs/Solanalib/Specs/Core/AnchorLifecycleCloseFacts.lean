/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleClose

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

/-- Source ownership and SDK mutation use the same current borrow store,
including after reinserting a finite SDK outcome. -/
theorem close_set_borrow (types : CloseTypes) (before : AnchorAccount.World types.Aux)
    (after : AccountInfoSdk.State) : (types.sdk.set before after).1 = after.borrow := by
  rw [← types.borrow_eq]
  rw [types.sdk.get_set]

/-- Zero length cannot reach the SDK memory-zeroing callback, independently
of the backing size or whether an earlier checked borrow fails. -/
theorem closeResize_ne_zero (state : AccountInfoSdk.State) (info : AccountInfo.Value)
    (guard : Borrow.Guard) (oldLen increase : Nat) (after : AccountInfoSdk.State) :
    AccountInfoSdk.prepareResize state ⟨info, 0, false⟩ ≠ .zero guard oldLen increase after := by
  unfold AccountInfoSdk.prepareResize
  dsimp only
  repeat' first | (solve | simp_all) | split

/-- The reviewed resize(0) and legacy realloc(0,false) agree on every modeled
input, including the unchanged-length shortcut and checked-borrow errors. -/
theorem closeResize_zeroInit (state : AccountInfoSdk.State) (info : AccountInfo.Value) :
    AccountInfoSdk.prepareResize state ⟨info, 0, true⟩ =
      AccountInfoSdk.prepareResize state ⟨info, 0, false⟩ := by
  unfold AccountInfoSdk.prepareResize
  dsimp only
  repeat' first | (solve | simp_all) | split

theorem closeResize_exists (state : AccountInfoSdk.State) (info : AccountInfo.Value)
    (ready : AccountInfoSdk.ResizeReady state ⟨info, 0, false⟩) :
    ∃ outcome, closeResize state info = some outcome := by
  have typed := AccountInfoSdk.prepareResize_not_malformed state ⟨info, 0, false⟩ ready
  cases step : AccountInfoSdk.prepareResize state ⟨info, 0, false⟩ with
  | malformed => exact False.elim (typed step)
  | zero guard oldLen increase after => exact False.elim (closeResize_ne_zero _ _ _ _ _ _ step)
  | finished result after => exact ⟨.returned result after, by simp only [closeResize, step]⟩

/-- A successful exclusive acquisition always permits the local u64 write
and one release. The other branch is the checked error or panic of the source. -/
theorem closeWrite_exists (checked : Bool) (profile : AccountInfo.Profile)
    (state : AccountInfoSdk.State) (info : AccountInfo.Value) (amount : Nat) :
    ∃ outcome, closeWrite checked profile state info amount = some outcome := by
  cases acquired : Borrow.acquire state.borrow info.lamports .exclusive AccountInfo.View.whole with
  | mk result during =>
    cases result with
    | error failure =>
      cases checked <;> simp [closeWrite, AccountInfo.tryBorrow, acquired, Except.mapError]
    | ok guard =>
      obtain ⟨live, cells, cell, present⟩ := Borrow.acquire_success acquired
      have found : during.lookupCell info.lamports = some cell := by
        simpa only [Borrow.State.lookupCell, cells] using present
      have written : (Borrow.write during guard (.lamports (UInt64.ofNat amount))).1 = .ok () := by
        simp only [Borrow.write, live, ↓reduceIte, Borrow.replaceCell, found]
      have held : (Borrow.write during guard (.lamports (UInt64.ofNat amount))).2.resolve guard =
          some ⟨info.lamports, .exclusive, 0, .whole⟩ := by
        simp only [Borrow.write, live, ↓reduceIte]
        simpa only [Borrow.State.resolve, Borrow.State.lookupSlot, Borrow.replaceCell_slots] using
          live
      have released := Borrow.release_live held
      simp only [closeWrite, AccountInfo.tryBorrow, acquired, Except.mapError, written, released]
      exact ⟨_, rfl⟩

theorem closeRead_exists (profile : AccountInfo.Profile) (state : AccountInfoSdk.State)
    (info : AccountInfo.Value) (ready : AccountInfo.ObservationReady .lamports state.borrow info) :
    ∃ outcome, closeRead profile state info = some outcome := by
  have typed := AccountInfo.observe_not_malformed .lamports state.borrow info ready
  cases step : AccountInfo.observe .lamports state.borrow info with
  | mk result after =>
    cases result with
    | malformed => exact False.elim (typed (by simp only [step]))
    | value value => exact ⟨_, by simp only [closeRead, step]; rfl⟩
    | borrowFailed => exact ⟨_, by simp only [closeRead, step]; rfl⟩

/-- The owner assignment is observable immediately, including when the later
resize returns an error. No close error rolls this assignment back. -/
theorem CloseBalancesReady.assigned_owner {mode : CloseMode} {state credited zeroed :
  AccountInfoSdk.State}
    {args : CloseArgs} {sourceBalance destinationBalance : Nat}
    (ready : CloseBalancesReady mode state args sourceBalance destinationBalance)
    (small : sourceBalance + destinationBalance < 2^64)
    (credit : closeWrite (mode == .checked) args.profile state args.destination
      (sourceBalance + destinationBalance) = some (.returned (.ok ()) credited))
    (zero : closeWrite false args.profile credited args.info 0 = some (.returned (.ok ()) zeroed)) :
    (AccountInfoSdk.assign zeroed (args.info, AnchorAccount.systemProgramId)).2.owner
      args.info.ownerRef =
      some AnchorAccount.systemProgramId :=
  AccountInfoSdk.assign_alias zeroed args.info args.info _ rfl (ready small credited credit zeroed
    zero).1

theorem CloseBalancesReady.exists {mode : CloseMode} {state : AccountInfoSdk.State}
    {args : CloseArgs} {sourceBalance destinationBalance : Nat}
    (ready : CloseBalancesReady mode state args sourceBalance destinationBalance) :
    ∃ outcome, closeAfterBalances mode args state sourceBalance destinationBalance = some outcome
      := by
  by_cases large : 2^64 ≤ sourceBalance + destinationBalance
  · cases mode <;> simp [closeAfterBalances, large]
  have small : sourceBalance + destinationBalance < 2^64 := Nat.lt_of_not_ge large
  obtain ⟨credited, credit⟩ := closeWrite_exists (mode == .checked) args.profile state
    args.destination
    (sourceBalance + destinationBalance)
  cases credited with
  | terminated reason => simp [closeAfterBalances, large, closeResultBind, closeBind, credit]
  | unwound reason after => simp [closeAfterBalances, large, closeResultBind, closeBind, credit]
  | returned result afterCredit =>
    cases result with
    | error error => simp [closeAfterBalances, large, closeResultBind, closeBind, credit]
    | ok value =>
      obtain ⟨zeroed, zero⟩ := closeWrite_exists false args.profile afterCredit args.info 0
      cases zeroed with
      | terminated reason => simp [closeAfterBalances, large, closeResultBind, closeBind, credit,
        zero]
      | unwound reason after => simp [closeAfterBalances, large, closeResultBind, closeBind,
        credit, zero]
      | returned result afterZero =>
        cases result with
        | error error => simp [closeAfterBalances, large, closeResultBind, closeBind, credit, zero]
        | ok value =>
          obtain ⟨outcome, finished⟩ := closeResize_exists _ args.info
            (ready small afterCredit credit afterZero zero).2
          exact ⟨outcome, by simpa only [closeAfterBalances, large, ↓reduceIte,
            credit, zero, closeResultBind, closeBind] using finished⟩

/-- Every admitted local close has a finite modeled outcome before error
conversion and moved-argument cleanup. No primitive callback return is assumed. -/
theorem CloseCoreReady.exists {mode : CloseMode} {state : AccountInfoSdk.State}
    {args : CloseArgs} (ready : CloseCoreReady mode state args) :
    ∃ outcome, commonCloseCore mode state args = some outcome := by
  cases mode with
  | legacy =>
    obtain ⟨first, firstCalled⟩ := closeRead_exists args.profile state args.destination ready.1
    cases first with
    | terminated reason => simp [commonCloseCore, firstCalled, closeBind]
    | unwound reason after => simp [commonCloseCore, firstCalled, closeBind]
    | returned destinationBalance afterDestination =>
      obtain ⟨second, secondCalled⟩ := closeRead_exists args.profile afterDestination args.info
        (ready.2 destinationBalance afterDestination firstCalled).1
      cases second with
      | terminated reason => simp [commonCloseCore, firstCalled, secondCalled, closeBind]
      | unwound reason after => simp [commonCloseCore, firstCalled, secondCalled, closeBind]
      | returned sourceBalance afterSource =>
        obtain ⟨outcome, finished⟩ := ((ready.2 destinationBalance afterDestination firstCalled).2
          sourceBalance afterSource secondCalled).exists
        exact ⟨outcome, by simpa only [commonCloseCore, firstCalled, secondCalled, closeBind] using
          finished⟩
  | checked =>
    obtain ⟨first, firstCalled⟩ := closeRead_exists args.profile state args.info ready.1
    cases first with
    | terminated reason => simp [commonCloseCore, firstCalled, closeBind]
    | unwound reason after => simp [commonCloseCore, firstCalled, closeBind]
    | returned sourceBalance afterSource =>
      obtain ⟨second, secondCalled⟩ := closeRead_exists args.profile afterSource args.destination
        (ready.2 sourceBalance afterSource firstCalled).1
      cases second with
      | terminated reason => simp [commonCloseCore, firstCalled, secondCalled, closeBind]
      | unwound reason after => simp [commonCloseCore, firstCalled, secondCalled, closeBind]
      | returned destinationBalance afterDestination =>
        obtain ⟨outcome, finished⟩ := ((ready.2 sourceBalance afterSource firstCalled).2
          destinationBalance afterDestination secondCalled).exists
        exact ⟨outcome, by simpa only [commonCloseCore, firstCalled, secondCalled, closeBind] using
          finished⟩

end Solanalib.Specs.Core.AnchorLifecycle
