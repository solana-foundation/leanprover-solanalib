/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck
import Solanalib.Specs.AnchorLang.account_loader

/-! Executable admission checks for the actual legacy common-close prefix.
Each universal premise is decided at its deterministic local read/write exit. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLoader.CloseReady

open Solanalib.Contracts.Model Solanalib.Specs.Core
  SolanalibTest.Conformance.Library.Families.Anchor Anchor.Decide
open AnchorLifecycle

def lamportsB (state : AccountInfoSdk.State) (info : AccountInfo.Value) : Bool :=
  match state.borrow.lookupCell info.lamports with
  | some ⟨.lamports _, _⟩ => true
  | _ => false

theorem lamportsB_iff (state : AccountInfoSdk.State) (info : AccountInfo.Value) :
    lamportsB state info = true ↔ AccountInfo.ObservationReady .lamports state.borrow info := by
  unfold lamportsB AccountInfo.ObservationReady
  cases found : state.borrow.lookupCell info.lamports with
  | none => simp [AccountInfo.Observation.handle, found]
  | some cell =>
    rcases cell with ⟨content, policy⟩
    cases content <;> simp [AccountInfo.Observation.handle, AccountInfo.Observation.project, found]

def resizeZeroB (state : AccountInfoSdk.State) (info : AccountInfo.Value) : Bool :=
  validB state.borrow && match state.borrow.lookupCell info.data with
  | some ⟨.data bytes, _⟩ =>
    if state.borrow.exclusiveCount info.data = 0 ∧ state.borrow.sharedCount info.data = 0 ∧
      bytes.length ≠ 0 then
      (state.buffer info.data).isSome else true
  | _ => false

theorem resizeZeroB_iff (state : AccountInfoSdk.State) (info : AccountInfo.Value) :
    resizeZeroB state info = true ↔ AccountInfoSdk.ResizeReady state ⟨info, 0, false⟩ := by
  unfold resizeZeroB AccountInfoSdk.ResizeReady
  rw [Bool.and_eq_true, validB_iff]
  apply and_congr_right; intro _
  cases found : state.borrow.lookupCell info.data with
  | none => simp
  | some cell =>
    rcases cell with ⟨content, policy⟩
    cases content with
    | lamports amount => simp
    | data bytes =>
      simp only [Option.some.injEq, Borrow.Cell.mk.injEq, AccountInfo.Content.data.injEq]
      by_cases reached : state.borrow.exclusiveCount info.data = 0 ∧
          state.borrow.sharedCount info.data = 0 ∧ bytes.length ≠ 0
      · rcases reached with ⟨exclusive, shared, size⟩
        simp [exclusive, shared, size, Ne.symm size, Option.isSome_iff_exists]
      · simp only [reached, ↓reduceIte, true_iff]
        refine ⟨bytes, policy, ⟨rfl, rfl⟩, ?_⟩
        intro exclusive shared size
        exact False.elim (reached ⟨exclusive, shared, Ne.symm size⟩)

def balancesB (state : AccountInfoSdk.State) (args : CloseArgs)
    (sourceBalance destinationBalance : Nat) : Bool :=
  if sourceBalance + destinationBalance < 2^64 then
    onOkB (closeWrite false args.profile state args.destination (sourceBalance +
      destinationBalance)) fun credited =>
      onOkB (closeWrite false args.profile credited args.info 0) fun zeroed =>
        decide (args.info.ownerRef.id < zeroed.owners.length) &&
          resizeZeroB (AccountInfoSdk.assign zeroed (args.info, AnchorAccount.systemProgramId)).2
            args.info
  else true

theorem balancesB_iff (state : AccountInfoSdk.State) (args : CloseArgs)
    (sourceBalance destinationBalance : Nat) :
    balancesB state args sourceBalance destinationBalance = true ↔
      CloseBalancesReady .legacy state args sourceBalance destinationBalance := by
  unfold balancesB CloseBalancesReady
  by_cases fits : sourceBalance + destinationBalance < 2^64
  · simp only [fits, ↓reduceIte, true_implies]
    apply onOk_iff (Anchor.PGraph.ofOption _) _ _ fun credited => ?_
    apply onOk_iff (Anchor.PGraph.ofOption _) _ _ fun zeroed => ?_
    rw [Bool.and_eq_true, decide_eq_true_eq, resizeZeroB_iff]
  · simp [fits]

def coreB (state : AccountInfoSdk.State) (args : CloseArgs) : Bool :=
  lamportsB state args.destination &&
    onReturnedB (closeRead args.profile state args.destination) fun destinationBalance
      afterDestination =>
      lamportsB afterDestination args.info &&
        onReturnedB (closeRead args.profile afterDestination args.info) fun sourceBalance
          afterSource =>
          balancesB afterSource args sourceBalance destinationBalance

theorem coreB_iff (state : AccountInfoSdk.State) (args : CloseArgs) :
    coreB state args = true ↔ CloseCoreReady .legacy state args := by
  unfold coreB CloseCoreReady
  rw [Bool.and_eq_true, lamportsB_iff]
  apply and_congr_right; intro _
  apply onReturned_iff (Anchor.PGraph.ofOption _) _ _ fun destinationBalance afterDestination => ?_
  rw [Bool.and_eq_true, lamportsB_iff]
  apply and_congr_right; intro _
  exact onReturned_iff (Anchor.PGraph.ofOption _) _ _ fun sourceBalance afterSource =>
    balancesB_iff afterSource args sourceBalance destinationBalance

end SolanalibTest.Conformance.Library.Families.AnchorLoader.CloseReady
