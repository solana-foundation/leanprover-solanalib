/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorViews.Callbacks

/-! Executable graphs of the registered relations, proved by composition of
their actual callback, field-store and ownership combinators. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor

def focused {P V U : Type} (s : World P Effects) (outcome : Outcome Effects V U String) :
    Option (Outcome (World P Effects) V U String) :=
  (some outcome).map (Owned.Focus.snd.liftOutcome s)

def placed {P U : Type} (policy : Borrow.Policy) (wrapper : Wrapper P) (s : World P Effects) :
    Option (Outcome (World P Effects) Borrow.Handle U String) :=
  some (.returned (place policy wrapper s).1 (place policy wrapper s).2)

def cloneFn (storage : InfoStorage) (mode : Nat) (before : World Nat Effects) (g : Borrow.Guard) :
    Option (Outcome (World Nat Effects) Borrow.Handle String String) :=
  match currentCell before.1 g with
  | none => none
  | some cell => match cell.value with
    | none => none
    | some wrapper =>
      (focused before (clonePayloadFn mode before.2
        ⟨⟨g, false⟩, (payloadLocation before.1 ⟨g, false⟩).getD ⟨0⟩, wrapper.account.value⟩)).bind
        (PGraph.bindK fun payload after =>
          (focused after (cloneInfoFn storage after.2 wrapper.account.info)).bind
            (PGraph.bindK fun info finished =>
              placed cell.policy { wrapper with account := ⟨payload, info⟩ } finished))

theorem clone_graph (storage : InfoStorage) (mode : Nat) (before : World Nat Effects) (g :
  Borrow.Guard) :
    PGraph (cloneRun storage (cloneTypes storage mode) before g) (cloneFn storage mode before g) :=
      by
  dsimp only [cloneTypes] at *
  unfold cloneRun cloneFn
  cases hc : currentCell before.1 g with
  | none => simp only; exact PGraph.false
  | some cell =>
    simp only
    cases hw : cell.value with
    | none => simp only; exact PGraph.false
    | some wrapper =>
      simp only
      apply PGraph.bind (PGraph.focusLift Owned.Focus.snd (PGraph.ofFunction (clonePayloadFn mode)
        _ _))
      intro payload after
      apply PGraph.bind (PGraph.focusLift Owned.Focus.snd (cloneInfo_graph storage _ _))
      intro info finished
      exact PGraph.eq_left _

def infoCloneFn (storage : InfoStorage) (before : World Unit Effects) (g : Borrow.Guard) :
    Option (Outcome (World Unit Effects) Borrow.Handle Empty String) :=
  match currentCell before.1 g with
  | none => none
  | some cell => match cell.value with
    | none => none
    | some wrapper =>
      (focused before (cloneInfoFn storage before.2 wrapper.account.info)).bind
        (PGraph.bindK fun info after => placed cell.policy { wrapper with account := ⟨(), info⟩ }
          after)

theorem infoClone_graph (storage : InfoStorage) (before : World Unit Effects) (g : Borrow.Guard) :
    PGraph (infoCloneRun storage (infoCloneTypes storage) before g) (infoCloneFn storage before g)
      := by
  dsimp only [infoCloneTypes] at *
  unfold infoCloneRun infoCloneFn
  cases hc : currentCell before.1 g with
  | none => simp only; exact PGraph.false
  | some cell =>
    simp only
    cases hw : cell.value with
    | none => simp only; exact PGraph.false
    | some wrapper =>
      simp only
      apply PGraph.bind (PGraph.focusLift Owned.Focus.snd (cloneInfo_graph storage _ _))
      intro info after
      exact PGraph.eq_left _

def intoInnerFn (storage : InfoStorage) (before : World Nat Effects) (h : Borrow.Handle) :
    Option (Outcome (World Nat Effects) Nat Empty String) :=
  match before.1.lookupCell h with
  | none => none
  | some cell => match cell.value with
    | none => none
    | some wrapper =>
      if before.1.lease h = .free then
        (focused (retire before h) (dropInfoFn storage before.2 wrapper.account.info)).map
          (Outcome.map fun _ => wrapper.account.value)
      else none

theorem intoInner_graph (storage : InfoStorage) (before : World Nat Effects) (h : Borrow.Handle) :
    PGraph (intoInnerRun storage (moveTypes storage) before h) (intoInnerFn storage before h) := by
  dsimp only [moveTypes] at *
  unfold intoInnerRun intoInnerFn
  cases hc : before.1.lookupCell h with
  | none => simp only; exact PGraph.false
  | some cell =>
    simp only
    cases hw : cell.value with
    | none => simp only; exact PGraph.false
    | some wrapper =>
      simp only
      by_cases free : before.1.lease h = .free
      · simp only [free, ↓reduceIte, true_and]
        exact PGraph.map _ (PGraph.focusLift Owned.Focus.snd (dropInfo_graph storage _ _))
      · simp only [free, ↓reduceIte, false_and]
        exact PGraph.false

def setInnerFn (mode : Nat) (before : World Nat Effects) (args : Borrow.Guard × Nat) :
    Option (Outcome (World Nat Effects) Unit String String) :=
  match current before.1 args.1 with
  | none => none
  | some wrapper =>
    (focused before (dropPayloadFn mode before.2
      ⟨⟨args.1, true⟩, (payloadLocation before.1 ⟨args.1, true⟩).getD ⟨0⟩,
        wrapper.account.value⟩)).map
      (AnchorViewsAssignment.replaceAfter
        (fun state value => ((writePayload state.1 ⟨args.1, true⟩ value).2, state.2)) args.2)

theorem setInner_graph (mode : Nat) (before : World Nat Effects) (args : Borrow.Guard × Nat) :
    PGraph (setInnerRun (setTypes mode) before args) (setInnerFn mode before args) := by
  dsimp only [setTypes] at *
  unfold setInnerRun setInnerFn
  cases hc : current before.1 args.1 with
  | none => simp only; exact PGraph.false
  | some wrapper =>
    simp only
    exact PGraph.exists_eq _ (PGraph.focusLift Owned.Focus.snd (PGraph.ofFunction (dropPayloadFn
      mode) _ _))

def mutableFn (debug : Bool) (before : World Nat Effects) (g : Borrow.Guard) :
    Option (Outcome (World Nat Effects) PayloadRef String String) :=
  match current before.1 g with
  | none => none
  | some wrapper =>
    if debug && !wrapper.account.info.isWritable then
      (focused before (logFn before.2 "The given Account is not mutable")).bind
        (PGraph.bindK fun _ after =>
          (focused after (panicFn after.2 ())).map (Outcome.map fun e : Empty => nomatch e))
    else some (.returned ⟨g, true⟩ before)

theorem mutable_graph (debug : Bool) (before : World Nat Effects) (g : Borrow.Guard) :
    PGraph (mutableRun (mutableTypes debug) before g) (mutableFn debug before g) := by
  dsimp only [mutableTypes] at *
  unfold mutableRun mutableFn
  cases hc : current before.1 g with
  | none => simp only; exact PGraph.false
  | some wrapper =>
    simp only
    by_cases check : (debug && !wrapper.account.info.isWritable) = true
    · simp only [check, ↓reduceIte]
      apply PGraph.bind (PGraph.focusLift Owned.Focus.snd (PGraph.ofFunction logFn _ _))
      intro _ after
      exact PGraph.map _ (PGraph.focusLift Owned.Focus.snd (PGraph.ofFunction panicFn _ _))
    · simp only [check]
      exact PGraph.eq_left _

end SolanalibTest.Conformance.Library.Families.AnchorViews
