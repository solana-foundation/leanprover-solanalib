/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Graph
import Solanalib.Specs.Core.AccountInfoGuardCallback
import Solanalib.Specs.Core.AnchorLoadingOwned

/-!
# Executable deciders for the predicates of the Anchor preconditions

Boolean functions with proved equivalences to the registered predicates the `requires` of the Anchor
contracts are built from: borrow-store validity, guard
history, the held-guard callback frame (`StateFrame`, `Frame`), token
liveness (`ExitLive`), and quantifiers over the exits of a callback with a
graph (`PGraph`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace SolanalibTest.Conformance.Library.Families.Anchor.Decide

open Solanalib.Contracts.Model Solanalib.Specs.Core

abbrev BState := AccountInfo.State

theorem lookupSlot_lt {s : BState} {id : Nat} {slot : Borrow.Slot AccountInfo.View}
    (h : s.lookupSlot id = some slot) : id < s.slots.length := by
  unfold Borrow.State.lookupSlot at h
  rcases Nat.lt_or_ge id s.slots.length with lt | ge
  · exact lt
  · rw [List.getElem?_eq_none ge] at h
    cases h

theorem lookupCell_lt {s : BState} {handle : Borrow.Handle} {cell : Borrow.Cell AccountInfo.Content}
    (h : s.lookupCell handle = some cell) : handle.cell < s.cells.length := by
  unfold Borrow.State.lookupCell at h
  rcases Nat.lt_or_ge handle.cell s.cells.length with lt | ge
  · exact lt
  · rw [List.getElem?_eq_none ge] at h
    cases h

/-! ## Borrow-store validity -/

def cellOk (s : BState) (h : Nat) : Bool :=
  match s.lookupCell ⟨h⟩ with
  | none => true
  | some cell => decide (s.exclusiveCount ⟨h⟩ ≤ 1 ∧ (s.exclusiveCount ⟨h⟩ = 1 → s.sharedCount ⟨h⟩ =
    0) ∧
      s.sharedCount ⟨h⟩ ≤ cell.policy.sharedLimit)

def slotOk (s : BState) (id : Nat) : Bool :=
  match s.lookupSlot id with
  | none => true
  | some slot => (s.lookupCell slot.cell).isSome

def validB (s : BState) : Bool :=
  (List.range s.slots.length).all (slotOk s) && (List.range s.cells.length).all (cellOk s)

theorem validB_iff (s : BState) : validB s = true ↔ s.Valid := by
  unfold validB Borrow.State.Valid
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun id slot hs => ?_, fun handle cell hc => ?_⟩
    · have := h1 id (lookupSlot_lt hs)
      simp only [slotOk, hs, Option.isSome_iff_exists] at this
      exact this
    · have := h2 handle.cell (lookupCell_lt hc)
      simp only [cellOk, hc, decide_eq_true_eq] at this
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun id _ => ?_, fun h _ => ?_⟩
    · unfold slotOk
      cases hs : s.lookupSlot id with
      | none => rfl
      | some slot =>
        obtain ⟨c, hc⟩ := h1 id slot hs
        simp [hc]
    · unfold cellOk
      cases hc : s.lookupCell ⟨h⟩ with
      | none => rfl
      | some cell =>
        simp only [decide_eq_true_eq]
        exact h2 ⟨h⟩ cell hc

/-! ## Guard history -/

def slotHistoryB : Option (Borrow.Slot AccountInfo.View) → Option (Borrow.Slot AccountInfo.View) →
  Bool
  | none, none => true
  | none, some _ => false
  | some _, none => true
  | some old, some next => decide (next.cell = old.cell ∧ next.mode = old.mode ∧ old.generation ≤
    next.generation)

theorem slotHistoryB_iff (a b : Option (Borrow.Slot AccountInfo.View)) :
    slotHistoryB a b = true ↔ Borrow.SlotHistory a b := by
  cases a <;> cases b <;> simp [slotHistoryB, Borrow.SlotHistory]

def historyB (before after : BState) : Bool :=
  decide (before.slots.length ≤ after.slots.length) &&
    (List.range before.slots.length).all fun id => slotHistoryB (before.lookupSlot id)
      (after.lookupSlot id)

theorem historyB_iff (before after : BState) : historyB before after = true ↔ Borrow.History before
  after := by
  unfold historyB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    slotHistoryB_iff]
  exact ⟨fun ⟨f, e⟩ => ⟨f, e⟩, fun ⟨f, e⟩ => ⟨f, e⟩⟩

/-! ## The held-guard callback frame -/

def cellKeptB (before after : BState) (h : Nat) : Bool :=
  match before.lookupCell ⟨h⟩ with
  | none => true
  | some old => match after.lookupCell ⟨h⟩ with
    | some next => decide (next.policy = old.policy)
    | none => false

def heldUnchangedB (before after : BState) (guard : Borrow.Guard) : Bool :=
  match before.resolve guard with
  | none => true
  | some slot => match before.lookupCell slot.cell, after.lookupCell slot.cell with
    | some old, some next => decide (next.value = old.value)
    | _, _ => true

def stateFrameB (before after : BState) (guard : Borrow.Guard) : Bool :=
  validB after && historyB before after && (List.range before.cells.length).all (cellKeptB before
    after) &&
    decide (after.resolve guard = before.resolve guard) && heldUnchangedB before after guard

theorem stateFrameB_iff (before after : BState) (guard : Borrow.Guard) :
    stateFrameB before after guard = true ↔ AccountInfo.GuardCallback.StateFrame before after guard
      := by
  unfold stateFrameB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, validB_iff,
    historyB_iff]
  constructor
  · rintro ⟨⟨⟨⟨valid, history⟩, cells⟩, held⟩, changes⟩
    refine ⟨valid, history, ?_, held, ?_⟩
    · intro handle old present
      have := cells handle.cell (lookupCell_lt present)
      simp only [cellKeptB, present] at this
      cases hn : after.lookupCell ⟨handle.cell⟩ with
      | none => rw [hn] at this; cases this
      | some next => rw [hn] at this; exact ⟨next, rfl, of_decide_eq_true this⟩
    · intro slot old next live oldFound nextFound
      simp only [heldUnchangedB, live, oldFound, nextFound, decide_eq_true_eq] at changes
      exact changes
  · rintro ⟨valid, history, cells, held, changes⟩
    refine ⟨⟨⟨⟨valid, history⟩, ?_⟩, held⟩, ?_⟩
    · intro h _
      unfold cellKeptB
      cases ho : before.lookupCell ⟨h⟩ with
      | none => rfl
      | some old =>
        obtain ⟨next, found, policy⟩ := cells ⟨h⟩ old ho
        simp [found, policy]
    · unfold heldUnchangedB
      cases hs : before.resolve guard with
      | none => rfl
      | some slot =>
        cases ho : before.lookupCell slot.cell with
        | none => simp only [ho]
        | some old =>
          cases hn : after.lookupCell slot.cell with
          | none => simp only [ho, hn]
          | some next =>
            simp only [ho, hn, decide_eq_true_eq]
            exact changes slot old next hs ho hn

def frameB {Aux V U T : Type} (before : AccountInfo.GuardCallback.World Aux) (guard : Borrow.Guard)
  :
    Outcome (AccountInfo.GuardCallback.World Aux) V U T → Bool
  | .returned _ after | .unwound _ after => stateFrameB before.1 after.1 guard
  | .terminated _ => true

theorem frameB_iff {Aux V U T : Type} (before : AccountInfo.GuardCallback.World Aux) (guard :
  Borrow.Guard)
    (o : Outcome (AccountInfo.GuardCallback.World Aux) V U T) :
    frameB before guard o = true ↔ AccountInfo.GuardCallback.Frame before guard o := by
  cases o <;> simp [frameB, AccountInfo.GuardCallback.Frame, stateFrameB_iff]

/-! ## Quantifiers over the exits of a callback with a graph -/

/-- Every exit of a callback with graph `x` satisfies `q`. -/
def allExitsB {O : Type} (x : Option O) (q : O → Bool) : Bool :=
  match x with
  | none => true
  | some o => q o

theorem allExits_iff {O : Type} {rel : O → Prop} {x : Option O} (h : PGraph rel x) (Q : O → Prop)
    (q : O → Bool) (hq : ∀ o, q o = true ↔ Q o) :
    allExitsB x q = true ↔ ∀ o, rel o → Q o := by
  constructor
  · intro hb o ho
    rw [(h o).mp ho] at hb
    exact (hq o).mp hb
  · intro hall
    cases hx : x with
    | none => rfl
    | some o => exact (hq o).mpr (hall o ((h o).mpr hx))

/-- Every normal exit `(v, s)` of a callback with graph `x` satisfies `q v s`. -/
def onReturnedB {S V U T : Type} (x : Option (Outcome S V U T)) (q : V → S → Bool) : Bool :=
  match x with
  | some (.returned v s) => q v s
  | _ => true

theorem onReturned_iff {S V U T : Type} {rel : Outcome S V U T → Prop} {x : Option (Outcome S V U
  T)}
    (h : PGraph rel x) (Q : V → S → Prop) (q : V → S → Bool) (hq : ∀ v s, q v s = true ↔ Q v s) :
    onReturnedB x q = true ↔ ∀ v s, rel (.returned v s) → Q v s := by
  constructor
  · intro hb v s hr
    rw [(h _).mp hr] at hb
    exact (hq v s).mp hb
  · intro hall
    cases hx : x with
    | none => rfl
    | some o =>
      cases o with
      | returned v s => exact (hq v s).mpr (hall v s ((h _).mpr hx))
      | unwound _ _ => rfl
      | terminated _ => rfl

/-- Every normal `Ok(())` exit `s` of a callback with graph `x` satisfies `q s`. -/
def onOkB {S E U T : Type} (x : Option (Outcome S (Except E Unit) U T)) (q : S → Bool) : Bool :=
  match x with
  | some (.returned (.ok ()) s) => q s
  | _ => true

theorem onOk_iff {S E U T : Type} {rel : Outcome S (Except E Unit) U T → Prop}
    {x : Option (Outcome S (Except E Unit) U T)} (h : PGraph rel x) (Q : S → Prop) (q : S → Bool)
    (hq : ∀ s, q s = true ↔ Q s) :
    onOkB x q = true ↔ ∀ s, rel (.returned (.ok ()) s) → Q s := by
  constructor
  · intro hb s hr
    rw [(h _).mp hr] at hb
    exact (hq s).mp hb
  · intro hall
    cases hx : x with
    | none => rfl
    | some o =>
      cases o with
      | returned v s =>
        cases v with
        | ok u => cases u; exact (hq s).mpr (hall s ((h _).mpr hx))
        | error _ => rfl
      | unwound _ _ => rfl
      | terminated _ => rfl

/-- `Admissible` of a callback with a graph. -/
theorem admissible_iff {Aux A V U T : Type} {guard : Borrow.Guard}
    {run : Callback.Run (AccountInfo.GuardCallback.World Aux) A V U T}
    {before : AccountInfo.GuardCallback.World Aux} {args : A}
    {x : Option (Outcome (AccountInfo.GuardCallback.World Aux) V U T)} (h : PGraph (run before
      args) x) :
    allExitsB x (frameB before guard) = true ↔ AccountInfo.GuardCallback.Admissible guard run
      before args :=
  allExits_iff h _ _ (frameB_iff before guard)

/-! ## Token liveness -/

def exitLiveB {Aux V U T : Type} (guard : Borrow.Guard) :
    Outcome (AnchorAccount.World Aux) V U T → Bool
  | .returned _ after | .unwound _ after => (after.1.resolve guard).isSome
  | .terminated _ => true

theorem exitLiveB_iff {Aux V U T : Type} (guard : Borrow.Guard) (o : Outcome (AnchorAccount.World
  Aux) V U T) :
    exitLiveB guard o = true ↔ AnchorLoadingOwned.ExitLive guard o := by
  cases o <;> simp [exitLiveB, AnchorLoadingOwned.ExitLive, Option.isSome_iff_exists]

theorem liveAt_iff {Aux A V U T : Type} {guard : Borrow.Guard}
    {run : Callback.Run (AnchorAccount.World Aux) A V U T} {before : AnchorAccount.World Aux} {args
      : A}
    {x : Option (Outcome (AnchorAccount.World Aux) V U T)} (h : PGraph (run before args) x) :
    allExitsB x (exitLiveB guard) = true ↔ AnchorLoadingOwned.LiveAt guard run before args :=
  allExits_iff h _ _ (exitLiveB_iff guard)

end SolanalibTest.Conformance.Library.Families.Anchor.Decide
