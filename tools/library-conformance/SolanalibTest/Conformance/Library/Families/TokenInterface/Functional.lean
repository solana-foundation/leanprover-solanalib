/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.Core.OwnedCleanup
import Solanalib.Specs.Core.OwnedFocus
import Solanalib.Specs.Core.OwnedVector

/-!
# Relations with at most one outcome, computed

The operational token models are relations over callback outcomes
(`Callback.Run`, `Callback.bind`, `Owned.protect`, `Owned.cleanup`). At a
family index whose dependencies admit at most one outcome per input (the
registered vector-ledger samples), the composed relation also admits at most
one, and it can be computed. `Fn r f` states that `r` admits exactly the
outcome `f` returns (none if `f` returns `none`). The lemmas below compose
`Fn` through the combinators, so a checker decides `r s a o` by evaluating
`f s a = some o`.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.Functional

open Solanalib.Contracts.Model Solanalib.Specs.Core

universe u

variable {S A V W U T : Type}

/-- `r` admits exactly the outcome computed by `f`. -/
def Fn (r : Callback.Run S A V U T) (f : S → A → Option (Outcome S V U T)) : Prop :=
  ∀ s a o, r s a o ↔ f s a = some o

/-- An outcome predicate admits exactly the computed outcome. -/
def OFn (p : Outcome S V U T → Prop) (x : Option (Outcome S V U T)) : Prop :=
  ∀ o, p o ↔ x = some o

/-- The continuation of `Callback.bind`, on computed outcomes. -/
def thenOpt (i : Outcome S V U T) (g : V → S → Option (Outcome S W U T)) :
    Option (Outcome S W U T) :=
  match i with
  | .returned v st => g v st
  | .unwound r st => some (.unwound r st)
  | .terminated r => some (.terminated r)

theorem bind_fn {r : Callback.Run S A V U T} {f : S → A → Option (Outcome S V U T)}
    (hr : Fn r f) {next : V → S → Outcome S W U T → Prop}
    {g : V → S → Option (Outcome S W U T)} (hn : ∀ v st, OFn (next v st) (g v st)) :
    Fn (Callback.bind r next) (fun s a => (f s a).bind (thenOpt · g)) := by
  intro s a o
  dsimp only
  constructor
  · rintro ⟨i, hi, hm⟩
    rw [(hr s a i).1 hi]
    cases i with
    | returned v st => exact (hn v st o).1 hm
    | unwound r st => simp only [Option.bind_some, thenOpt]; rw [hm]
    | terminated r => simp only [Option.bind_some, thenOpt]; rw [hm]
  · intro h
    cases hf : f s a with
    | none => rw [hf] at h; cases h
    | some i =>
      rw [hf] at h
      refine ⟨i, (hr s a i).2 hf, ?_⟩
      cases i with
      | returned v st => exact (hn v st o).2 h
      | unwound r st =>
        simp only [Option.bind_some, thenOpt, Option.some.injEq] at h
        exact h.symm
      | terminated r =>
        simp only [Option.bind_some, thenOpt, Option.some.injEq] at h
        exact h.symm

theorem map_fn {r : Callback.Run S A V U T} {f : S → A → Option (Outcome S V U T)}
    (hr : Fn r f) (h : V → W) :
    Fn (Callback.map h r) (fun s a => (f s a).map (Outcome.map h)) := by
  intro s a o
  dsimp only
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [(hr s a i).1 hi]
    rfl
  · intro e
    cases hf : f s a with
    | none => rw [hf] at e; cases e
    | some i =>
      rw [hf] at e
      exact ⟨i, (hr s a i).2 hf, Option.some.inj e⟩

theorem ofFunction_fn (run : S → A → Outcome S V U T) :
    Fn (Callback.ofFunction run) (fun s a => some (run s a)) := by
  intro s a o
  exact ⟨fun h => congrArg some h, fun h => Option.some.inj h⟩

theorem returnsOf_fn (run : S → A → V × S) :
    Fn (U := U) (T := T) (returnsOf run)
      (fun s a => some (.returned (run s a).1 (run s a).2)) := by
  intro s a o
  cases o with
  | returned v st =>
    show run s a = (v, st) ↔
      (some (Outcome.returned (run s a).1 (run s a).2) : Option (Outcome S V U T)) =
        some (.returned v st)
    constructor
    · intro h; rw [h]
    · intro h
      simp only [Option.some.injEq, Outcome.returned.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [← h1, ← h2]
  | unwound r st => exact ⟨False.elim, fun h => by cases h⟩
  | terminated r => exact ⟨False.elim, fun h => by cases h⟩

/-! ## Focus -/

theorem lift_fn {Outer Inner : Type} (focus : Owned.Focus Outer Inner)
    {r : Callback.Run Inner A V U T} {f : Inner → A → Option (Outcome Inner V U T)}
    (hr : Fn r f) :
    Fn (focus.lift r) (fun s a => (f (focus.get s) a).map (focus.liftOutcome s)) := by
  intro s a o
  dsimp only
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [(hr _ a i).1 hi]
    rfl
  · intro e
    cases hf : f (focus.get s) a with
    | none => rw [hf] at e; cases e
    | some i =>
      rw [hf] at e
      exact ⟨i, (hr _ a i).2 hf, Option.some.inj e⟩

/-! ## Cleanup -/

/-- Pointwise relation of two lists (core Lean has no `List.Forall₂`). -/
inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : All2 R [] []
  | cons {a b as bs} : R a b → All2 R as bs → All2 R (a :: as) (b :: bs)

/-- A drop action admits exactly the computed outcome. -/
def DFn (d : Owned.DropAction S U T) (f : S → Option (Outcome S Unit U T)) : Prop :=
  ∀ s o, d s o ↔ f s = some o

/-- `Owned.cleanup` on computed drop outcomes, with a functional double-unwind
policy `dbl`. -/
def cleanupF (dbl : S → U → U → T) :
    List (S → Option (Outcome S Unit U T)) → Outcome S V U T → Option (Outcome S V U T)
  | [], pending => some pending
  | fd :: rest, .returned v st => (fd st).bind fun dropped =>
    match dropped with
    | .returned () after => cleanupF dbl rest (.returned v after)
    | .unwound r after => cleanupF dbl rest (.unwound r after)
    | .terminated r => some (.terminated r)
  | fd :: rest, .unwound orig st => (fd st).bind fun dropped =>
    match dropped with
    | .returned () after => cleanupF dbl rest (.unwound orig after)
    | .unwound r after => some (.terminated (dbl after orig r))
    | .terminated r => some (.terminated r)
  | _ :: _, .terminated r => some (.terminated r)

theorem cleanup_fn {double : Owned.DoubleUnwind S U T} {dbl : S → U → U → T}
    (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l) :
    ∀ (drops : List (Owned.DropAction S U T)) (fds : List (S → Option (Outcome S Unit U T))),
      All2 DFn drops fds →
      ∀ (pending final : Outcome S V U T),
        Owned.cleanup double drops pending final ↔ cleanupF dbl fds pending = some final
  | [], [], .nil, pending, final => by
    show final = pending ↔ some pending = some final
    exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
  | d :: drops, fd :: fds, .cons hfd hrest, pending, final => by
    have ih := cleanup_fn hd drops fds hrest
    cases pending with
    | returned v st =>
      show (∃ dropped, d st dropped ∧ _) ↔ (fd st).bind _ = some final
      constructor
      · rintro ⟨dropped, hdrop, hm⟩
        rw [(hfd st dropped).1 hdrop, Option.bind_some]
        cases dropped with
        | returned u after => cases u; exact (ih _ _).1 hm
        | unwound r after => exact (ih _ _).1 hm
        | terminated r => rw [hm]
      · intro h
        cases hf : fd st with
        | none => rw [hf] at h; cases h
        | some dropped =>
          rw [hf, Option.bind_some] at h
          refine ⟨dropped, (hfd st dropped).2 hf, ?_⟩
          cases dropped with
          | returned u after => cases u; exact (ih _ _).2 h
          | unwound r after => exact (ih _ _).2 h
          | terminated r => exact (Option.some.inj h).symm
    | unwound orig st =>
      show (∃ dropped, d st dropped ∧ _) ↔ (fd st).bind _ = some final
      constructor
      · rintro ⟨dropped, hdrop, hm⟩
        rw [(hfd st dropped).1 hdrop, Option.bind_some]
        cases dropped with
        | returned u after => cases u; exact (ih _ _).1 hm
        | unwound r after =>
          obtain ⟨t, ht, rfl⟩ := hm
          rw [(hd _ _ _ _).1 ht]
        | terminated r => rw [hm]
      · intro h
        cases hf : fd st with
        | none => rw [hf] at h; cases h
        | some dropped =>
          rw [hf, Option.bind_some] at h
          refine ⟨dropped, (hfd st dropped).2 hf, ?_⟩
          cases dropped with
          | returned u after => cases u; exact (ih _ _).2 h
          | unwound r after =>
            exact ⟨dbl after orig r, (hd _ _ _ _).2 rfl, (Option.some.inj h).symm⟩
          | terminated r => exact (Option.some.inj h).symm
    | terminated r =>
      show final = .terminated r ↔ some (.terminated r) = some final
      exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩

/-- `Owned.onUnwind` on computed outcomes. -/
def onUnwindF (dbl : S → U → U → T) (fds : List (S → Option (Outcome S Unit U T)))
    (pending : Outcome S V U T) : Option (Outcome S V U T) :=
  match pending with
  | .returned v st => some (.returned v st)
  | .unwound _ _ | .terminated _ => cleanupF dbl fds pending

theorem protect_fn {double : Owned.DoubleUnwind S U T} {dbl : S → U → U → T}
    (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l)
    {drops : List (Owned.DropAction S U T)} {fds : List (S → Option (Outcome S Unit U T))}
    (hdrops : All2 DFn drops fds)
    {body : Callback.Run S A V U T} {f : S → A → Option (Outcome S V U T)} (hb : Fn body f) :
    Fn (Owned.protect double drops body) (fun s a => (f s a).bind (onUnwindF dbl fds)) := by
  intro s a o
  dsimp only
  constructor
  · rintro ⟨pending, hp, hu⟩
    rw [(hb s a pending).1 hp, Option.bind_some]
    cases pending with
    | returned v st => show some (.returned v st) = some o; rw [hu]
    | unwound r st => exact (cleanup_fn hd drops fds hdrops _ _).1 hu
    | terminated r => exact (cleanup_fn hd drops fds hdrops _ _).1 hu
  · intro h
    cases hf : f s a with
    | none => rw [hf] at h; cases h
    | some pending =>
      rw [hf, Option.bind_some] at h
      refine ⟨pending, (hb s a pending).2 hf, ?_⟩
      cases pending with
      | returned v st => exact (Option.some.inj h).symm
      | unwound r st => exact (cleanup_fn hd drops fds hdrops _ _).2 h
      | terminated r => exact (cleanup_fn hd drops fds hdrops _ _).2 h

/-! ## The vector-ledger reference provider -/

section Vector

variable {E : Type}

def modifyF (state : Owned.VectorState E) (resource : Nat) (update : List E → List E) :
    Option (Outcome (Owned.VectorState E) Unit U T) :=
  (state.current resource).map fun values =>
    .returned () (state.set resource (some (update values)))

theorem modify_fn (state : Owned.VectorState E) (resource : Nat) (update : List E → List E) :
    OFn (U := U) (T := T) (state.modify resource update) (modifyF state resource update) := by
  intro o
  unfold Owned.VectorState.modify modifyF
  constructor
  · rintro ⟨values, hv, rfl⟩
    rw [hv]; rfl
  · intro h
    cases hc : state.current resource with
    | none => rw [hc] at h; cases h
    | some values =>
      rw [hc] at h
      exact ⟨values, rfl, (Option.some.inj h).symm⟩

def retireF (state : Owned.VectorState E) (resource : Nat) :
    Option (Outcome (Owned.VectorState E) Unit U T) :=
  (state.current resource).map fun _ => .returned () (state.set resource none)

theorem retire_fn (state : Owned.VectorState E) (resource : Nat) :
    OFn (U := U) (T := T) (state.retire resource) (retireF state resource) := by
  intro o
  unfold Owned.VectorState.retire retireF
  constructor
  · rintro ⟨values, hv, rfl⟩
    rw [hv]; rfl
  · intro h
    cases hc : state.current resource with
    | none => rw [hc] at h; cases h
    | some values =>
      rw [hc] at h
      exact ⟨values, rfl, (Option.some.inj h).symm⟩

theorem vpush_fn : Fn (U := U) (T := T) (Owned.vectorReference (Element := E)).push
    (fun st a => modifyF st a.1 (· ++ [a.2])) := by
  intro st a o
  obtain ⟨r, v⟩ := a
  exact modify_fn st r _ o

theorem vextend_fn : Fn (U := U) (T := T) (Owned.vectorReference (Element := E)).extend
    (fun st a => modifyF st a.1 (· ++ a.2)) := by
  intro st a o
  obtain ⟨r, v⟩ := a
  exact modify_fn st r _ o

theorem vdrop_fn : Fn (U := U) (T := T) (Owned.vectorReference (Element := E)).drop
    (fun st r => retireF st r) :=
  fun st r o => retire_fn st r o

end Vector

end SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
