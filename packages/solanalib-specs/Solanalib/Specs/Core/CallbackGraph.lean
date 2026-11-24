/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.OwnedCleanup
public import Solanalib.Specs.Core.OwnedFocus

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core

/- Graph algebra for explicit finite callback interpretations. These lemmas
compose the existing mathematical callback and cleanup relations; they make
no assertion about SDK implementations, allocation or termination. -/
/-- `rel` admits exactly the value of `x`, if any. -/
def PGraph {O : Type} (rel : O → Prop) (x : Option O) : Prop := ∀ o, rel o ↔ x = some o

namespace PGraph

theorem eq_left {O : Type} (x : O) : PGraph (fun o => o = x) (some x) := by
  intro o; constructor
  · intro h; rw [h]
  · intro h; cases h; rfl

theorem eq_right {O : Type} (x : O) : PGraph (fun o => x = o) (some x) := by
  intro o; constructor
  · intro h; rw [h]
  · intro h; cases h; rfl

theorem false {O : Type} : PGraph (fun (_ : O) => False) none := by
  intro o; exact ⟨False.elim, fun h => by cases h⟩

theorem congr {O : Type} {rel rel' : O → Prop} {x : Option O} (h : PGraph rel x)
    (e : ∀ o, rel' o ↔ rel o) : PGraph rel' x := fun o => (e o).trans (h o)

theorem ofOption {O : Type} (x : Option O) : PGraph (fun o => x = some o) x := fun _ => Iff.rfl

theorem ofFunction {S A V U T : Type} (g : S → A → Outcome S V U T) (b : S) (a : A) :
    PGraph (Callback.ofFunction g b a) (some (g b a)) := by
  intro o; constructor
  · intro h; show some (g b a) = some o; rw [show g b a = o from h]
  · intro h; cases h; rfl

/-- The continuation of `Callback.bind` and `Outcome.bind` on partial functions. -/
def bindK {S V W U T : Type} (g : V → S → Option (Outcome S W U T)) :
    Outcome S V U T → Option (Outcome S W U T)
  | .returned v s => g v s
  | .unwound r s => some (.unwound r s)
  | .terminated r => some (.terminated r)

theorem bind {S A V W U T : Type} {run : Callback.Run S A V U T}
    {next : V → S → Outcome S W U T → Prop} {f : Option (Outcome S V U T)}
    {g : V → S → Option (Outcome S W U T)} {b : S} {a : A}
    (hrun : PGraph (run b a) f) (hnext : ∀ v s, PGraph (next v s) (g v s)) :
    PGraph (Callback.bind run next b a) (f.bind (bindK g)) := by
  intro o
  constructor
  · rintro ⟨i, hi, k⟩
    rw [(hrun i).mp hi]
    cases i with
    | returned v s => exact (hnext v s o).mp k
    | unwound r s => rw [k]; rfl
    | terminated r => rw [k]; rfl
  · intro h
    cases f with
    | none => cases h
    | some i =>
      refine ⟨i, (hrun i).mpr rfl, ?_⟩
      cases i with
      | returned v s => exact (hnext v s o).mpr h
      | unwound r s => cases h; rfl
      | terminated r => cases h; rfl

theorem map {S A V W U T : Type} {run : Callback.Run S A V U T} (k : V → W)
    {f : Option (Outcome S V U T)} {b : S} {a : A} (hrun : PGraph (run b a) f) :
    PGraph (Callback.map k run b a) (f.map (Outcome.map k)) := by
  intro o
  constructor
  · rintro ⟨i, hi, e⟩
    rw [(hrun i).mp hi]; rw [← e]; rfl
  · intro h
    cases f with
    | none => cases h
    | some i => cases h; exact ⟨i, (hrun i).mpr rfl, rfl⟩

/-- An existential over an intermediate outcome followed by a functional step. -/
theorem exists_step {I O : Type} {first : I → Prop} {step : I → O → Prop} {f : Option I}
    {g : I → Option O} (hfirst : PGraph first f) (hstep : ∀ i, PGraph (step i) (g i)) :
    PGraph (fun o => ∃ i, first i ∧ step i o) (f.bind g) := by
  intro o
  constructor
  · rintro ⟨i, hi, hs⟩
    rw [(hfirst i).mp hi]; exact (hstep i o).mp hs
  · intro h
    cases f with
    | none => cases h
    | some i => exact ⟨i, (hfirst i).mpr rfl, (hstep i o).mpr h⟩

/-- An existential over an intermediate outcome followed by an equation. -/
theorem exists_eq {I O : Type} {first : I → Prop} {f : Option I} (k : I → O)
    (hfirst : PGraph first f) : PGraph (fun o => ∃ i, first i ∧ k i = o) (f.map k) := by
  intro o
  constructor
  · rintro ⟨i, hi, e⟩
    rw [(hfirst i).mp hi, ← e]; rfl
  · intro h
    cases f with
    | none => cases h
    | some i => cases h; exact ⟨i, (hfirst i).mpr rfl, rfl⟩

/-- An existential over an intermediate outcome followed by an equation, reversed. -/
theorem exists_eq' {I O : Type} {first : I → Prop} {f : Option I} (k : I → O)
    (hfirst : PGraph first f) : PGraph (fun o => ∃ i, first i ∧ o = k i) (f.map k) :=
  congr (exists_eq k hfirst) fun _ => exists_congr fun _ => and_congr_right fun _ => eq_comm

/-- An existential over an intermediate outcome followed by a partial step. -/
theorem exists_opt {I O : Type} {first : I → Prop} {f : Option I} (k : I → Option O)
    (hfirst : PGraph first f) : PGraph (fun o => ∃ i, first i ∧ k i = some o) (f.bind k) :=
  exists_step hfirst fun i => ofOption (k i)

/-- Callback-free partial cleanup over a list of drop actions (`Owned.cleanup`). -/
def cleanupFn {S V U T : Type} (double : S → U → U → Option T) :
    List (S → Option (Outcome S Unit U T)) → Outcome S V U T → Option (Outcome S V U T)
  | [], pending => some pending
  | action :: rest, .returned value state =>
    (action state).bind fun dropped => match dropped with
      | .returned () after => cleanupFn double rest (.returned value after)
      | .unwound reason after => cleanupFn double rest (.unwound reason after)
      | .terminated reason => some (.terminated reason)
  | action :: rest, .unwound original state =>
    (action state).bind fun dropped => match dropped with
      | .returned () after => cleanupFn double rest (.unwound original after)
      | .unwound reason after => (double after original reason).map .terminated
      | .terminated reason => some (.terminated reason)
  | _ :: _, .terminated reason => some (.terminated reason)

/-- Pointwise graphs of a list of drop actions. -/
def DropsGraph {S U T : Type} : List (Owned.DropAction S U T) →
    List (S → Option (Outcome S Unit U T)) → Prop
  | [], [] => True
  | d :: ds, f :: fs => (∀ s, PGraph (d s) (f s)) ∧ DropsGraph ds fs
  | _, _ => False

theorem DropsGraph.nil {S U T : Type} : DropsGraph ([] : List (Owned.DropAction S U T)) [] :=
  trivial

theorem DropsGraph.cons {S U T : Type} {d : Owned.DropAction S U T} {ds : List (Owned.DropAction S
  U T)}
    {f : S → Option (Outcome S Unit U T)} {fs : List (S → Option (Outcome S Unit U T))}
    (h : ∀ s, PGraph (d s) (f s)) (t : DropsGraph ds fs) : DropsGraph (d :: ds) (f :: fs) := ⟨h, t⟩

theorem cleanup {S V U T : Type} {double : Owned.DoubleUnwind S U T}
    {doubleFn : S → U → U → Option T}
    (hdouble : ∀ s r r', PGraph (double s r r') (doubleFn s r r')) :
    ∀ (drops : List (Owned.DropAction S U T)) (fns : List (S → Option (Outcome S Unit U T))),
      DropsGraph drops fns → ∀ pending : Outcome S V U T,
      PGraph (Owned.cleanup double drops pending) (cleanupFn doubleFn fns pending)
  | [], [], _, pending => by
    intro o; show o = pending ↔ some pending = some o
    exact ⟨fun h => by rw [h], fun h => by cases h; rfl⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim
  | d :: ds, f :: fs, ⟨hd, hds⟩, .returned value state => by
    apply exists_step (hd state)
    intro dropped
    cases dropped with
    | returned u after => cases u; exact cleanup hdouble ds fs hds _
    | unwound reason after => exact cleanup hdouble ds fs hds _
    | terminated reason => exact eq_left _
  | d :: ds, f :: fs, ⟨hd, hds⟩, .unwound original state => by
    apply exists_step (hd state)
    intro dropped
    cases dropped with
    | returned u after => cases u; exact cleanup hdouble ds fs hds _
    | unwound reason after =>
      exact exists_eq' Outcome.terminated (hdouble after original reason)
    | terminated reason => exact eq_left _
  | _ :: _, _ :: _, _, .terminated reason => eq_left _

/-- `Owned.onUnwind` on partial functions. -/
def onUnwindFn {S V U T : Type} (double : S → U → U → Option T)
    (fns : List (S → Option (Outcome S Unit U T))) : Outcome S V U T → Option (Outcome S V U T)
  | .returned value state => some (.returned value state)
  | pending => cleanupFn double fns pending

theorem onUnwind {S V U T : Type} {double : Owned.DoubleUnwind S U T}
    {doubleFn : S → U → U → Option T}
    (hdouble : ∀ s r r', PGraph (double s r r') (doubleFn s r r'))
    {drops : List (Owned.DropAction S U T)} {fns : List (S → Option (Outcome S Unit U T))}
    (hdrops : DropsGraph drops fns) (pending : Outcome S V U T) :
    PGraph (Owned.onUnwind double drops pending) (onUnwindFn doubleFn fns pending) := by
  cases pending with
  | returned value state => exact eq_left _
  | unwound reason state => exact cleanup hdouble drops fns hdrops _
  | terminated reason => exact cleanup hdouble drops fns hdrops _

theorem scope {S A V U T : Type} {double : Owned.DoubleUnwind S U T}
    {doubleFn : S → U → U → Option T}
    (hdouble : ∀ s r r', PGraph (double s r r') (doubleFn s r r'))
    {drops : List (Owned.DropAction S U T)} {fns : List (S → Option (Outcome S Unit U T))}
    (hdrops : DropsGraph drops fns) {body : Callback.Run S A V U T}
    {f : Option (Outcome S V U T)} {b : S} {a : A} (hbody : PGraph (body b a) f) :
    PGraph (Owned.scope double drops body b a) (f.bind (cleanupFn doubleFn fns)) :=
  exists_step hbody fun pending => cleanup hdouble drops fns hdrops pending

theorem protect {S A V U T : Type} {double : Owned.DoubleUnwind S U T}
    {doubleFn : S → U → U → Option T}
    (hdouble : ∀ s r r', PGraph (double s r r') (doubleFn s r r'))
    {drops : List (Owned.DropAction S U T)} {fns : List (S → Option (Outcome S Unit U T))}
    (hdrops : DropsGraph drops fns) {body : Callback.Run S A V U T}
    {f : Option (Outcome S V U T)} {b : S} {a : A} (hbody : PGraph (body b a) f) :
    PGraph (Owned.protect double drops body b a) (f.bind (onUnwindFn doubleFn fns)) :=
  exists_step hbody fun pending => onUnwind hdouble hdrops pending

theorem focusLift {Outer Inner A V U T : Type} (focus : Owned.Focus Outer Inner)
    {run : Callback.Run Inner A V U T} {f : Option (Outcome Inner V U T)} {b : Outer} {a : A}
    (hrun : PGraph (run (focus.get b) a) f) :
    PGraph (focus.lift run b a) (f.map (focus.liftOutcome b)) :=
  exists_eq _ hrun

end PGraph

end Solanalib.Specs.Core
