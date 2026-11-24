/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
import Solanalib.Specs.Core.TokenRequestAllocatedControl
import Solanalib.Specs.Core.TokenRequestAllocatedSeedsUnpack
import Solanalib.Specs.Core.AccountInfoRc

/-!
# Result-aware control combinators, computed

The operational model `Token.OnchainAllocated` (spl-token-2022 11.0.0
`onchain::invoke_transfer_checked`) is written in the Result-aware combinators
of `Token.AllocatedControl`. An `AllocatedControl.Run` relates a state to the
outcomes it admits; its return value is a `Result`. This module computes these
combinators, as `Functional` does for the `Callback` combinators.

`RFn r f` states that `r` admits exactly the outcome that `f` computes, and no
outcome when `f` returns `none`. For each combinator `X` of `AllocatedControl`
there is a computed form `XR` and a lemma `XR_fn : RFn (X …) (XR …)`, which
takes the `RFn`, `Fn` or `DFn` facts of the arguments. A component proves `RFn`
of a model function by composing these lemmas, with its computed function
built from the same `XR` forms in the same order.

The last section computes the Callback-level combinators that the onchain model
uses beyond those of `Functional`: `Owned.scope`, `AllocatedSeeds.bindResult`,
`AccountInfoRc.lift` and the list iteration `forEach`.

Naming: the computed forms of `AllocatedControl` combinators end in `R`, and
their lemmas are `XR_fn`. The computed forms of Callback-level relations end in
`F`, as in `Functional`, and their lemmas are named after the relation
(`Owned.scope_fn`). These names do not clash with those of `Functional`, so a
module can open both namespaces.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional

variable {S A V W U T : Type}

/-! ## Computed Result-aware runs -/

/-- A computed Result-aware run: the outcome from the given state, or `none`
when the relation admits no outcome. -/
abbrev RRun (S V U T : Type) := S → Option (Outcome S (Except Token.Error V) U T)

/-- `r` admits exactly the outcome computed by `f`. -/
def RFn (r : AllocatedControl.Run S V U T) (f : RRun S V U T) : Prop :=
  ∀ s o, r s o ↔ f s = some o

/-- A Callback-level run with an `Except` value, at fixed arguments, is a
Result-aware run. This covers `fun state => r state a` in the model. -/
theorem call_fn {r : Callback.Run S A (Except Token.Error V) U T}
    {f : S → A → Option (Outcome S (Except Token.Error V) U T)} (hr : Fn r f) (a : A) :
    RFn (fun s => r s a) (fun s => f s a) :=
  fun s o => hr s a o

/-- Both branches of a model `if` are computed by the same `if`. -/
theorem iteR_fn (c : Prop) [Decidable c] {r₁ r₂ : AllocatedControl.Run S V U T}
    {f₁ f₂ : RRun S V U T} (h₁ : c → RFn r₁ f₁) (h₂ : ¬c → RFn r₂ f₂) :
    RFn (if c then r₁ else r₂) (if c then f₁ else f₂) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h₁ hc
  · simp only [hc, ↓reduceIte]; exact h₂ hc

/-! ## Pure steps -/

/-- `AllocatedControl.pure`, computed. -/
def pureR (v : V) : RRun S V U T := fun s => some (.returned (.ok v) s)

/-- `AllocatedControl.pure v` admits exactly `pureR v`. -/
theorem pureR_fn (v : V) : RFn (S := S) (U := U) (T := T) (AllocatedControl.pure v) (pureR v) :=
  fun _ _ => ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩

/-- `AllocatedControl.fail`, computed. -/
def failR (e : Token.Error) : RRun S V U T := fun s => some (.returned (.error e) s)

/-- `AllocatedControl.fail e` admits exactly `failR e`. -/
theorem failR_fn (e : Token.Error) :
    RFn (S := S) (V := V) (U := U) (T := T) (AllocatedControl.fail e) (failR e) :=
  fun _ _ => ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩

/-- `AllocatedControl.result`, computed. -/
def resultR (x : Except Token.Error V) : RRun S V U T := fun s => some (.returned x s)

/-- `AllocatedControl.result x` admits exactly `resultR x`. -/
theorem resultR_fn (x : Except Token.Error V) :
    RFn (S := S) (U := U) (T := T) (AllocatedControl.result x) (resultR x) :=
  fun _ _ => ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩

/-- `AllocatedControl.inspect`, computed: an absent observation admits no outcome. -/
def inspectR (observe : S → Option V) : RRun S V U T :=
  fun s => (observe s).map fun v => .returned (.ok v) s

/-- `AllocatedControl.inspect observe` admits exactly `inspectR observe`. -/
theorem inspectR_fn (observe : S → Option V) :
    RFn (U := U) (T := T) (AllocatedControl.inspect observe) (inspectR observe) := by
  intro s o
  constructor
  · rintro ⟨v, hv, rfl⟩
    show (observe s).map _ = _
    rw [hv]; rfl
  · intro h
    cases hv : observe s with
    | none => simp [inspectR, hv] at h
    | some v =>
      simp only [inspectR, hv, Option.map_some, Option.some.injEq] at h
      exact ⟨v, hv, h.symm⟩

/-! ## Sequencing -/

/-- the continuation of `AllocatedControl.bind` on a computed outcome: only `Ok`
reaches `g`; an `Err`, an unwind and a terminal exit are kept. -/
def thenR (i : Outcome S (Except Token.Error V) U T) (g : V → RRun S W U T) :
    Option (Outcome S (Except Token.Error W) U T) :=
  match i with
  | .returned (.ok v) st => g v st
  | .returned (.error e) st => some (.returned (.error e) st)
  | .unwound r st => some (.unwound r st)
  | .terminated r => some (.terminated r)

/-- `AllocatedControl.bind`, computed. -/
def bindR (f : RRun S V U T) (g : V → RRun S W U T) : RRun S W U T :=
  fun s => (f s).bind (thenR · g)

/-- `AllocatedControl.bind first next` admits exactly `bindR f g`. -/
theorem bindR_fn {first : AllocatedControl.Run S V U T} {f : RRun S V U T} (hf : RFn first f)
    {next : V → AllocatedControl.Run S W U T} {g : V → RRun S W U T}
    (hg : ∀ v, RFn (next v) (g v)) :
    RFn (AllocatedControl.bind first next) (bindR f g) := by
  intro s o
  constructor
  · rintro ⟨i, hi, hm⟩
    show (f s).bind (thenR · g) = some o
    rw [(hf s i).1 hi, Option.bind_some]
    cases i with
    | returned x st =>
      cases x with
      | ok v => exact (hg v st o).1 hm
      | error e => exact (congrArg some hm).symm
    | unwound r st => exact (congrArg some hm).symm
    | terminated r => exact (congrArg some hm).symm
  · intro h
    cases hfs : f s with
    | none => simp [bindR, hfs] at h
    | some i =>
      simp only [bindR, hfs, Option.bind_some] at h
      refine ⟨i, (hf s i).2 hfs, ?_⟩
      cases i with
      | returned x st =>
        cases x with
        | ok v => exact (hg v st o).2 h
        | error e => exact (Option.some.inj h).symm
      | unwound r st => exact (Option.some.inj h).symm
      | terminated r => exact (Option.some.inj h).symm

/-! ## Dependency calls -/

/-- `AllocatedControl.perform`, computed from the computed outcome of the call. -/
def performR (callF : S → Option (Outcome S V U T)) : RRun S V U T :=
  fun s => (callF s).map (Outcome.map Except.ok)

/-- `AllocatedControl.perform call` admits exactly `performR callF` when the
call admits exactly `callF`. -/
theorem performR_fn {call : S → Outcome S V U T → Prop} {callF : S → Option (Outcome S V U T)}
    (hc : ∀ s, OFn (call s) (callF s)) :
    RFn (AllocatedControl.perform call) (performR callF) := by
  intro s o
  constructor
  · rintro ⟨i, hi, rfl⟩
    show (callF s).map _ = _
    rw [(hc s i).1 hi]; rfl
  · intro h
    cases hcs : callF s with
    | none => simp [performR, hcs] at h
    | some i =>
      simp only [performR, hcs, Option.map_some, Option.some.injEq] at h
      exact ⟨i, (hc s i).2 hcs, h⟩

/-- The usual `perform fun state => run state a` of the model, for a dependency
`run` computed by `f`. -/
theorem performCall_fn {run : Callback.Run S A V U T} {f : S → A → Option (Outcome S V U T)}
    (hr : Fn run f) (a : A) :
    RFn (AllocatedControl.perform fun s => run s a) (performR fun s => f s a) :=
  performR_fn fun s o => hr s a o

/-- Any two maps out of `Empty` act alike on outcomes. -/
theorem outcome_map_empty {X : Type} (f g : Empty → X) (o : Outcome S Empty U T) :
    Outcome.map f o = Outcome.map g o := by
  cases o with
  | returned v _ => exact v.elim
  | unwound _ _ => rfl
  | terminated _ => rfl

/-- `AllocatedControl.panic`, computed from the computed outcome of the panic dependency. -/
def panicR (callF : S → Option (Outcome S Empty U T)) : RRun S V U T :=
  fun s => (callF s).map (Outcome.map Empty.elim)

/-- `AllocatedControl.panic call` admits exactly `panicR callF`. -/
theorem panicR_fn {call : S → Outcome S Empty U T → Prop} {callF : S → Option (Outcome S Empty U T)}
    (hc : ∀ s, OFn (call s) (callF s)) :
    RFn (V := V) (AllocatedControl.panic call) (panicR callF) := by
  intro s o
  constructor
  · rintro ⟨i, hi, rfl⟩
    show (callF s).map _ = _
    rw [(hc s i).1 hi]
    exact congrArg some (outcome_map_empty _ _ i)
  · intro h
    cases hcs : callF s with
    | none => simp [panicR, hcs] at h
    | some i =>
      simp only [panicR, hcs, Option.map_some, Option.some.injEq] at h
      exact ⟨i, (hc s i).2 hcs, (outcome_map_empty _ _ i).trans h⟩

/-! ## Cleanup -/

/-- `AllocatedControl.scope`, computed: the body, then `cleanupF` on every exit. -/
def scopeR (dbl : S → U → U → T) (fds : List (S → Option (Outcome S Unit U T)))
    (bodyF : RRun S V U T) : RRun S V U T :=
  fun s => (bodyF s).bind (cleanupF dbl fds)

/-- `AllocatedControl.scope double drops body` admits exactly
`scopeR dbl fds bodyF`. -/
theorem scopeR_fn {double : Owned.DoubleUnwind S U T} {dbl : S → U → U → T}
    (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l)
    {drops : List (Owned.DropAction S U T)} {fds : List (S → Option (Outcome S Unit U T))}
    (hdrops : All2 DFn drops fds) {body : AllocatedControl.Run S V U T} {bodyF : RRun S V U T}
    (hb : RFn body bodyF) :
    RFn (AllocatedControl.scope double drops body) (scopeR dbl fds bodyF) := by
  intro s o
  constructor
  · rintro ⟨pending, hp, hc⟩
    show (bodyF s).bind _ = some o
    rw [(hb s pending).1 hp, Option.bind_some]
    exact (cleanup_fn hd drops fds hdrops pending o).1 hc
  · intro h
    cases hf : bodyF s with
    | none => simp [scopeR, hf] at h
    | some pending =>
      simp only [scopeR, hf, Option.bind_some] at h
      exact ⟨pending, (hb s pending).2 hf, (cleanup_fn hd drops fds hdrops pending o).2 h⟩

/-- the exit of `AllocatedControl.moveOnOk` on a computed outcome: `Ok` moves out
unchanged; an `Err`, an unwind or a terminal exit goes through `cleanupF`. -/
def unlessOkF (dbl : S → U → U → T) (fds : List (S → Option (Outcome S Unit U T)))
    (pending : Outcome S (Except Token.Error V) U T) :
    Option (Outcome S (Except Token.Error V) U T) :=
  match pending with
  | .returned (.ok v) st => some (.returned (.ok v) st)
  | .returned (.error e) st => cleanupF dbl fds (.returned (.error e) st)
  | .unwound r st => cleanupF dbl fds (.unwound r st)
  | .terminated r => cleanupF dbl fds (.terminated r)

/-- `AllocatedControl.moveOnOk`, computed. -/
def moveOnOkR (dbl : S → U → U → T) (fds : List (S → Option (Outcome S Unit U T)))
    (bodyF : RRun S V U T) : RRun S V U T :=
  fun s => (bodyF s).bind (unlessOkF dbl fds)

/-- `AllocatedControl.moveOnOk double drops body` admits exactly
`moveOnOkR dbl fds bodyF`. -/
theorem moveOnOkR_fn {double : Owned.DoubleUnwind S U T} {dbl : S → U → U → T}
    (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l)
    {drops : List (Owned.DropAction S U T)} {fds : List (S → Option (Outcome S Unit U T))}
    (hdrops : All2 DFn drops fds) {body : AllocatedControl.Run S V U T} {bodyF : RRun S V U T}
    (hb : RFn body bodyF) :
    RFn (AllocatedControl.moveOnOk double drops body) (moveOnOkR dbl fds bodyF) := by
  have hc := cleanup_fn (V := Except Token.Error V) hd drops fds hdrops
  intro s o
  constructor
  · rintro ⟨pending, hp, hm⟩
    show (bodyF s).bind _ = some o
    rw [(hb s pending).1 hp, Option.bind_some]
    cases pending with
    | returned x st =>
      cases x with
      | ok v => exact (congrArg some hm).symm
      | error e => exact (hc _ o).1 hm
    | unwound r st => exact (hc _ o).1 hm
    | terminated r => exact (hc _ o).1 hm
  · intro h
    cases hf : bodyF s with
    | none => simp [moveOnOkR, hf] at h
    | some pending =>
      simp only [moveOnOkR, hf, Option.bind_some] at h
      refine ⟨pending, (hb s pending).2 hf, ?_⟩
      cases pending with
      | returned x st =>
        cases x with
        | ok v => exact (Option.some.inj h).symm
        | error e => exact (hc _ o).2 h
      | unwound r st => exact (hc _ o).2 h
      | terminated r => exact (hc _ o).2 h

/-! ## Account-data steps -/

section Data

variable {X : Type}

/-- `AllocatedControl.fromStep`, computed from the computed
form of the panic dependency `raiseF`. A `.malformed` step admits no outcome, so it computes `none`.
-/
def fromStepR
    (raiseF : AccountInfo.State × X → Onchain.Panic →
      Option (Outcome (AccountInfo.State × X) Empty U T))
    (step : AccountInfo.State → Onchain.Step V × AccountInfo.State) :
    RRun (AccountInfo.State × X) V U T :=
  fun s =>
    match step s.1 with
    | (.success v, after) => some (.returned (.ok v) (after, s.2))
    | (.error e, after) => some (.returned (.error e) (after, s.2))
    | (.panic r, after) => panicR (fun st => raiseF st r) (after, s.2)
    | (.malformed, _) => none

/-- `AllocatedControl.fromStep raise step` admits exactly `fromStepR raiseF step`. -/
theorem fromStepR_fn {raise : Callback.Run (AccountInfo.State × X) Onchain.Panic Empty U T}
    {raiseF : AccountInfo.State × X → Onchain.Panic →
      Option (Outcome (AccountInfo.State × X) Empty U T)}
    (hraise : Fn raise raiseF) (step : AccountInfo.State → Onchain.Step V × AccountInfo.State) :
    RFn (AllocatedControl.fromStep raise step) (fromStepR raiseF step) := by
  intro s o
  unfold AllocatedControl.fromStep fromStepR
  cases step s.1 with
  | mk value after =>
    cases value with
    | success v => exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
    | error e => exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
    | panic r => exact panicR_fn (fun st o => hraise st r o) (after, s.2) o
    | malformed => exact ⟨False.elim, fun h => by cases h⟩

/-- `AllocatedControl.borrow`, computed: the data borrow of `info`, checked or
unchecked, retaining its guard and the copied slice length. -/
def borrowR
    (raiseF : AccountInfo.State × X → Onchain.Panic →
      Option (Outcome (AccountInfo.State × X) Empty U T))
    (checked : Bool) (info : AccountInfo.Value) :
    RRun (AccountInfo.State × X) AllocatedControl.DataRef U T :=
  fun s =>
    match Onchain.borrowData checked s.1 info with
    | (.success borrowed, after) =>
      some (.returned (.ok ⟨borrowed.guard, borrowed.bytes.length⟩) (after, s.2))
    | (.error e, after) => some (.returned (.error e) (after, s.2))
    | (.panic r, after) => panicR (fun st => raiseF st r) (after, s.2)
    | (.malformed, _) => none

/-- `AllocatedControl.borrow raise checked info` admits exactly
`borrowR raiseF checked info`. -/
theorem borrowR_fn {raise : Callback.Run (AccountInfo.State × X) Onchain.Panic Empty U T}
    {raiseF : AccountInfo.State × X → Onchain.Panic →
      Option (Outcome (AccountInfo.State × X) Empty U T)}
    (hraise : Fn raise raiseF) (checked : Bool) (info : AccountInfo.Value) :
    RFn (AllocatedControl.borrow raise checked info) (borrowR raiseF checked info) := by
  intro s o
  unfold AllocatedControl.borrow AllocatedControl.fromStep borrowR
  dsimp only
  cases Onchain.borrowData checked s.1 info with
  | mk value after =>
    cases value with
    | success borrowed => exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
    | error e => exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
    | panic r => exact panicR_fn (fun st o => hraise st r o) (after, s.2) o
    | malformed => exact ⟨False.elim, fun h => by cases h⟩

/-- `AllocatedControl.DataRef.drop`, computed: a failed release admits no outcome. -/
def DataRef.dropF (reference : AllocatedControl.DataRef) :
    AccountInfo.State × X → Option (Outcome (AccountInfo.State × X) Unit U T) :=
  fun s =>
    match Borrow.release s.1 reference.guard with
    | (.ok (), after) => some (.returned () (after, s.2))
    | (.error _, _) => none

/-- The guard release `reference.drop` admits exactly `DataRef.dropF reference`. -/
theorem DataRef.drop_fn (reference : AllocatedControl.DataRef) :
    DFn (reference.drop (Extra := X) (Unwind := U) (Terminal := T)) (DataRef.dropF reference) := by
  intro s o
  unfold AllocatedControl.DataRef.drop DataRef.dropF
  cases Borrow.release s.1 reference.guard with
  | mk r after =>
    cases r with
    | ok u => cases u; exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
    | error e => exact ⟨False.elim, fun h => by cases h⟩

/-- `AllocatedControl.withData`, computed: borrow, then the body in a scope
that releases the guard. -/
def withDataR
    (raiseF : AccountInfo.State × X → Onchain.Panic →
      Option (Outcome (AccountInfo.State × X) Empty U T))
    (dbl : AccountInfo.State × X → U → U → T) (checked : Bool) (info : AccountInfo.Value)
    (bodyF : AllocatedControl.DataRef → RRun (AccountInfo.State × X) V U T) :
    RRun (AccountInfo.State × X) V U T :=
  bindR (borrowR raiseF checked info) fun reference =>
    scopeR dbl [DataRef.dropF reference] (bodyF reference)

/-- `AllocatedControl.withData raise double checked info body` admits exactly
`withDataR raiseF dbl checked info bodyF`. -/
theorem withDataR_fn {raise : Callback.Run (AccountInfo.State × X) Onchain.Panic Empty U T}
    {raiseF : AccountInfo.State × X → Onchain.Panic →
      Option (Outcome (AccountInfo.State × X) Empty U T)}
    (hraise : Fn raise raiseF)
    {double : Owned.DoubleUnwind (AccountInfo.State × X) U T}
    {dbl : AccountInfo.State × X → U → U → T} (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l)
    (checked : Bool) (info : AccountInfo.Value)
    {body : AllocatedControl.DataRef → AllocatedControl.Run (AccountInfo.State × X) V U T}
    {bodyF : AllocatedControl.DataRef → RRun (AccountInfo.State × X) V U T}
    (hb : ∀ reference, RFn (body reference) (bodyF reference)) :
    RFn (AllocatedControl.withData raise double checked info body)
      (withDataR raiseF dbl checked info bodyF) :=
  bindR_fn (borrowR_fn hraise checked info) fun reference =>
    scopeR_fn hd (.cons (DataRef.drop_fn reference) .nil) (hb reference)

end Data

/-! ## Lists of computed drops -/

/-- Pointwise facts concatenate. -/
theorem All2.append {α β : Type} {R : α → β → Prop} :
    ∀ {as bs cs ds : _}, All2 R as bs → All2 R cs ds → All2 R (as ++ cs) (bs ++ ds)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons x hs, h => .cons x (All2.append hs h)

/-- A pointwise fact holds of two maps of the same list. -/
theorem All2.map {α β γ : Type} {R : β → γ → Prop} (f : α → β) (g : α → γ)
    (h : ∀ a, R (f a) (g a)) : ∀ l : List α, All2 R (l.map f) (l.map g)
  | [] => .nil
  | a :: rest => .cons (h a) (All2.map f g h rest)

/-! ## Callback-level combinators -/

/-- `Owned.scope`, computed: the body, then `cleanupF` on every exit. -/
def Owned.scopeF (dbl : S → U → U → T) (fds : List (S → Option (Outcome S Unit U T)))
    (f : S → A → Option (Outcome S V U T)) : S → A → Option (Outcome S V U T) :=
  fun s a => (f s a).bind (cleanupF dbl fds)

/-- `Owned.scope double drops body` admits exactly `Owned.scopeF dbl fds f`. -/
theorem Owned.scope_fn {double : Owned.DoubleUnwind S U T} {dbl : S → U → U → T}
    (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l)
    {drops : List (Owned.DropAction S U T)} {fds : List (S → Option (Outcome S Unit U T))}
    (hdrops : All2 DFn drops fds) {body : Callback.Run S A V U T}
    {f : S → A → Option (Outcome S V U T)} (hb : Fn body f) :
    Fn (Owned.scope double drops body) (Owned.scopeF dbl fds f) := by
  intro s a o
  constructor
  · rintro ⟨pending, hp, hc⟩
    show (f s a).bind _ = some o
    rw [(hb s a pending).1 hp, Option.bind_some]
    exact (cleanup_fn hd drops fds hdrops pending o).1 hc
  · intro h
    cases hf : f s a with
    | none => simp [Owned.scopeF, hf] at h
    | some pending =>
      simp only [Owned.scopeF, hf, Option.bind_some] at h
      exact ⟨pending, (hb s a pending).2 hf, (cleanup_fn hd drops fds hdrops pending o).2 h⟩

/-- `AllocatedSeeds.bindResult`, computed: only `Ok` reaches `g`. -/
def AllocatedSeeds.bindResultF (f : S → Unit → Option (Outcome S (Except Token.Error V) U T))
    (g : V → S → Unit → Option (Outcome S (Except Token.Error W) U T)) :
    S → Unit → Option (Outcome S (Except Token.Error W) U T) :=
  fun s a => (f s a).bind (thenOpt · fun result after =>
    match result with
    | .ok v => g v after ()
    | .error e => some (.returned (.error e) after))

/-- `AllocatedSeeds.bindResult first next` admits exactly
`AllocatedSeeds.bindResultF f g`. -/
theorem AllocatedSeeds.bindResult_fn {first : Callback.Run S Unit (Except Token.Error V) U T}
    {f : S → Unit → Option (Outcome S (Except Token.Error V) U T)} (hf : Fn first f)
    {next : V → Callback.Run S Unit (Except Token.Error W) U T}
    {g : V → S → Unit → Option (Outcome S (Except Token.Error W) U T)}
    (hg : ∀ v, Fn (next v) (g v)) :
    Fn (AllocatedSeeds.bindResult first next) (AllocatedSeeds.bindResultF f g) := by
  refine bind_fn hf fun result after o => ?_
  cases result with
  | ok v => exact hg v after () o
  | error e => exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩

/-- `AccountInfoRc.lift`, computed: an Rc dependency has no unwind exit. -/
def AccountInfoRc.liftF (f : S → A → Option (Outcome S V Empty T)) :
    S → A → Option (Outcome S V U T) :=
  fun s a => (f s a).map Solanalib.Specs.Core.AccountInfoRc.liftOutcome

/-- `AccountInfoRc.lift run` admits exactly `AccountInfoRc.liftF f`. -/
theorem AccountInfoRc.lift_fn {run : Callback.Run S A V Empty T}
    {f : S → A → Option (Outcome S V Empty T)} (hr : Fn run f) :
    Fn (Solanalib.Specs.Core.AccountInfoRc.lift (Unwind := U) run) (AccountInfoRc.liftF f) := by
  intro s a o
  constructor
  · rintro ⟨i, hi, rfl⟩
    show (f s a).map _ = _
    rw [(hr s a i).1 hi]; rfl
  · intro e
    cases hf : f s a with
    | none => simp [AccountInfoRc.liftF, hf] at e
    | some i =>
      simp only [AccountInfoRc.liftF, hf, Option.map_some, Option.some.injEq] at e
      exact ⟨i, (hr s a i).2 hf, e⟩

/-- Run `step` on each element of a list in order, threading the actual state
and discarding each returned value. An unwind or a terminal exit stops the
iteration. -/
def forEach (step : Callback.Run S A W U T) : List A → Callback.Run S Unit Unit U T
  | [] => fun s _ o => o = .returned () s
  | a :: rest =>
    Callback.bind (fun s (_ : Unit) => step s a) (fun _ s o => forEach step rest s () o)

/-- `forEach`, computed. -/
def forEachF (stepF : S → A → Option (Outcome S W U T)) :
    List A → S → Unit → Option (Outcome S Unit U T)
  | [], s, _ => some (.returned () s)
  | a :: rest, s, _ => (stepF s a).bind (thenOpt · fun _ st => forEachF stepF rest st ())

/-- `forEach step l` admits exactly `forEachF stepF l`. -/
theorem forEach_fn {step : Callback.Run S A W U T} {stepF : S → A → Option (Outcome S W U T)}
    (hs : Fn step stepF) : ∀ l, Fn (forEach step l) (forEachF stepF l)
  | [] => fun s _ _ => ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩
  | a :: rest => fun s u o =>
    bind_fn (fun s _ o => hs s a o) (fun _ st o => forEach_fn hs rest st () o) s u o

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
