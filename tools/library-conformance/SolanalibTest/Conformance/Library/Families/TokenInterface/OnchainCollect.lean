/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc
import Solanalib.Specs.Core.TokenRequestAllocatedCollectProtocol

/-!
# Collection, seed resolution and the extra-account chain, computed

Component (7b) of the computed Token-2022 onchain model.

* **Collection.** `collect_fn` computes the reference interpretation
  `AllocatedCollect.protocolProvider protocol` of a collection protocol with no
  internal chunks and the default partial-cleanup order. A protocol trace is
  then determined by its callback outcomes, so `Trace` is computed by
  `traceF`, by recursion on `iterator.length - index`. `collect_fn` has the
  form of `DepPrims.collect_fn`, and `collectDepPrims` builds a `DepPrims`
  bundle from it.
* **Seed resolution.** `resolve_fn` computes `AllocatedSeeds.resolve` over any
  seed vector bundles: `unpackFromF` and `pushViewsFromF` mirror the
  well-founded recursions of `unpackFrom` and `pushViewsFrom`. No property of
  the seed vectors is assumed. At an index whose seed vectors are empty-only
  (`push` admits nothing), a PDA extra with a seed computes `none`.
* **Extra accounts.** `collectRefs_fn`, `resolveExtra_fn`, `appendResolved_fn`,
  `addExtraEntries_fn` and `addExtraList_fn`, over any `P : Prims types` and
  `D : DepPrims types deps`. `addExtraList_fn` takes the computed TLV validator
  and `extraSlice` of component (7a) as hypotheses.

`guardObservations` and `ExtraSlice.entryAt` are functions of the state, so
the computed forms use them directly.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainCollect

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc

/-! ## Helpers -/

/-- An equation with a fixed outcome, computed. -/
private theorem ret_iff {X : Type} {o v : X} : o = v ↔ some v = some o :=
  ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩

/-- No computed value: no outcome. -/
private theorem none_iff {X : Type} {o : X} : False ↔ (none : Option X) = some o :=
  ⟨False.elim, fun h => by cases h⟩

/-! ## Collection -/

section Collect

open AllocatedCollect

variable {Extra Resource U T : Type}

/-- Computed partial-cleanup drops of a protocol with the default order: the
acquired guards in order, then the in-progress storage retirement. -/
def partialDropsF
    (retireF : Option Resource → List Element →
      World Extra → Option (Outcome (World Extra) Unit U T))
    (acquired : List Element) : List (World Extra → Option (Outcome (World Extra) Unit U T)) :=
  acquired.map (fun element => DataRef.dropF element.2) ++ [retireF none acquired]

/-- `Protocol.cleanup`, computed, for the default order. -/
def protocolCleanupF {V : Type} (dbl : World Extra → U → U → T)
    (retireF : Option Resource → List Element →
      World Extra → Option (Outcome (World Extra) Unit U T))
    (acquired : List Element) (pending : Outcome (World Extra) V U T) :
    Option (Outcome (World Extra) V U T) :=
  match pending with
  | .terminated reason => some (.terminated reason)
  | .returned v before => cleanupF dbl (partialDropsF retireF acquired) (.returned v before)
  | .unwound reason before => cleanupF dbl (partialDropsF retireF acquired) (.unwound reason before)

/-- `Protocol.finishExit`, computed. -/
def finishExitF (dbl : World Extra → U → U → T)
    (retireF : Option Resource → List Element →
      World Extra → Option (Outcome (World Extra) Unit U T))
    (acquired : List Element) (pending : Outcome (World Extra) Resource U T) :
    Option (Outcome (World Extra) (Except Token.Error Resource) U T) :=
  match pending with
  | .returned resource after => some (.returned (.ok resource) after)
  | .unwound reason after => protocolCleanupF dbl retireF acquired (.unwound reason after)
  | .terminated reason => some (.terminated reason)

/-- The protocol trace, computed from the next callback index, the acquired
prefix and the actual state. Before the end of the iterator, the element read
and the callback outcome decide the step; at the end, `finish` runs. There is
no internal chunk. An index past the end has no trace. -/
def traceF
    (finishF : World Extra → List Element → Option (Outcome (World Extra) Resource U T))
    (retireF : Option Resource → List Element →
      World Extra → Option (Outcome (World Extra) Unit U T))
    (dbl : World Extra → U → U → T) (iterator : Iterator Extra)
    (callbackF : World Extra → AccountInfo.Value →
      Option (Outcome (World Extra) (Except Token.Error Element) U T))
    (index : Nat) (acquired : List Element) (before : World Extra) :
    Option (Outcome (World Extra) (Except Token.Error Resource) U T) :=
  if _within : index < iterator.length then
    (iterator.elementAt before index).bind fun info =>
    (callbackF before info).bind fun called =>
      match called with
      | .returned (.ok element) after =>
        traceF finishF retireF dbl iterator callbackF (index + 1) (acquired ++ [element]) after
      | .returned (.error error) after =>
        protocolCleanupF dbl retireF acquired (.returned (.error error) after)
      | .unwound reason after => protocolCleanupF dbl retireF acquired (.unwound reason after)
      | .terminated reason => some (.terminated reason)
  else if index = iterator.length then
    (finishF before acquired).bind (finishExitF dbl retireF acquired)
  else none
termination_by iterator.length - index

/-- The reference collection, computed: the trace from index 0 and no
acquired element. -/
def collectF
    (finishF : World Extra → List Element → Option (Outcome (World Extra) Resource U T))
    (retireF : Option Resource → List Element →
      World Extra → Option (Outcome (World Extra) Unit U T))
    (dbl : World Extra → U → U → T) (iterator : Iterator Extra)
    (callbackF : World Extra → AccountInfo.Value →
      Option (Outcome (World Extra) (Except Token.Error Element) U T)) :
    RRun (World Extra) Resource U T :=
  traceF finishF retireF dbl iterator callbackF 0 []

variable {protocol : Protocol Extra Resource U T}
  {finishF : World Extra → List Element → Option (Outcome (World Extra) Resource U T)}
  {retireF : Option Resource → List Element →
    World Extra → Option (Outcome (World Extra) Unit U T)}
  {dbl : World Extra → U → U → T}

/-- `Protocol.cleanup` admits exactly `protocolCleanupF` for the default order. -/
theorem protocolCleanup_fn {V : Type}
    (hret : ∀ resource acquired,
      DFn (protocol.retire resource acquired) (retireF resource acquired))
    (hd : ∀ s o l t, protocol.double s o l t ↔ t = dbl s o l)
    (hord : ∀ before acquired, protocol.partialOrder before acquired = acquired)
    (acquired : List Element) (pending final : Outcome (World Extra) V U T) :
    protocol.cleanup acquired pending final ↔
      protocolCleanupF dbl retireF acquired pending = some final := by
  have hdrops : All2 DFn (acquired.map (fun element => element.2.drop) ++
      [protocol.retire none acquired]) (partialDropsF retireF acquired) :=
    All2.append (All2.map _ _ (fun element => DataRef.drop_fn element.2) acquired)
      (.cons (hret none acquired) .nil)
  cases pending with
  | returned v before =>
    show (protocol.partialOrder before acquired).Perm acquired ∧
      Owned.cleanup protocol.double (protocol.partialDrops before acquired) _ final ↔ _
    unfold Protocol.partialDrops
    rw [hord]
    exact (and_iff_right (List.Perm.refl acquired)).trans (cleanup_fn hd _ _ hdrops _ final)
  | unwound reason before =>
    show (protocol.partialOrder before acquired).Perm acquired ∧
      Owned.cleanup protocol.double (protocol.partialDrops before acquired) _ final ↔ _
    unfold Protocol.partialDrops
    rw [hord]
    exact (and_iff_right (List.Perm.refl acquired)).trans (cleanup_fn hd _ _ hdrops _ final)
  | terminated reason => exact ret_iff

/-- `Protocol.finishExit` admits exactly `finishExitF` for the default order. -/
theorem finishExit_fn
    (hret : ∀ resource acquired,
      DFn (protocol.retire resource acquired) (retireF resource acquired))
    (hd : ∀ s o l t, protocol.double s o l t ↔ t = dbl s o l)
    (hord : ∀ before acquired, protocol.partialOrder before acquired = acquired)
    (acquired : List Element) (pending : Outcome (World Extra) Resource U T)
    (final : Outcome (World Extra) (Except Token.Error Resource) U T) :
    protocol.finishExit acquired pending final ↔
      finishExitF dbl retireF acquired pending = some final := by
  cases pending with
  | returned resource after => exact ret_iff
  | unwound reason after =>
    exact protocolCleanup_fn (V := Except Token.Error Resource) hret hd hord acquired
      (.unwound reason after) final
  | terminated reason => exact ret_iff

/-- Every trace with no internal chunk ends in the outcome computed by `traceF`. -/
theorem trace_sound
    (hint : ∀ index acquired before outcome, ¬ protocol.internal index acquired before outcome)
    (hfin : Fn protocol.finish finishF)
    (hret : ∀ resource acquired,
      DFn (protocol.retire resource acquired) (retireF resource acquired))
    (hd : ∀ s o l t, protocol.double s o l t ↔ t = dbl s o l)
    (hord : ∀ before acquired, protocol.partialOrder before acquired = acquired)
    {iterator : Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Token.Error Element) U T}
    {callbackF : World Extra → AccountInfo.Value →
      Option (Outcome (World Extra) (Except Token.Error Element) U T)}
    (hcb : Fn callback callbackF) {index : Nat} {acquired : List Element} {before : World Extra}
    {calls : List Nat} {final : Outcome (World Extra) (Except Token.Error Resource) U T}
    (trace : Trace protocol iterator callback index acquired before calls final) :
    traceF finishF retireF dbl iterator callbackF index acquired before = some final := by
  induction trace with
  | done endOfIterator finished exit =>
    rw [traceF, dite_eq_right (by omega), ite_eq_left endOfIterator, (hfin _ _ _).1 finished,
      Option.bind_some]
    exact (finishExit_fn hret hd hord _ _ _).1 exit
  | next within read called _ induction =>
    rw [traceF, dite_eq_left within, read, Option.bind_some, (hcb _ _ _).1 called, Option.bind_some]
    exact induction
  | error within read called cleaned =>
    rw [traceF, dite_eq_left within, read, Option.bind_some, (hcb _ _ _).1 called, Option.bind_some]
    exact (protocolCleanup_fn hret hd hord _ _ _).1 cleaned
  | unwind within read called cleaned =>
    rw [traceF, dite_eq_left within, read, Option.bind_some, (hcb _ _ _).1 called, Option.bind_some]
    exact (protocolCleanup_fn hret hd hord _ _ _).1 cleaned
  | terminal within read called =>
    rw [traceF, dite_eq_left within, read, Option.bind_some, (hcb _ _ _).1 called, Option.bind_some]
  | internalReturn _ stepped => exact (hint _ _ _ _ stepped).elim
  | internalUnwind _ stepped => exact (hint _ _ _ _ stepped).elim
  | internalTerminal _ stepped => exact (hint _ _ _ _ stepped).elim

/-- Every outcome computed by `traceF` ends a trace, with some callback list. -/
theorem trace_complete
    (hfin : Fn protocol.finish finishF)
    (hret : ∀ resource acquired,
      DFn (protocol.retire resource acquired) (retireF resource acquired))
    (hd : ∀ s o l t, protocol.double s o l t ↔ t = dbl s o l)
    (hord : ∀ before acquired, protocol.partialOrder before acquired = acquired)
    (iterator : Iterator Extra)
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Token.Error Element) U T}
    {callbackF : World Extra → AccountInfo.Value →
      Option (Outcome (World Extra) (Except Token.Error Element) U T)}
    (hcb : Fn callback callbackF) (index : Nat) (acquired : List Element) (before : World Extra)
    (final : Outcome (World Extra) (Except Token.Error Resource) U T)
    (h : traceF finishF retireF dbl iterator callbackF index acquired before = some final) :
    ∃ calls, Trace protocol iterator callback index acquired before calls final := by
  rw [traceF] at h
  by_cases within : index < iterator.length
  · rw [dite_eq_left within] at h
    cases hread : iterator.elementAt before index with
    | none => rw [hread] at h; cases h
    | some info =>
      rw [hread, Option.bind_some] at h
      cases hcall : callbackF before info with
      | none => rw [hcall] at h; cases h
      | some called =>
        rw [hcall, Option.bind_some] at h
        have hc := (hcb before info called).2 hcall
        cases called with
        | returned x after =>
          cases x with
          | ok element =>
            obtain ⟨calls, tail⟩ :=
              trace_complete hfin hret hd hord iterator hcb (index + 1) _ _ final h
            exact ⟨_, .next within hread hc tail⟩
          | error error =>
            exact ⟨_, .error within hread hc ((protocolCleanup_fn hret hd hord _ _ final).2 h)⟩
        | unwound reason after =>
          exact ⟨_, .unwind within hread hc ((protocolCleanup_fn hret hd hord _ _ final).2 h)⟩
        | terminated reason =>
          cases h
          exact ⟨_, .terminal within hread hc⟩
  · rw [dite_eq_right within] at h
    by_cases atEnd : index = iterator.length
    · rw [ite_eq_left atEnd] at h
      cases hf : finishF before acquired with
      | none => rw [hf] at h; cases h
      | some pending =>
        rw [hf, Option.bind_some] at h
        exact ⟨[], .done atEnd ((hfin _ _ _).2 hf) ((finishExit_fn hret hd hord _ _ final).2 h)⟩
    · rw [ite_eq_right atEnd] at h
      cases h
termination_by iterator.length - index

/-- **The generic collection lemma.** The reference interpretation of a
collection protocol with no internal chunk (`internal` admits nothing), a
computed `finish`, computed storage retirements, a functional double-unwind
policy and the default partial-cleanup order admits exactly `collectF`, for
every callback computed by a function. This is the form of
`DepPrims.collect_fn`. -/
theorem collect_fn
    (hint : ∀ index acquired before outcome, ¬ protocol.internal index acquired before outcome)
    (hfin : Fn protocol.finish finishF)
    (hret : ∀ resource acquired,
      DFn (protocol.retire resource acquired) (retireF resource acquired))
    (hd : ∀ s o l t, protocol.double s o l t ↔ t = dbl s o l)
    (hord : ∀ before acquired, protocol.partialOrder before acquired = acquired) :
    ∀ iterator callback callbackF, Fn callback callbackF →
      RFn ((protocolProvider protocol).run iterator callback)
        (collectF finishF retireF dbl iterator callbackF) :=
  fun iterator _ _ hcb s o =>
    ⟨fun ⟨_, trace⟩ => trace_sound hint hfin hret hd hord hcb trace,
      trace_complete hfin hret hd hord iterator hcb 0 [] s o⟩

end Collect

/-! ## Seed resolution -/

section Seeds

open AllocatedSeeds

variable {S BR SR RR U T : Type} {ops : AllocatedSeeds.Ops S BR SR RR U T}

/-- Both branches of a model `if` between callbacks are computed by the same `if`. -/
private theorem ite_fn {A V : Type} (c : Prop) [Decidable c] {r₁ r₂ : Callback.Run S A V U T}
    {f₁ f₂ : S → A → Option (Outcome S V U T)} (h₁ : c → Fn r₁ f₁) (h₂ : ¬c → Fn r₂ f₂) :
    Fn (if c then r₁ else r₂) (if c then f₁ else f₂) := by
  by_cases hc : c
  · rw [ite_eq_left hc, ite_eq_left hc]; exact h₁ hc
  · rw [ite_eq_right hc, ite_eq_right hc]; exact h₂ hc

/-- `returnedResult`, computed. -/
def returnedResultF {V : Type} (value : Except Token.Error V) :
    S → Unit → Option (Outcome S (Except Token.Error V) U T) :=
  fun s _ => some (.returned value s)

/-- `returnedResult value` admits exactly `returnedResultF value`. -/
theorem returnedResult_fn {V : Type} (value : Except Token.Error V) :
    Fn (returnedResult (State := S) (Unwind := U) (Terminal := T) value) (returnedResultF value) :=
  fun _ _ _ => ret_iff

/-- `unpackOne`, computed from the literal byte-vector constructor. -/
def unpackOneF (fromListF : S → List UInt8 → Option (Outcome S BR U T)) (input : Bytes) :
    S → Unit → Option (Outcome S (Except Token.Error (Seed BR)) U T) :=
  match input with
  | [] => returnedResultF (.error .InvalidAccountData)
  | tag :: rest =>
    if tag = 0 then returnedResultF (.ok .uninitialized)
    else if tag = 1 then
      match rest with
      | [] => returnedResultF (.error Hook.invalidSeedBytes)
      | length :: payload =>
        if payload.length < length.toNat then returnedResultF (.error Hook.invalidSeedBytes)
        else fun s _ => (fromListF s (payload.take length.toNat)).map
          (Outcome.map fun resource => Except.ok (.literal resource))
    else if tag = 2 then
      match rest with
      | offset :: length :: _ => returnedResultF (.ok (.instructionData offset length))
      | _ => returnedResultF (.error Hook.invalidSeedBytes)
    else if tag = 3 then
      match rest with
      | index :: _ => returnedResultF (.ok (.accountKey index))
      | _ => returnedResultF (.error Hook.invalidSeedBytes)
    else if tag = 4 then
      match rest with
      | index :: offset :: length :: _ => returnedResultF (.ok (.accountData index offset length))
      | _ => returnedResultF (.error Hook.invalidSeedBytes)
    else returnedResultF (.error .InvalidAccountData)

/-- `unpackOne bytes input` admits exactly `unpackOneF fromListF input`. -/
theorem unpackOne_fn {bytes : Owned.VectorOps S UInt8 BR U T}
    {fromListF : S → List UInt8 → Option (Outcome S BR U T)} (hb : Fn bytes.fromList fromListF) :
    ∀ input, Fn (unpackOne bytes input) (unpackOneF fromListF input)
  | [] => returnedResult_fn _
  | tag :: rest => by
    unfold unpackOne unpackOneF
    refine ite_fn _ (fun _ => returnedResult_fn _) fun _ => ite_fn _ (fun _ => ?_) fun _ =>
      ite_fn _ (fun _ => ?_) fun _ => ite_fn _ (fun _ => ?_) fun _ =>
      ite_fn _ (fun _ => ?_) fun _ => returnedResult_fn _
    · match rest with
      | [] => exact returnedResult_fn _
      | length :: payload =>
        exact ite_fn _ (fun _ => returnedResult_fn _) fun _ =>
          map_fn (fun s _ o => hb s (payload.take length.toNat) o) _
    · match rest with
      | [] => exact returnedResult_fn _
      | [_] => exact returnedResult_fn _
      | _ :: _ :: _ => exact returnedResult_fn _
    · match rest with
      | [] => exact returnedResult_fn _
      | _ :: _ => exact returnedResult_fn _
    · match rest with
      | [] => exact returnedResult_fn _
      | [_] => exact returnedResult_fn _
      | [_, _] => exact returnedResult_fn _
      | _ :: _ :: _ :: _ => exact returnedResult_fn _

/-- `unpackFrom`, computed by the same recursion on `32 - offset`: decode one
seed at the current offset in the actual state, then push it and continue
after its width. -/
def unpackFromF (hb : VecPrims ops.bytes) (hs : VecPrims ops.seeds)
    (configurationAt : S → Option Solanalib.Runtime.Pubkey) (resource : SR) (offset : Nat) (before
      : S) :
    Option (Outcome S (Except Token.Error Unit) U T) :=
  if _within : offset < 32 then
    (configurationAt before).bind fun configuration =>
    (unpackOneF hb.fromListF (configuration.bytes.drop offset) before ()).bind fun decoded =>
      match decoded with
      | .returned (.error error) after => some (.returned (.error error) after)
      | .returned (.ok seed) after =>
        (widthAt ops.bytes after seed).bind fun width =>
          match seed with
          | .uninitialized => some (.returned (.ok ()) after)
          | _ =>
            if _positive : 0 < width then
              (hs.pushF after (resource, seed)).bind (thenOpt · fun _ state =>
                unpackFromF hb hs configurationAt resource (offset + width) state)
            else none
      | .unwound reason after => some (.unwound reason after)
      | .terminated reason => some (.terminated reason)
  else some (.returned (.ok ()) before)
termination_by 32 - offset

/-- `unpackFrom ops configurationAt resource offset` admits exactly
`unpackFromF hb hs configurationAt resource offset`. -/
theorem unpackFrom_fn (hb : VecPrims ops.bytes) (hs : VecPrims ops.seeds)
    (configurationAt : S → Option Solanalib.Runtime.Pubkey) (resource : SR) (offset : Nat) (before
      : S)
    (outcome : Outcome S (Except Token.Error Unit) U T) :
    unpackFrom ops configurationAt resource offset before outcome ↔
      unpackFromF hb hs configurationAt resource offset before = some outcome := by
  rw [unpackFrom, unpackFromF]
  by_cases within : offset < 32
  · rw [ite_eq_left within, dite_eq_left within]
    refine exists_bind_iff' (fun _ => Iff.rfl) fun configuration =>
      exists_bind_iff' (fun decoded => unpackOne_fn hb.fromList_fn _ before () decoded)
        fun decoded => ?_
    cases decoded with
    | returned x after =>
      cases x with
      | error error => exact ret_iff
      | ok seed =>
        refine exists_bind_iff' (fun _ => Iff.rfl) fun width => ?_
        have step : ¬seed = .uninitialized →
            ((if _positive : 0 < width then
              Callback.bind (fun state (_ : Unit) => ops.seeds.push state (resource, seed))
                (fun _ state result => unpackFrom ops configurationAt resource
                  (offset + width) state result) after () outcome
            else False) ↔
            (if _positive : 0 < width then
              (hs.pushF after (resource, seed)).bind (thenOpt · fun _ state =>
                unpackFromF hb hs configurationAt resource (offset + width) state)
            else none) = some outcome) := by
          intro _
          by_cases positive : 0 < width
          · rw [dite_eq_left positive, dite_eq_left positive]
            exact bind_fn (fun s _ o => hs.push_fn s (resource, seed) o)
              (fun _ state o => unpackFrom_fn hb hs configurationAt resource (offset + width)
                state o) after () outcome
          · rw [dite_eq_right positive, dite_eq_right positive]
            exact none_iff
        cases seed with
        | uninitialized => exact ret_iff
        | literal r => exact step (by intro h; cases h)
        | instructionData o l => exact step (by intro h; cases h)
        | accountKey i => exact step (by intro h; cases h)
        | accountData i o l => exact step (by intro h; cases h)
    | unwound reason after => exact ret_iff
    | terminated reason => exact ret_iff
  · rw [ite_eq_right within, dite_eq_right within]
    exact ret_iff
termination_by 32 - offset

/-- `unpack`, computed: allocate the empty seed vector, unpack from offset 0,
and move the vector out on `Ok`; otherwise drop it. -/
def unpackF (hb : VecPrims ops.bytes) (hs : VecPrims ops.seeds) (dbl : S → U → U → T)
    (configurationAt : S → Option Solanalib.Runtime.Pubkey) :
    S → Unit → Option (Outcome S (Except Token.Error SR) U T) :=
  fun before _ =>
    (configurationAt before).bind fun _ =>
    (unpackFromF hb hs configurationAt (ops.seeds.empty before).1 0
      (ops.seeds.empty before).2).bind fun pending =>
      match Outcome.map (fun (result : Except Token.Error Unit) =>
          result.map (fun _ => (ops.seeds.empty before).1)) pending with
      | .returned (.ok resource) after => some (.returned (.ok resource) after)
      | moved => cleanupF dbl [hs.dropActionF (ops.seeds.empty before).1] moved

/-- `unpack ops double configurationAt` admits exactly `unpackF hb hs dbl configurationAt`. -/
theorem unpack_fn (hb : VecPrims ops.bytes) (hs : VecPrims ops.seeds)
    {double : Owned.DoubleUnwind S U T} {dbl : S → U → U → T}
    (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l) (configurationAt : S → Option
      Solanalib.Runtime.Pubkey) :
    Fn (unpack ops double configurationAt) (unpackF hb hs dbl configurationAt) := by
  intro before _ outcome
  refine exists_bind_iff' (fun _ => Iff.rfl) fun _ =>
    exists_bind_iff' (fun pending => unpackFrom_fn hb hs configurationAt _ 0 _ pending)
      fun pending => ?_
  have hc := cleanup_fn (V := Except Token.Error SR) hd _ _
    (.cons (hs.dropAction_fn (ops.seeds.empty before).1) .nil)
  cases pending with
  | returned x after =>
    cases x with
    | ok u => exact ret_iff
    | error error => exact hc _ outcome
  | unwound reason after => exact hc _ outcome
  | terminated reason => exact hc _ outcome

/-- `seedView`, computed: the borrowed view of one unpacked seed, or its
source error. -/
def seedViewF (args : Args S) (instruction : BytesView S) (seed : Seed BR) :
    S → Unit → Option (Outcome S (Except Token.Error (Option (BytesView S))) U T) :=
  fun before _ =>
    match seed with
    | .uninitialized => some (.returned (.ok none) before)
    | .literal resource =>
      (ops.bytes.current before resource).bind fun bytes =>
        some (.returned (.ok (some ⟨bytes.length, fun state => ops.bytes.current state resource⟩))
          before)
    | .instructionData offset length =>
      (instruction.observe before).bind fun _ =>
        if instruction.length < offset.toNat + length.toNat then
          some (.returned (.error Hook.instructionDataTooSmall) before)
        else some (.returned (.ok (some (instruction.slice offset.toNat length.toNat))) before)
    | .accountKey index =>
      (args.accountsAt before).bind fun accounts =>
        match accounts[index.toNat]? with
        | none => some (.returned (.error Hook.accountNotFound) before)
        | some _ => some (.returned (.ok (some
            ⟨32, fun state => (accountKeyAt args index.toNat state).map (·.bytes)⟩)) before)
    | .accountData index offset length =>
      (args.accountsAt before).bind fun accounts =>
        match accounts[index.toNat]? with
        | none => some (.returned (.error Hook.accountNotFound) before)
        | some (_, none) => some (.returned (.error Hook.accountDataNotFound) before)
        | some (_, some bytes) =>
          if bytes.length < offset.toNat + length.toNat then
            some (.returned (.error Hook.accountDataTooSmall) before)
          else
            let parent : BytesView S := ⟨bytes.length, accountDataAt args index.toNat⟩
            some (.returned (.ok (some (parent.slice offset.toNat length.toNat))) before)

/-- `seedView ops args instruction seed` admits exactly `seedViewF args instruction seed`. -/
theorem seedView_fn (args : Args S) (instruction : BytesView S) (seed : Seed BR) :
    Fn (seedView ops args instruction seed) (seedViewF (ops := ops) args instruction seed) := by
  intro before _ outcome
  cases seed with
  | uninitialized => exact ret_iff
  | literal resource => exact exists_bind_iff' (fun _ => Iff.rfl) fun _ => ret_iff
  | instructionData offset length =>
    refine exists_bind_iff' (fun _ => Iff.rfl) fun _ => ?_
    by_cases small : instruction.length < offset.toNat + length.toNat
    · rw [ite_eq_left small, ite_eq_left small]; exact ret_iff
    · rw [ite_eq_right small, ite_eq_right small]; exact ret_iff
  | accountKey index =>
    refine exists_bind_iff' (fun _ => Iff.rfl) fun accounts => ?_
    cases accounts[index.toNat]? with
    | none => exact ret_iff
    | some _ => exact ret_iff
  | accountData index offset length =>
    refine exists_bind_iff' (fun _ => Iff.rfl) fun accounts => ?_
    cases accounts[index.toNat]? with
    | none => exact ret_iff
    | some account =>
      obtain ⟨key, data⟩ := account
      cases data with
      | none => exact ret_iff
      | some bytes =>
        by_cases small : bytes.length < offset.toNat + length.toNat
        · simp only [small, ↓reduceIte]; exact ret_iff
        · simp only [small, ↓reduceIte]; exact ret_iff

/-- `pushViewsFrom`, computed by the same recursion on `seedCount - index`:
view the seed at `index` in the actual state and push a present view. -/
def pushViewsFromF (hr : VecPrims ops.refs) (args : Args S) (instruction : BytesView S)
    (seeds : SR) (references : RR) (seedCount index : Nat) (before : S) :
    Option (Outcome S (Except Token.Error Unit) U T) :=
  if _within : index < seedCount then
    (ops.seeds.current before seeds).bind fun current =>
      if current.length = seedCount then
        current[index]?.bind fun seed =>
          AllocatedSeeds.bindResultF (seedViewF (ops := ops) args instruction seed)
            (fun view state _ =>
              match view with
              | none =>
                pushViewsFromF hr args instruction seeds references seedCount (index + 1) state
              | some borrowed =>
                (hr.pushF state (references, borrowed)).bind (thenOpt · fun _ after =>
                  pushViewsFromF hr args instruction seeds references seedCount (index + 1) after))
            before ()
      else none
  else some (.returned (.ok ()) before)
termination_by seedCount - index

/-- `pushViewsFrom ops args instruction seeds references seedCount index`
admits exactly `pushViewsFromF hr args instruction seeds references seedCount index`. -/
theorem pushViewsFrom_fn (hr : VecPrims ops.refs) (args : Args S) (instruction : BytesView S)
    (seeds : SR) (references : RR) (seedCount index : Nat) (before : S)
    (outcome : Outcome S (Except Token.Error Unit) U T) :
    pushViewsFrom ops args instruction seeds references seedCount index before outcome ↔
      pushViewsFromF hr args instruction seeds references seedCount index before =
        some outcome := by
  rw [pushViewsFrom, pushViewsFromF]
  by_cases within : index < seedCount
  · rw [ite_eq_left within, dite_eq_left within]
    refine exists_bind_iff' (fun _ => Iff.rfl) fun current => ?_
    by_cases sized : current.length = seedCount
    · rw [ite_eq_left sized, and_iff_right sized]
      refine exists_bind_iff' (fun _ => Iff.rfl) fun seed => ?_
      refine AllocatedSeeds.bindResult_fn (seedView_fn args instruction seed)
        (fun view state _ o => ?_) before () outcome
      cases view with
      | none =>
        exact pushViewsFrom_fn hr args instruction seeds references seedCount (index + 1) state o
      | some borrowed =>
        exact bind_fn (fun s _ o => hr.push_fn s (references, borrowed) o)
          (fun _ after o => pushViewsFrom_fn hr args instruction seeds references seedCount
            (index + 1) after o) state () o
    · rw [ite_eq_right sized]
      exact ⟨fun h => absurd h.1 sized, fun h => by cases h⟩
  · rw [ite_eq_right within, dite_eq_right within]
    exact ret_iff
termination_by seedCount - index

/-- `searchPda`, computed from the computed address-library dependency. -/
def searchPdaF
    (findF : S → Address.Syscall.PdaInputs → Option (Outcome S (Solanalib.Runtime.Pubkey × UInt8) U
      T))
    (programAt : S → Option Solanalib.Runtime.Pubkey) (references : RR) :
    S → Unit → Option (Outcome S (Except Token.Error Solanalib.Runtime.Pubkey) U T) :=
  fun before _ =>
    (ops.refs.current before references).bind fun views =>
    (readViews before views).bind fun values =>
    (programAt before).bind fun program =>
      (findF before ⟨values, program⟩).map (Outcome.map fun value => Except.ok value.1)

/-- `searchPda ops find programAt references` admits exactly
`searchPdaF findF programAt references`. -/
theorem searchPda_fn {find : FindPda S U T}
    {findF : S → Address.Syscall.PdaInputs → Option (Outcome S (Solanalib.Runtime.Pubkey × UInt8) U
      T)}
    (hfind : Fn find findF) (programAt : S → Option Solanalib.Runtime.Pubkey) (references : RR) :
    Fn (searchPda ops find programAt references)
      (searchPdaF (ops := ops) findF programAt references) := by
  intro before _ outcome
  have hcall := fun values program =>
    map_fn hfind (fun (value : Solanalib.Runtime.Pubkey × UInt8) => (Except.ok value.1 : Except
      Token.Error _))
      before ⟨values, program⟩ outcome
  constructor
  · rintro ⟨views, values, program, hv, hval, hp, hm⟩
    exact (exists_bind_iff' (fun _ => Iff.rfl) fun views => exists_bind_iff' (fun _ => Iff.rfl)
      fun values => exists_bind_iff' (fun _ => Iff.rfl) fun program => hcall values program).1
      ⟨views, hv, values, hval, program, hp, hm⟩
  · intro h
    obtain ⟨views, hv, values, hval, program, hp, hm⟩ :=
      (exists_bind_iff' (fun _ => Iff.rfl) fun views => exists_bind_iff' (fun _ => Iff.rfl)
        fun values => exists_bind_iff' (fun _ => Iff.rfl) fun program => hcall values program).2 h
    exact ⟨views, values, program, hv, hval, hp, hm⟩

/-- `resolvePda`, computed: allocate the reference vector, push the seed views,
search, and drop the reference vector on every non-terminal exit. -/
def resolvePdaF (hr : VecPrims ops.refs) (dbl : S → U → U → T)
    (findF : S → Address.Syscall.PdaInputs → Option (Outcome S (Solanalib.Runtime.Pubkey × UInt8) U
      T))
    (args : Args S) (instruction : BytesView S) (programAt : S → Option Solanalib.Runtime.Pubkey)
    (seeds : SR) : S → Unit → Option (Outcome S (Except Token.Error Solanalib.Runtime.Pubkey) U T)
      :=
  fun before _ =>
    (ops.seeds.current before seeds).bind fun current =>
      Owned.scopeF dbl [hr.dropActionF (ops.refs.empty before).1]
        (AllocatedSeeds.bindResultF
          (fun state _ => pushViewsFromF hr args instruction seeds (ops.refs.empty before).1
            current.length 0 state)
          (fun _ => searchPdaF (ops := ops) findF programAt (ops.refs.empty before).1))
        (ops.refs.empty before).2 ()

/-- `resolvePda ops double find args instruction programAt seeds` admits exactly
`resolvePdaF hr dbl findF args instruction programAt seeds`. -/
theorem resolvePda_fn (hr : VecPrims ops.refs) {double : Owned.DoubleUnwind S U T}
    {dbl : S → U → U → T} (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l) {find : FindPda S U T}
    {findF : S → Address.Syscall.PdaInputs → Option (Outcome S (Solanalib.Runtime.Pubkey × UInt8) U
      T)}
    (hfind : Fn find findF) (args : Args S) (instruction : BytesView S)
    (programAt : S → Option Solanalib.Runtime.Pubkey) (seeds : SR) :
    Fn (resolvePda ops double find args instruction programAt seeds)
      (resolvePdaF hr dbl findF args instruction programAt seeds) := by
  intro before _ outcome
  refine exists_bind_iff' (fun _ => Iff.rfl) fun current => ?_
  exact Owned.scope_fn hd (.cons (hr.dropAction_fn (ops.refs.empty before).1) .nil)
    (AllocatedSeeds.bindResult_fn
      (fun state _ o => pushViewsFrom_fn hr args instruction seeds (ops.refs.empty before).1
        current.length 0 state o)
      (fun _ => searchPda_fn hfind programAt (ops.refs.empty before).1))
    (ops.refs.empty before).2 () outcome

/-- `finishMeta`, computed: the flags read after the PDA search. -/
def finishMetaF (args : Args S) (key : Solanalib.Runtime.Pubkey) :
    S → Unit → Option (Outcome S (Except Token.Error Solanalib.Runtime.CpiMeta) U T) :=
  fun before _ => (args.extraAt before).bind fun extra =>
    some (.returned (.ok (Instruction.accountMeta key extra.isSigner extra.isWritable)) before)

/-- `finishMeta args key` admits exactly `finishMetaF args key`. -/
theorem finishMeta_fn (args : Args S) (key : Solanalib.Runtime.Pubkey) :
    Fn (finishMeta (Unwind := U) (Terminal := T) args key) (finishMetaF args key) :=
  fun _ _ _ => exists_bind_iff' (fun _ => Iff.rfl) fun _ => ret_iff

/-- `resolveSelected`, computed: unpack the seed vector, resolve the PDA in a
scope that drops it, and read the flags. -/
def resolveSelectedF (hb : VecPrims ops.bytes) (hs : VecPrims ops.seeds) (hr : VecPrims ops.refs)
    (dbl : S → U → U → T)
    (findF : S → Address.Syscall.PdaInputs → Option (Outcome S (Solanalib.Runtime.Pubkey × UInt8) U
      T))
    (args : Args S) (programAt : S → Option Solanalib.Runtime.Pubkey) :
    S → Unit → Option (Outcome S (Except Token.Error Solanalib.Runtime.CpiMeta) U T) :=
  fun before _ => (args.instructionAt before).bind fun instruction =>
    AllocatedSeeds.bindResultF
      (unpackF hb hs dbl fun state => (args.extraAt state).map (·.configuration))
      (fun seeds => Owned.scopeF dbl [hs.dropActionF seeds]
        (AllocatedSeeds.bindResultF
          (resolvePdaF hr dbl findF args ⟨instruction.length, args.instructionAt⟩ programAt seeds)
          (finishMetaF args)))
      before ()

/-- `resolveSelected ops double find args programAt` admits exactly
`resolveSelectedF hb hs hr dbl findF args programAt`. -/
theorem resolveSelected_fn (hb : VecPrims ops.bytes) (hs : VecPrims ops.seeds)
    (hr : VecPrims ops.refs) {double : Owned.DoubleUnwind S U T} {dbl : S → U → U → T}
    (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l) {find : FindPda S U T}
    {findF : S → Address.Syscall.PdaInputs → Option (Outcome S (Solanalib.Runtime.Pubkey × UInt8) U
      T)}
    (hfind : Fn find findF) (args : Args S) (programAt : S → Option Solanalib.Runtime.Pubkey) :
    Fn (resolveSelected ops double find args programAt)
      (resolveSelectedF hb hs hr dbl findF args programAt) := by
  intro before _ outcome
  refine exists_bind_iff' (fun _ => Iff.rfl) fun instruction => ?_
  exact AllocatedSeeds.bindResult_fn (unpack_fn hb hs hd _)
    (fun seeds => Owned.scope_fn hd (.cons (hs.dropAction_fn seeds) .nil)
      (AllocatedSeeds.bindResult_fn (resolvePda_fn hr hd hfind args _ programAt seeds)
        (finishMeta_fn args)))
    before () outcome

/-- `resolveKeyData`, computed: the PubkeyData branch has no dependency. -/
def resolveKeyDataF (args : Args S) (configuration : Solanalib.Runtime.Pubkey) :
    S → Unit → Option (Outcome S (Except Token.Error Solanalib.Runtime.Pubkey) U T) :=
  fun before _ =>
    match configuration.bytes with
    | 1 :: index :: _ =>
      (args.instructionAt before).bind fun instruction =>
        some (.returned
          (if index.toNat + 32 ≤ instruction.length then
            .ok (.ofBytes (Solanalib.Runtime.slice instruction index.toNat 32))
          else .error Hook.instructionDataTooSmall) before)
    | 2 :: index :: offset :: _ =>
      (args.accountsAt before).bind fun accounts =>
        some (.returned
          (match accounts[index.toNat]? with
          | none => .error Hook.accountNotFound
          | some (_, none) => .error Hook.accountDataNotFound
          | some (_, some bytes) =>
            if offset.toNat + 32 ≤ bytes.length then
              .ok (.ofBytes (Solanalib.Runtime.slice bytes offset.toNat 32))
            else .error Hook.accountDataTooSmall) before)
    | 1 :: _ | 2 :: _ => some (.returned (.error Hook.invalidPubkeyBytes) before)
    | _ => some (.returned (.error .InvalidAccountData) before)

/-- `resolveKeyData args configuration` admits exactly `resolveKeyDataF args configuration`. -/
theorem resolveKeyData_fn (args : Args S) (configuration : Solanalib.Runtime.Pubkey) :
    Fn (resolveKeyData (Unwind := U) (Terminal := T) args configuration)
      (resolveKeyDataF args configuration) := by
  intro before _ outcome
  unfold resolveKeyData resolveKeyDataF
  generalize configuration.bytes = bytes
  split <;> split <;>
    (try simp (config := { decide := true }) only [List.cons.injEq, true_and] at *) <;>
    first
    | (obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›; exact exists_bind_iff' (fun _ => Iff.rfl) fun _ => ret_iff)
    | (obtain ⟨rfl, rfl, rfl⟩ := ‹_ ∧ _›; exact exists_bind_iff' (fun _ => Iff.rfl) fun _ =>
      ret_iff)
    | exact ret_iff
    | (subst_vars; simp_all)

/-- `AllocatedSeeds.resolve`, computed: the static branch, the two PDA
branches through `resolveSelectedF`, and the PubkeyData branch. -/
def resolveF (hb : VecPrims ops.bytes) (hs : VecPrims ops.seeds) (hr : VecPrims ops.refs)
    (dbl : S → U → U → T)
    (findF : S → Address.Syscall.PdaInputs → Option (Outcome S (Solanalib.Runtime.Pubkey × UInt8) U
      T))
    (args : Args S) : S → Unit → Option (Outcome S (Except Token.Error Solanalib.Runtime.CpiMeta) U
      T) :=
  fun before _ => (args.extraAt before).bind fun extra =>
    if extra.discriminator.toNat = 0 then
      some (.returned (.ok (Instruction.accountMeta extra.configuration extra.isSigner
        extra.isWritable)) before)
    else if extra.discriminator.toNat = 1 then
      (args.programAt before).bind fun _ =>
        resolveSelectedF hb hs hr dbl findF args args.programAt before ()
    else if 128 ≤ extra.discriminator.toNat then
      (args.accountsAt before).bind fun accounts =>
        match accounts[extra.discriminator.toNat - 128]? with
        | none => some (.returned (.error Hook.accountNotFound) before)
        | some _ => resolveSelectedF hb hs hr dbl findF args
            (accountKeyAt args (extra.discriminator.toNat - 128)) before ()
    else if extra.discriminator.toNat = 2 then
      AllocatedSeeds.bindResultF (resolveKeyDataF args extra.configuration) (finishMetaF args)
        before ()
    else some (.returned (.error .InvalidAccountData) before)

/-- **Seed resolution.** `AllocatedSeeds.resolve ops double find args` admits
exactly `resolveF hb hs hr dbl findF args`, for any computed seed vector
bundles, double-unwind policy and address-library dependency. -/
theorem resolve_fn (hb : VecPrims ops.bytes) (hs : VecPrims ops.seeds) (hr : VecPrims ops.refs)
    {double : Owned.DoubleUnwind S U T} {dbl : S → U → U → T}
    (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l) {find : FindPda S U T}
    {findF : S → Address.Syscall.PdaInputs → Option (Outcome S (Solanalib.Runtime.Pubkey × UInt8) U
      T)}
    (hfind : Fn find findF) (args : Args S) :
    Fn (resolve ops double find args) (resolveF hb hs hr dbl findF args) := by
  intro before _ outcome
  refine exists_bind_iff' (fun _ => Iff.rfl) fun extra => ?_
  dsimp only
  by_cases t0 : extra.discriminator.toNat = 0
  · rw [ite_eq_left t0, ite_eq_left t0]; exact ret_iff
  rw [ite_eq_right t0, ite_eq_right t0]
  by_cases t1 : extra.discriminator.toNat = 1
  · rw [ite_eq_left t1, ite_eq_left t1]
    exact exists_bind_iff' (fun _ => Iff.rfl) fun _ =>
      resolveSelected_fn hb hs hr hd hfind args args.programAt before () outcome
  rw [ite_eq_right t1, ite_eq_right t1]
  by_cases high : 128 ≤ extra.discriminator.toNat
  · rw [ite_eq_left high, ite_eq_left high]
    refine exists_bind_iff' (fun _ => Iff.rfl) fun accounts => ?_
    cases accounts[extra.discriminator.toNat - 128]? with
    | none => exact ret_iff
    | some _ => exact resolveSelected_fn hb hs hr hd hfind args _ before () outcome
  rw [ite_eq_right high, ite_eq_right high]
  by_cases t2 : extra.discriminator.toNat = 2
  · rw [ite_eq_left t2, ite_eq_left t2]
    exact AllocatedSeeds.bindResult_fn (resolveKeyData_fn args extra.configuration)
      (finishMeta_fn args) before () outcome
  rw [ite_eq_right t2, ite_eq_right t2]
  exact ret_iff

end Seeds

/-! ## The collection dependency of the onchain model -/

section Borrow

variable {Extra U T : Type}

/-- `AllocatedCollect.borrowElement`, computed: the checked borrow, then the
copied key with the reference. -/
def borrowElementF
    (raiseF : AllocatedCollect.World Extra → Onchain.Panic →
      Option (Outcome (AllocatedCollect.World Extra) Empty U T)) :
    AllocatedCollect.World Extra → AccountInfo.Value →
      Option (Outcome (AllocatedCollect.World Extra)
        (Except Token.Error AllocatedCollect.Element) U T) :=
  fun s info => bindR (borrowR raiseF true info) (fun reference => pureR (info.key, reference)) s

/-- `AllocatedCollect.borrowElement raise` admits exactly `borrowElementF raiseF`. -/
theorem borrowElement_fn
    {raise : Callback.Run (AllocatedCollect.World Extra) Onchain.Panic Empty U T}
    {raiseF : AllocatedCollect.World Extra → Onchain.Panic →
      Option (Outcome (AllocatedCollect.World Extra) Empty U T)}
    (hraise : Fn raise raiseF) :
    Fn (AllocatedCollect.borrowElement raise) (borrowElementF raiseF) :=
  fun s info o => bindR_fn (borrowR_fn hraise true info) (fun _ => pureR_fn _) s o

end Borrow

section Model

open OnchainAllocated

variable {types : Types} {deps : Dependencies types}

/-- The `DepPrims` bundle of a collection dependency that is the reference
interpretation of a protocol with no internal chunk, `types.guards.fromList`
as its `finish`, computed storage retirements, a functional double-unwind
policy and the default partial-cleanup order. -/
def collectDepPrims (P : Prims types)
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource types.Unwind
      types.Terminal}
    (hcollect : deps.collect = AllocatedCollect.protocolProvider protocol)
    (hint : ∀ index acquired before outcome, ¬ protocol.internal index acquired before outcome)
    (hfinish : protocol.finish = types.guards.fromList)
    (retireF : Option types.GuardResource → List AllocatedCollect.Element → DropF types)
    (hret : ∀ resource acquired,
      DFn (protocol.retire resource acquired) (retireF resource acquired))
    {dbl : World types.Extra → types.Unwind → types.Unwind → types.Terminal}
    (hd : ∀ s o l t, protocol.double s o l t ↔ t = dbl s o l)
    (hord : ∀ before acquired, protocol.partialOrder before acquired = acquired)
    (invokeF : World types.Extra → CpiRequest.Request AccountInfo.Value →
      Option (Outcome (World types.Extra) (Except Token.Error Unit) types.Unwind types.Terminal))
    (invoke_fn : Fn deps.invoke invokeF) : DepPrims types deps where
  collectF := collectF P.guards.fromListF retireF dbl
  collect_fn := by
    rw [hcollect]
    exact collect_fn hint (hfinish ▸ P.guards.fromList_fn) hret hd hord
  invokeF := invokeF
  invoke_fn := invoke_fn

/-- `collectRefs`, computed: observe the infos, then collect with the borrow closure. -/
def collectRefsF (P : Prims types) (D : DepPrims types deps) (resource : types.InfoResource) :
    RunF types types.GuardResource :=
  bindR (inspectR fun state => types.infos.current state resource) fun infos =>
    D.collectF (infoIterator types resource infos.length) (borrowElementF P.raiseF)

/-- `collectRefs types deps resource` admits exactly `collectRefsF P D resource`. -/
theorem collectRefs_fn (P : Prims types) (D : DepPrims types deps)
    (resource : types.InfoResource) :
    RFn (collectRefs types deps resource) (collectRefsF P D resource) :=
  bindR_fn (inspectR_fn _) fun _ => D.collect_fn _ _ _ (borrowElement_fn P.raise_fn)

/-! ## The extra-account chain -/

/-- The resolver arguments of `resolveExtra`: the selected record, the
instruction bytes, the program key and the collected guard observations. -/
def resolveArgs (execute : Prepared types) (slice : ExtraSlice) (index : Nat)
    (references : types.GuardResource) : AllocatedSeeds.Args (World types.Extra) where
  extraAt := slice.entryAt types index
  instructionAt := fun current => types.bytes.current current execute.instruction.data
  programAt := fun _ => some execute.instruction.programId
  accountsAt := guardObservations types references

/-- `resolveExtra`, computed: collect the guards, then resolve in a scope that
drops the guard vector. -/
def resolveExtraF (P : Prims types) (D : DepPrims types deps) (execute : Prepared types)
    (slice : ExtraSlice) (index : Nat) : RunF types Solanalib.Runtime.CpiMeta :=
  bindR (collectRefsF P D execute.infos) fun references =>
    scopeR P.dbl [P.guards.dropActionF references]
      (fun s => resolveF P.seedBytes P.seeds P.seedRefs P.dbl (findPdaF P)
        (resolveArgs execute slice index references) s ())

/-- `resolveExtra types deps execute slice index` admits exactly
`resolveExtraF P D execute slice index`. -/
theorem resolveExtra_fn (P : Prims types) (D : DepPrims types deps) (execute : Prepared types)
    (slice : ExtraSlice) (index : Nat) :
    RFn (resolveExtra types deps execute slice index) (resolveExtraF P D execute slice index) :=
  bindR_fn (collectRefs_fn P D execute.infos) fun references =>
    scopeR_fn P.double_fn (.cons (P.guards.dropAction_fn references) .nil)
      (call_fn (resolve_fn P.seedBytes P.seeds P.seedRefs P.double_fn (findPda_fn P)
        (resolveArgs execute slice index references)) ())

/-- `appendResolved`, computed: de-escalate against the current metadata,
select the additional account, clone it, push the metadata (dropping the
clone if that fails) and push the clone. -/
def appendResolvedF (P : Prims types) (args : Onchain.Args) (execute : Prepared types)
    (resolved : Solanalib.Runtime.CpiMeta) : RunF types Unit :=
  bindR (inspectR fun state => types.metas.current state execute.instruction.metas) fun previous =>
    match args.additional.find? fun info =>
        info.key == (Hook.deescalate previous resolved).key with
    | none => failR Hook.incorrectExtraAccount
    | some info =>
      bindR (cloneInfoF P info) fun cloned =>
      bindR (moveOnOkR P.dbl [dropInfoF P cloned]
        (performR fun s => P.metas.pushF s
          (execute.instruction.metas, Hook.deescalate previous resolved))) fun _ =>
        performR fun s => P.infos.pushF s (execute.infos, cloned)

/-- `appendResolved types args execute resolved` admits exactly
`appendResolvedF P args execute resolved`. -/
theorem appendResolved_fn (P : Prims types) (args : Onchain.Args) (execute : Prepared types)
    (resolved : Solanalib.Runtime.CpiMeta) :
    RFn (appendResolved types args execute resolved) (appendResolvedF P args execute resolved) := by
  refine bindR_fn (inspectR_fn _) fun previous => ?_
  dsimp only
  cases args.additional.find? (fun info => info.key == (Hook.deescalate previous resolved).key) with
  | none => exact failR_fn _
  | some info =>
    exact bindR_fn (cloneInfo_fn P info) fun cloned =>
      bindR_fn (moveOnOkR_fn P.double_fn (.cons (dropInfo_fn P cloned) .nil)
        (performCall_fn P.metas.push_fn _)) fun _ => performCall_fn P.infos.push_fn _

/-- `addExtraEntries`, computed by the same recursion on the remaining count. -/
def addExtraEntriesF (P : Prims types) (D : DepPrims types deps) (args : Onchain.Args)
    (execute : Prepared types) (slice : ExtraSlice) : Nat → Nat → RunF types Unit
  | 0, _ => pureR ()
  | remaining + 1, index =>
    bindR (resolveExtraF P D execute slice index) fun resolved =>
    bindR (appendResolvedF P args execute resolved) fun _ =>
      addExtraEntriesF P D args execute slice remaining (index + 1)

/-- `addExtraEntries types deps args execute slice remaining index` admits
exactly `addExtraEntriesF P D args execute slice remaining index`. -/
theorem addExtraEntries_fn (P : Prims types) (D : DepPrims types deps) (args : Onchain.Args)
    (execute : Prepared types) (slice : ExtraSlice) :
    ∀ remaining index, RFn (addExtraEntries types deps args execute slice remaining index)
      (addExtraEntriesF P D args execute slice remaining index)
  | 0, _ => pureR_fn ()
  | remaining + 1, index =>
    bindR_fn (resolveExtra_fn P D execute slice index) fun resolved =>
      bindR_fn (appendResolved_fn P args execute resolved) fun _ =>
        addExtraEntries_fn P D args execute slice remaining (index + 1)

/-- `addExtraList`, computed from the computed TLV validator `validateF` and
the computed `extraSlice` (`sliceF`) of component (7a). -/
def addExtraListF (P : Prims types) (D : DepPrims types deps) (args : Onchain.Args)
    (execute : Prepared types) (validateF : AllocatedControl.DataRef → RunF types Unit)
    (sliceF : AllocatedControl.DataRef → RunF types ExtraSlice)
    (reference : AllocatedControl.DataRef) : RunF types Unit :=
  bindR (validateF reference) fun _ =>
  bindR (sliceF reference) fun slice =>
    addExtraEntriesF P D args execute slice slice.count 0

/-- `addExtraList types deps args execute reference` admits exactly
`addExtraListF P D args execute validateF sliceF reference`, given the
`RFn` lemmas of the TLV validator and of `extraSlice`. -/
theorem addExtraList_fn (P : Prims types) (D : DepPrims types deps) (args : Onchain.Args)
    (execute : Prepared types) {validateF : AllocatedControl.DataRef → RunF types Unit}
    (hv : ∀ reference, RFn (fun state => AllocatedTlv.validate types.discriminators
      types.doubleUnwind reference.read state ()) (validateF reference))
    {sliceF : AllocatedControl.DataRef → RunF types ExtraSlice}
    (hs : ∀ reference, RFn (extraSlice types reference) (sliceF reference))
    (reference : AllocatedControl.DataRef) :
    RFn (addExtraList types deps args execute reference)
      (addExtraListF P D args execute validateF sliceF reference) :=
  bindR_fn (hv reference) fun _ => bindR_fn (hs reference) fun slice =>
    addExtraEntries_fn P D args execute slice slice.count 0

end Model

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainCollect
