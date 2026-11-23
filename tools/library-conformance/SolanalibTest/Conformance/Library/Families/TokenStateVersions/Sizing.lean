/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SplToken2022Interface.Extensions
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.Operational

set_option autoImplicit false

open Solanalib.Specs.SplToken2022Interface

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.Sizing

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.Extensions (Ledger dblE doubleE_fn
  drops_fn)

abbrev BOut := Outcome Ledger Nat Empty Empty
abbrev SOut := Outcome Ledger (Except Token.Error Nat) Empty Empty

def pushesF (resource : Nat) : List ExtensionType → Ledger →
    Option (Outcome Ledger Unit Empty Empty)
  | [], before => some (.returned () before)
  | value :: rest, before => (modifyF before resource (· ++ [value])).bind
      (thenOpt · (fun _ after => pushesF resource rest after))

theorem pushes_fn (resource : Nat) (values : List ExtensionType) (before : Ledger)
    (o : Outcome Ledger Unit Empty Empty) :
    Legacy.pushAll Owned.vectorReference resource values before o ↔
      pushesF resource values before = some o := by
  induction values generalizing before o with
  | nil =>
    exact ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩
  | cons value rest ih =>
    change (∃ pushed, Owned.vectorReference.push before (resource, value) pushed ∧ _) ↔ _
    rw [pushesF]
    constructor
    · rintro ⟨pushed, hp, continued⟩
      rw [(modify_fn before resource (· ++ [value]) pushed).1 hp, Option.bind_some]
      cases pushed with
      | returned u after => cases u; exact (ih after o).1 continued
      | unwound r _ => exact r.elim
      | terminated r => exact r.elim
    · intro h
      cases hp : modifyF (U := Empty) (T := Empty) before resource (· ++ [value]) with
      | none => rw [hp] at h; cases h
      | some pushed =>
        rw [hp, Option.bind_some] at h
        refine ⟨pushed, (modify_fn before resource (· ++ [value]) pushed).2 hp, ?_⟩
        cases pushed with
        | returned u after => cases u; exact (ih after o).2 h
        | unwound r _ => exact r.elim
        | terminated r => exact r.elim

/-- Only deduplication inspects the current accumulated vector. -/
def additions (mode : Legacy.BuildKind) (kind : ExtensionType) (resource : Nat)
    (before : Ledger) : Option (List ExtensionType) :=
  match mode with
  | .required => some kind.requiredAccountExtensions
  | .deduplicate => (before.current resource).map (Legacy.pendingPushes .deduplicate kind)

def buildF (mode : Legacy.BuildKind) (input : List Legacy.Kind) (resource index : Nat)
    (before : Ledger) : Option BOut :=
  if bound : index < input.length then
    (additions mode input[index].val resource before).bind fun pending =>
      (pushesF resource pending before).bind fun pushed =>
        match pushed with
        | .returned () after => buildF mode input resource (index + 1) after
        | .unwound r after => cleanupF dblE [fun st => retireF st resource] (.unwound r after)
        | .terminated r => some (.terminated r)
  else some (.returned resource before)
termination_by input.length - index

/-- At the closed successful allocator, only returned Unit outcomes exist. -/
theorem unit_outcome_exists {P : Outcome Ledger Unit Empty Empty → Prop} :
    (∃ outcome, P outcome) ↔ ∃ after, P (.returned () after) := by
  constructor
  · rintro ⟨outcome, found⟩
    cases outcome with
    | returned u after => cases u; exact ⟨after, found⟩
    | unwound reason _ => exact reason.elim
    | terminated reason => exact reason.elim
  · rintro ⟨after, found⟩
    exact ⟨.returned () after, found⟩

theorem build_fn (mode : Legacy.BuildKind) (input : List Legacy.Kind) (resource index : Nat)
    (before : Ledger) (o : BOut) :
    Legacy.buildVector mode Legacy.typeArrayReference input resource index before o ↔
      buildF mode input resource index before = some o := by
  dsimp only [Legacy.typeArrayReference]
  by_cases bound : index < input.length
  · rw [Legacy.buildVector, buildF]
    change (if _ : index < input.length then _ else _) ↔
      (if _ : index < input.length then _ else _) = some o
    rw [dite_eq_left bound, dite_eq_left bound]
    have step (pending : List ExtensionType) :
        (∃ pushed, Legacy.pushAll Owned.vectorReference resource pending before pushed ∧
          match pushed with
          | .returned () after => Legacy.buildVector mode Legacy.typeArrayReference input resource
              (index + 1) after o
          | .unwound r after => Owned.cleanup (fun _ _ _ _ => False)
              [(Owned.vectorReference : Owned.VectorOps Ledger ExtensionType Nat Empty
                Empty).dropAction resource]
              (.unwound r after) o
          | .terminated r => o = .terminated r) ↔
        (pushesF resource pending before).bind (fun pushed =>
          match pushed with
          | .returned () after => buildF mode input resource (index + 1) after
          | .unwound r after => cleanupF dblE [fun st => retireF st resource] (.unwound r after)
          | .terminated r => some (.terminated r)) = some o := by
      constructor
      · rintro ⟨pushed, hp, continued⟩
        rw [(pushes_fn resource pending before pushed).1 hp, Option.bind_some]
        cases pushed with
        | returned u after =>
          cases u; exact (build_fn mode input resource (index + 1) after o).1 continued
        | unwound r _ => exact r.elim
        | terminated r => exact r.elim
      · intro h
        cases hp : pushesF resource pending before with
        | none => rw [hp] at h; cases h
        | some pushed =>
          rw [hp, Option.bind_some] at h
          refine ⟨pushed, (pushes_fn resource pending before pushed).2 hp, ?_⟩
          cases pushed with
          | returned u after =>
            cases u; exact (build_fn mode input resource (index + 1) after o).2 h
          | unwound r _ => exact r.elim
          | terminated r => exact r.elim
    simp only [unit_outcome_exists, Legacy.typeArrayReference] at step
    cases mode with
    | required =>
      simpa only [additions, Option.bind_some, unit_outcome_exists] using
        step input[index].val.requiredAccountExtensions
    | deduplicate =>
      dsimp only [additions]
      change (∃ values, before.current resource = some values ∧ _) ↔ _
      cases hc : before.current resource with
      | none => simp
      | some values =>
        simp only [Option.map_some, Option.bind_some]
        constructor
        · rintro ⟨observed, current, continued⟩
          cases Option.some.inj current
          apply (step (Legacy.pendingPushes .deduplicate input[index].val values)).1
          simpa only [unit_outcome_exists] using continued
        · intro h
          refine ⟨values, rfl, ?_⟩
          simpa only [unit_outcome_exists] using
            (step (Legacy.pendingPushes .deduplicate input[index].val values)).2 h
  · rw [Legacy.buildVector, buildF]
    change (if _ : index < input.length then _ else _) ↔
      (if _ : index < input.length then _ else _) = some o
    rw [dite_eq_right bound, dite_eq_right bound]
    exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
termination_by input.length - index

def sizeF (baseLength : Nat) (input : List Legacy.Kind) (before : Ledger) : Option SOut :=
  if input.length = 0 then some (.returned (.ok baseLength) before)
  else (buildF .deduplicate input before.length 0 (before ++ [some []])).bind fun built =>
    match built with
    | .returned resource after =>
      (after.current resource).bind fun values =>
        (cleanupF dblE [fun st => retireF st resource] (.returned (Legacy.sumLengths values)
          after)).map
          (Outcome.map (Except.map Legacy.accountSize))
    | .unwound r after => some (.unwound r after)
    | .terminated r => some (.terminated r)

theorem size_fn (baseLength : Nat) (input : List Legacy.Kind) (before : Ledger) (o : SOut) :
    Solanalib.Specs.SplToken2022.extension.ExtensionType.try_calculate_account_len_run
      ⟨Legacy.typeArrayReference, baseLength⟩ before input o ↔ sizeF baseLength input before = some
        o := by
  change Legacy.calculateAccountLength ⟨Legacy.typeArrayReference, baseLength⟩ before input o ↔ _
  dsimp only [Legacy.calculateAccountLength, Legacy.typeArrayReference]
  unfold sizeF
  by_cases empty : input.length = 0
  · simp only [empty, ↓reduceIte]
    exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
  · simp only [empty, ↓reduceIte]
    constructor
    · rintro ⟨built, hb, continued⟩
      rw [(build_fn .deduplicate input before.length 0 (before ++ [some []]) built).1 hb,
        Option.bind_some]
      cases built with
      | returned resource after =>
        dsimp only at continued ⊢
        obtain ⟨values, current, cleaned, dropped, rfl⟩ := continued
        change after.current resource = some values at current
        rw [current, Option.bind_some, (cleanup_fn doubleE_fn _ _ (drops_fn resource) _ _).1
          dropped]
        rfl
      | unwound r _ => exact r.elim
      | terminated r => exact r.elim
    · intro h
      cases hb : buildF .deduplicate input before.length 0 (before ++ [some []]) with
      | none => rw [hb] at h; cases h
      | some built =>
        rw [hb, Option.bind_some] at h
        refine ⟨built, (build_fn .deduplicate input before.length 0 (before ++ [some []]) built).2
          hb, ?_⟩
        cases built with
        | returned resource after =>
          dsimp only at h ⊢
          cases hc : after.current resource with
          | none => rw [hc] at h; cases h
          | some values =>
            rw [hc, Option.bind_some] at h
            cases hd : cleanupF dblE [fun st => retireF st resource] (.returned (Legacy.sumLengths
              values) after) with
            | none => rw [hd] at h; cases h
            | some cleaned =>
              rw [hd] at h
              exact ⟨values, hc, cleaned, (cleanup_fn doubleE_fn _ _ (drops_fn resource) _ _).2 hd,
                (Option.some.inj h).symm⟩
        | unwound r _ => exact r.elim
        | terminated r => exact r.elim

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.Sizing

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.Sizing

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.Extensions (Ledger dblE doubleE_fn
  drops_fn)

/-- The result stays owned, including the zero-allocation empty-vector case. -/
def requiredF (input : List Legacy.Kind) (before : Ledger) : Option BOut :=
  buildF .required input before.length 0 (before ++ [some []])

theorem required_fn (input : List Legacy.Kind) (before : Ledger) (o : BOut) :
    extension.ExtensionType.get_required_init_account_extensions_run
      Legacy.typeArrayReference before input o ↔ requiredF input before = some o :=
  build_fn .required input before.length 0 (before ++ [some []]) o

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.Sizing
