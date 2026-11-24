/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc
import Solanalib.Specs.Core.TokenRequestAllocatedLiteral

/-!
# Array-literal construction, computed

`Owned.Array.Provider.run` interprets a Rust array literal through a provider:
its `work` dependency may run another internal chunk (`.again`), ask for the
next expression (`.evaluate`) or ask for completion (`.finish`), and the
relation `Owned.Array.Trace` admits every finite sequence of such answers. A
provider that never answers `.again` (`NoAgain`) evaluates each expression
once, so for a provider bundled as `ArrayPrims` the trace admits at most one
outcome. This module computes it (`Owned.Array.traceF`), by recursion on the
number of expressions still to evaluate, and proves `Owned.Array.Trace_fn`,
`runDetailed_fn` and `run_fn`.

An unwind cleans the evaluated prefix (`Provider.close`). Its cleanup order
must be a permutation of the evaluated positions; the permutation check is
decidable, so `Owned.Array.closeF` decides it and needs no hypothesis on the
order. The identity order of the closed index passes it.

The last section instantiates the provider with the literal
provider of the onchain model (`OnchainRc.literalPrims`) and computes the two account-array
literals: `initialInfos` and `executeInfos`.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainLiteral

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.OnchainAllocated
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc

/-! ## A provider that never answers `.again` -/

section Generic

variable {S E Res U T : Type} {provider : Owned.Array.Provider S E Res U T}

/-- `provider.cleanupActions values order`, computed: the element drops in the
given order, then the storage retirement. -/
def Owned.Array.cleanupActionsF (h : ArrayPrims provider) (values : List E)
    (order : List (Fin values.length)) : List (S → Option (Outcome S Unit U T)) :=
  order.map (fun index s => h.dropF s values[index]) ++ [fun s => h.retireF s values]

/-- Each of `provider.cleanupActions values order` admits exactly the computed
action. -/
theorem Owned.Array.cleanupActions_fn (h : ArrayPrims provider) (values : List E)
    (order : List (Fin values.length)) :
    All2 DFn (provider.cleanupActions values order)
      (Owned.Array.cleanupActionsF h values order) :=
  All2.append (All2.map _ _ (fun index s o => h.drop_fn s values[index] o) order)
    (.cons (fun s o => h.retire_fn s values o) .nil)

/-- `provider.close`, computed: check the cleanup order, run the cleanup
actions on the unwind, and annotate the progress. An order that is not a
permutation of the evaluated positions admits no outcome. -/
def Owned.Array.closeF (h : ArrayPrims provider) (values : List E)
    (site : Owned.Array.FailureSite) (before : S) (reason : U) :
    Option (Outcome S Res (Owned.Array.Failure × U) T) :=
  if (provider.cleanupOrder before values).Perm (List.finRange values.length) then
    (cleanupF h.dbl (Owned.Array.cleanupActionsF h values (provider.cleanupOrder before values))
      (.unwound reason before)).map (Owned.Array.annotate ⟨values.length, site⟩)
  else none

/-- `provider.close values site before reason` admits exactly
`closeF h values site before reason`. -/
theorem Owned.Array.close_fn (h : ArrayPrims provider) (values : List E)
    (site : Owned.Array.FailureSite) (before : S) (reason : U) :
    OFn (provider.close values site before reason)
      (Owned.Array.closeF h values site before reason) := by
  intro final
  unfold Owned.Array.Provider.close Owned.Array.closeF
  by_cases hp : (provider.cleanupOrder before values).Perm (List.finRange values.length)
  · simp only [hp, ↓reduceIte]
    have hc := cleanup_fn (V := Res) h.double_fn _ _
      (Owned.Array.cleanupActions_fn h values (provider.cleanupOrder before values))
      (.unwound reason before)
    constructor
    · rintro ⟨-, pending, hpend, rfl⟩
      rw [(hc pending).1 hpend]; rfl
    · intro e
      cases hcf : cleanupF h.dbl
          (Owned.Array.cleanupActionsF h values (provider.cleanupOrder before values))
          (.unwound reason before) with
      | none => rw [hcf] at e; cases e
      | some pending =>
        rw [hcf] at e
        exact ⟨trivial, pending, (hc pending).2 hcf, Option.some.inj e⟩
  · simp only [hp, ↓reduceIte]
    exact ⟨fun h => h.1.elim, fun e => by cases e⟩

/-- The literal trace, computed for a provider that never answers `.again`:
from the evaluated prefix `values`, ask `work`, then evaluate the next
expression and recurse on the extended prefix, or finish, or clean up. An
`.again` answer, an answer that breaks the expression count and an absent
dependency outcome admit no outcome. -/
def Owned.Array.traceF (h : ArrayPrims provider) (count : Nat)
    (evaluateF : S → Nat → Option (Outcome S E U T)) (values : List E) (before : S) :
    Option (Outcome S Res (Owned.Array.Failure × U) T) :=
  match h.workF before (count, values) with
  | some (.returned .again _) => none
  | some (.returned .evaluate ready) =>
    if values.length < count then
      match evaluateF ready values.length with
      | some (.returned value after) =>
        Owned.Array.traceF h count evaluateF (values ++ [value]) after
      | some (.unwound reason after) => Owned.Array.closeF h values .evaluate after reason
      | some (.terminated reason) => some (.terminated reason)
      | none => none
    else none
  | some (.returned .finish ready) =>
    if values.length = count then
      match h.finishF ready values with
      | some (.returned resource after) => some (.returned resource after)
      | some (.unwound reason after) => Owned.Array.closeF h values .finish after reason
      | some (.terminated reason) => some (.terminated reason)
      | none => none
    else none
  | some (.unwound reason after) => Owned.Array.closeF h values .work after reason
  | some (.terminated reason) => some (.terminated reason)
  | none => none
termination_by count - values.length
decreasing_by simp only [List.length_append, List.length_singleton]; omega

/-- Forward half of `Owned.Array.Trace_fn`: every trace is the computed one.
An `.again` step contradicts `NoAgain`. -/
theorem Owned.Array.traceF_of_trace (h : ArrayPrims provider) (hna : NoAgain provider)
    {evaluate : Callback.Run S Nat E U T} {evaluateF : S → Nat → Option (Outcome S E U T)}
    (he : Fn evaluate evaluateF) {count : Nat} {values : List E} {before : S}
    {final : Outcome S Res (Owned.Array.Failure × U) T}
    (trace : Owned.Array.Trace provider count evaluate values before final) :
    Owned.Array.traceF h count evaluateF values before = some final := by
  induction trace with
  | again _ _ _ _ work => exact (hna _ _ _ work).elim
  | next values before ready after value final bound work expression _ ih =>
    rw [Owned.Array.traceF, (h.work_fn _ _ _).1 work]
    simp only [bound, ↓reduceIte, (he _ _ _).1 expression]
    exact ih
  | workUnwind values before after reason final work closed =>
    rw [Owned.Array.traceF, (h.work_fn _ _ _).1 work]
    exact (Owned.Array.close_fn h values _ after reason final).1 closed
  | workTerminal values before reason work =>
    rw [Owned.Array.traceF, (h.work_fn _ _ _).1 work]
  | evaluateUnwind values before ready after reason final bound work expression closed =>
    rw [Owned.Array.traceF, (h.work_fn _ _ _).1 work]
    simp only [bound, ↓reduceIte, (he _ _ _).1 expression]
    exact (Owned.Array.close_fn h values _ after reason final).1 closed
  | evaluateTerminal values before ready reason bound work expression =>
    rw [Owned.Array.traceF, (h.work_fn _ _ _).1 work]
    simp only [bound, ↓reduceIte, (he _ _ _).1 expression]
  | finishReturn values before ready after resource complete work finished =>
    rw [Owned.Array.traceF, (h.work_fn _ _ _).1 work]
    simp only [complete, ↓reduceIte, (h.finish_fn _ _ _).1 finished]
  | finishUnwind values before ready after reason final complete work finished closed =>
    rw [Owned.Array.traceF, (h.work_fn _ _ _).1 work]
    simp only [complete, ↓reduceIte, (h.finish_fn _ _ _).1 finished]
    exact (Owned.Array.close_fn h values _ after reason final).1 closed
  | finishTerminal values before ready reason complete work finished =>
    rw [Owned.Array.traceF, (h.work_fn _ _ _).1 work]
    simp only [complete, ↓reduceIte, (h.finish_fn _ _ _).1 finished]

/-- Backward half of `Owned.Array.Trace_fn`: the computed outcome is a trace.
The recursion mirrors that of `traceF`, on the number of expressions still to
evaluate; the `next` step uses its bound. -/
theorem Owned.Array.trace_of_traceF (h : ArrayPrims provider)
    {evaluate : Callback.Run S Nat E U T} {evaluateF : S → Nat → Option (Outcome S E U T)}
    (he : Fn evaluate evaluateF) (count : Nat) (values : List E) (before : S)
    (final : Outcome S Res (Owned.Array.Failure × U) T)
    (e : Owned.Array.traceF h count evaluateF values before = some final) :
    Owned.Array.Trace provider count evaluate values before final := by
  rw [Owned.Array.traceF] at e
  split at e
  · cases e
  · rename_i ready hw
    have work := (h.work_fn _ _ _).2 hw
    split at e
    · rename_i bound
      split at e
      · rename_i value after hv
        exact .next values before ready after value final bound work ((he _ _ _).2 hv)
          (Owned.Array.trace_of_traceF h he count (values ++ [value]) after final e)
      · rename_i reason after hv
        exact .evaluateUnwind values before ready after reason final bound work ((he _ _ _).2 hv)
          ((Owned.Array.close_fn h values _ after reason final).2 e)
      · rename_i reason hv
        cases e
        exact .evaluateTerminal values before ready reason bound work ((he _ _ _).2 hv)
      · cases e
    · cases e
  · rename_i ready hw
    have work := (h.work_fn _ _ _).2 hw
    split at e
    · rename_i complete
      split at e
      · rename_i resource after hf
        cases e
        exact .finishReturn values before ready after resource complete work ((h.finish_fn _ _ _).2
          hf)
      · rename_i reason after hf
        exact .finishUnwind values before ready after reason final complete work
          ((h.finish_fn _ _ _).2 hf) ((Owned.Array.close_fn h values _ after reason final).2 e)
      · rename_i reason hf
        cases e
        exact .finishTerminal values before ready reason complete work ((h.finish_fn _ _ _).2 hf)
      · cases e
    · cases e
  · rename_i reason after hw
    exact .workUnwind values before after reason final ((h.work_fn _ _ _).2 hw)
      ((Owned.Array.close_fn h values _ after reason final).2 e)
  · rename_i reason hw
    cases e
    exact .workTerminal values before reason ((h.work_fn _ _ _).2 hw)
  · cases e
termination_by count - values.length
decreasing_by simp only [List.length_append, List.length_singleton]; omega

/-- A provider that never answers `.again` admits exactly the computed trace. -/
theorem Owned.Array.Trace_fn (h : ArrayPrims provider) (hna : NoAgain provider)
    {evaluate : Callback.Run S Nat E U T} {evaluateF : S → Nat → Option (Outcome S E U T)}
    (he : Fn evaluate evaluateF) (count : Nat) (values : List E) (before : S) :
    OFn (Owned.Array.Trace provider count evaluate values before)
      (Owned.Array.traceF h count evaluateF values before) :=
  fun final => ⟨Owned.Array.traceF_of_trace h hna he,
    Owned.Array.trace_of_traceF h he count values before final⟩

/-- `provider.runDetailed`, computed: the trace from the empty prefix. -/
def Owned.Array.runDetailedF (h : ArrayPrims provider) (count : Nat)
    (evaluateF : S → Nat → Option (Outcome S E U T)) (before : S) :
    Option (Outcome S Res (Owned.Array.Failure × U) T) :=
  Owned.Array.traceF h count evaluateF [] before

/-- `provider.runDetailed count evaluate` admits exactly
`runDetailedF h count evaluateF`, for a provider that never answers `.again`. -/
theorem Owned.Array.runDetailed_fn (h : ArrayPrims provider) (hna : NoAgain provider)
    {evaluate : Callback.Run S Nat E U T} {evaluateF : S → Nat → Option (Outcome S E U T)}
    (he : Fn evaluate evaluateF) (count : Nat) (before : S) :
    OFn (provider.runDetailed count evaluate before)
      (Owned.Array.runDetailedF h count evaluateF before) :=
  Owned.Array.Trace_fn h hna he count [] before

/-- `provider.run`, computed: the detailed outcome without its progress. -/
def Owned.Array.runF (h : ArrayPrims provider) (count : Nat)
    (evaluateF : S → Nat → Option (Outcome S E U T)) (before : S) :
    Option (Outcome S Res U T) :=
  (Owned.Array.runDetailedF h count evaluateF before).map Owned.Array.erase

/-- `provider.run count evaluate` admits exactly `runF h count evaluateF`, for a
provider that never answers `.again`. -/
theorem Owned.Array.run_fn (h : ArrayPrims provider) (hna : NoAgain provider)
    {evaluate : Callback.Run S Nat E U T} {evaluateF : S → Nat → Option (Outcome S E U T)}
    (he : Fn evaluate evaluateF) (count : Nat) (before : S) :
    OFn (provider.run count evaluate before) (Owned.Array.runF h count evaluateF before) := by
  have hd := Owned.Array.runDetailed_fn h hna he count before
  intro final
  constructor
  · rintro ⟨detailed, hdet, rfl⟩
    show (Owned.Array.runDetailedF h count evaluateF before).map _ = _
    rw [(hd detailed).1 hdet]; rfl
  · intro e
    cases hr : Owned.Array.runDetailedF h count evaluateF before with
    | none => simp [Owned.Array.runF, hr] at e
    | some detailed =>
      simp only [Owned.Array.runF, hr, Option.map_some, Option.some.injEq] at e
      exact ⟨detailed, (hd detailed).2 hr, e⟩

end Generic

/-! ## The two AccountInfo literals of the onchain model -/

section Model

variable {types : Types}

/-- `initialInfos`, computed: the four-element literal of clones of source,
mint, destination and authority. -/
def initialInfosF (P : Prims types) (args : Onchain.Args) : RunF types types.InfoResource :=
  performR fun s => Owned.Array.runF (literalPrims P) 4 (initialInfoAtF P args) s

/-- `initialInfos types args` admits exactly `initialInfosF P args` when the
literal work never answers `.again`. -/
theorem initialInfos_fn (P : Prims types) (hna : NoAgain types.infoLiteral)
    (args : Onchain.Args) : RFn (initialInfos types args) (initialInfosF P args) :=
  performR_fn (Owned.Array.run_fn (literalPrims P) hna (initialInfoAt_fn P args) 4)

/-- The exit of `executeInfos` after the literal, computed: a returned vector
is `Ok`; an unwind cleans the instruction and the arguments not yet moved into
the literal (`Failure.completed`), and a terminal exit stays terminal. -/
def executeExitF (P : Prims types) (args : Onchain.Args)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    Outcome (World types.Extra) types.InfoResource (Owned.Array.Failure × types.Unwind)
      types.Terminal →
    Option (Outcome (World types.Extra) (Except Token.Error types.InfoResource) types.Unwind
      types.Terminal)
  | .returned resource after => some (.returned (.ok resource) after)
  | .unwound (failure, reason) after =>
    cleanupF P.dbl (instructionDropsF P instruction ++ executeRemainderF P args failure.completed)
      (.unwound reason after)
  | .terminated reason => some (.terminated reason)

/-- `executeInfos`, computed: the five-element literal of the four moved
arguments and a clone of the validation account, then `executeExitF`. -/
def executeInfosF (P : Prims types) (args : Onchain.Args) (validation : AccountInfo.Value)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    RunF types types.InfoResource :=
  fun s => (Owned.Array.runDetailedF (literalPrims P) 5 (executeInfoAtF P args validation) s).bind
    (executeExitF P args instruction)

/-- `executeInfos types args validation instruction` admits exactly
`executeInfosF P args validation instruction` when the literal work never
answers `.again`. -/
theorem executeInfos_fn (P : Prims types) (hna : NoAgain types.infoLiteral)
    (args : Onchain.Args) (validation : AccountInfo.Value)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    RFn (executeInfos types args validation instruction)
      (executeInfosF P args validation instruction) := by
  have hd := Owned.Array.runDetailed_fn (literalPrims P) hna (executeInfoAt_fn P args validation) 5
  have hc := fun completed => cleanup_fn (V := Except Token.Error types.InfoResource)
    P.double_fn _ _ (All2.append (instructionDrops_fn P instruction)
      (executeRemainder_fn P args completed))
  have hx : ∀ detailed o, (match detailed with
      | .returned resource after => o = .returned (.ok resource) after
      | .unwound (failure, reason) after =>
        Owned.cleanup types.doubleUnwind
          (instructionDrops types instruction ++ executeRemainder types args failure.completed)
          (.unwound reason after) o
      | .terminated reason => o = .terminated reason) ↔
      executeExitF P args instruction detailed = some o := by
    intro detailed o
    match detailed with
    | .returned resource after => exact ⟨fun e => by rw [e]; rfl, fun e => (Option.some.inj e).symm⟩
    | .unwound (failure, reason) after => exact hc failure.completed _ o
    | .terminated reason => exact ⟨fun e => by rw [e]; rfl, fun e => (Option.some.inj e).symm⟩
  intro s o
  constructor
  · rintro ⟨detailed, hdet, hm⟩
    show (Owned.Array.runDetailedF _ _ _ s).bind _ = _
    rw [(hd s detailed).1 hdet, Option.bind_some]
    exact (hx detailed o).1 hm
  · intro e
    cases hr : Owned.Array.runDetailedF (literalPrims P) 5 (executeInfoAtF P args validation) s with
    | none => simp [executeInfosF, hr] at e
    | some detailed =>
      simp only [executeInfosF, hr, Option.bind_some] at e
      exact ⟨detailed, (hd s detailed).2 hr, (hx detailed o).2 e⟩

end Model

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainLiteral
