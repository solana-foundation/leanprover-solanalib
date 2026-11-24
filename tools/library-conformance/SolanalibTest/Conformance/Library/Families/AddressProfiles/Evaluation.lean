/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Address
import Solanalib.Specs.Core.AddressDerived

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AddressProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
  Solanalib.Specs.Core.Address.Syscall
open Solanalib.Specs.Core.Address.Operations

namespace Evaluation

variable {S U T : Type}

abbrev createIndex (mode : Initialization)
    (sys : S → CreateRequest → Outcome S (CreateReply mode) U T)
    (panic : S → String → Outcome S Empty U T) : CreateIndex mode :=
  ⟨⟨S, U, T⟩, Callback.ofFunction sys, Callback.ofFunction panic⟩

def finishCreateEval {mode : Initialization} (profile : ErrorProfile)
    (panic : S → String → Outcome S Empty U T) (reply : CreateReply mode) (after : S) :
    Option (Outcome S (Except Error Value) U T) :=
  if reply.status = 0 then
    (mode.observe reply.output).map fun value => .returned (.ok value) after
  else match profile.decode reply.status with
    | some error => some (.returned (.error error) after)
    | none => some (Outcome.map (fun impossible : Empty => nomatch impossible)
        (panic after profile.panicMessage))

theorem finishCreate_ofFunction {mode : Initialization} (profile : ErrorProfile)
    (sys : S → CreateRequest → Outcome S (CreateReply mode) U T)
    (panic : S → String → Outcome S Empty U T) (reply : CreateReply mode) (after : S)
    (o : Outcome S (Except Error Value) U T) :
    finishCreate profile (createIndex mode sys panic) reply after o ↔
      finishCreateEval profile panic reply after = some o := by
  unfold finishCreate finishCreateEval
  by_cases zero : reply.status = 0
  · simp only [zero, ↓reduceIte]
    cases mode.observe reply.output <;> simp [eq_comm]
  · simp only [zero, ↓reduceIte]
    cases profile.decode reply.status with
    | some error => simp [eq_comm]
    | none =>
      simp only [Option.some.injEq]
      exact Callback.map_ofFunction _ panic after profile.panicMessage o

def createEval {mode : Initialization} (profile : ErrorProfile)
    (sys : S → CreateRequest → Outcome S (CreateReply mode) U T)
    (panic : S → String → Outcome S Empty U T) (before : S) (inputs : PdaInputs) :
    Option (Outcome S (Except Error Value) U T) :=
  if badSeeds inputs then some (.returned (.error .maxSeedLengthExceeded) before)
  else match sys before (createRequest mode inputs) with
    | .returned reply after => finishCreateEval profile panic reply after
    | .unwound reason after => some (.unwound reason after)
    | .terminated reason => some (.terminated reason)

theorem createRun_ofFunction {mode : Initialization} (profile : ErrorProfile)
    (sys : S → CreateRequest → Outcome S (CreateReply mode) U T)
    (panic : S → String → Outcome S Empty U T) (before : S) (inputs : PdaInputs)
    (o : Outcome S (Except Error Value) U T) :
    createRun profile (createIndex mode sys panic) before inputs o ↔
      createEval profile sys panic before inputs = some o := by
  unfold createRun createEval
  by_cases bad : badSeeds inputs = true
  · simp [bad, eq_comm]
  · simp only [bad]
    unfold Callback.bind
    constructor
    · rintro ⟨actual, step, rest⟩
      change sys before (createRequest mode inputs) = actual at step
      subst actual
      cases hs : sys before (createRequest mode inputs) with
      | returned reply after =>
        rw [hs] at rest
        exact (finishCreate_ofFunction profile sys panic reply after o).mp rest
      | unwound reason after => rw [hs] at rest; simp [rest]
      | terminated reason => rw [hs] at rest; simp [rest]
    · intro h
      refine ⟨sys before (createRequest mode inputs), rfl, ?_⟩
      cases hs : sys before (createRequest mode inputs) with
      | returned reply after =>
        rw [hs] at h
        exact (finishCreate_ofFunction profile sys panic reply after o).mpr h
      | unwound reason after => rw [hs] at h; simpa [eq_comm] using h
      | terminated reason => rw [hs] at h; simpa [eq_comm] using h

def createInitializedB {mode : Initialization} : Outcome S (CreateReply mode) U T → Bool
  | .returned reply _ => reply.status != 0 || (mode.observe reply.output).isSome
  | _ => true

def createReadyB (mode : Initialization) (sys : S → CreateRequest → Outcome S (CreateReply mode) U
  T)
    (before : S) (inputs : PdaInputs) : Bool :=
  match mode with
  | .zeroed => true
  | .uninitialized => badSeeds inputs || createInitializedB (sys before (createRequest mode inputs))

theorem createReady_ofFunction (mode : Initialization)
    (sys : S → CreateRequest → Outcome S (CreateReply mode) U T)
    (panic : S → String → Outcome S Empty U T) (before : S) (inputs : PdaInputs) :
    createReady (createIndex mode sys panic) before inputs ↔ createReadyB mode sys before inputs =
      true := by
  cases mode with
  | zeroed => exact iff_of_true trivial rfl
  | uninitialized =>
    unfold createReady createReadyB
    by_cases bad : badSeeds inputs = true
    · simp [bad]
    · have good : badSeeds inputs = false := Bool.eq_false_iff.mpr bad
      simp only [good, Bool.false_or, forall_const]
      change (∀ reply after, sys before (createRequest .uninitialized inputs) = .returned reply
        after →
        reply.status = 0 → ∃ value, reply.output = some value) ↔ _
      cases hs : sys before (createRequest .uninitialized inputs) with
      | returned reply after =>
        simp only [createInitializedB, Initialization.observe, id_eq, Bool.or_eq_true, bne_iff_ne,
          ne_eq]
        constructor
        · intro h
          by_cases zero : reply.status = 0
          · exact Or.inr (Option.isSome_iff_exists.mpr (h reply after rfl zero))
          · exact Or.inl zero
        · intro h reply' after' same zero
          cases same
          exact Option.isSome_iff_exists.mp (h.resolve_left (fun ne => ne zero))
      | unwound reason after => simp [createInitializedB]
      | terminated reason => simp [createInitializedB]

abbrev zeroFindIndex (sys : S → PdaRequest → Outcome S ZeroFindReply U T)
    (panic : S → SearchPanic → Outcome S Empty U T) : ZeroFindIndex :=
  ⟨⟨S, U, T⟩, Callback.ofFunction sys, Callback.ofFunction panic⟩

def zeroFindEval (sys : S → PdaRequest → Outcome S ZeroFindReply U T)
    (panic : S → SearchPanic → Outcome S Empty U T) (before : S) (inputs : PdaInputs) :
    Outcome S (Value × UInt8) U T :=
  Outcome.bind (Outcome.map zeroFindDecode (sys before (zeroFindRequest inputs)))
    (Address.Syscall.finishOutcome panic)

theorem zeroFindRun_ofFunction (sys : S → PdaRequest → Outcome S ZeroFindReply U T)
    (panic : S → SearchPanic → Outcome S Empty U T) (before : S) (inputs : PdaInputs)
    (o : Outcome S (Value × UInt8) U T) :
    zeroFindRun (zeroFindIndex sys panic) before inputs o ↔ zeroFindEval sys panic before inputs =
      o := by
  unfold zeroFindRun zeroFindEval Callback.bind
  constructor
  · rintro ⟨actual, step, rest⟩
    have mapped := (Callback.map_ofFunction zeroFindDecode sys before (zeroFindRequest inputs)
      actual).mp step
    rw [mapped]
    cases actual with
    | returned result after =>
      exact (Address.Syscall.finishFind_ofFunction panic result after o).mp rest
    | unwound reason after => exact rest.symm
    | terminated reason => exact rest.symm
  · intro h
    refine ⟨_, (Callback.map_ofFunction zeroFindDecode sys before (zeroFindRequest inputs) _).mpr
      rfl, ?_⟩
    cases actual : Outcome.map zeroFindDecode (sys before (zeroFindRequest inputs)) with
    | returned result after =>
      rw [actual] at h
      exact (Address.Syscall.finishFind_ofFunction panic result after o).mpr h
    | unwound reason after => rw [actual] at h; exact h.symm
    | terminated reason => rw [actual] at h; exact h.symm

theorem zeroDerivedRun_ofFunction {Args : Type} (inputs : Args → PdaInputs)
    (sys : S → PdaRequest → Outcome S ZeroFindReply U T)
    (panic : S → SearchPanic → Outcome S Empty U T) (before : S) (args : Args)
    (o : Outcome S Value U T) :
    zeroDerivedRun inputs (zeroFindIndex sys panic) before args o ↔
      Outcome.map Prod.fst (zeroFindEval sys panic before (inputs args)) = o := by
  unfold zeroDerivedRun Callback.map
  constructor
  · rintro ⟨actual, step, rest⟩
    rw [(zeroFindRun_ofFunction sys panic before (inputs args) actual).mp step]
    exact rest
  · intro h
    exact ⟨_, (zeroFindRun_ofFunction sys panic before (inputs args) _).mpr rfl, h⟩

abbrev uninitFindIndex (sys : S → PdaRequest → Outcome S PdaReply U T)
    (panic : S → SearchPanic → Outcome S Empty U T) : UninitFindIndex :=
  ⟨⟨S, U, T⟩, Callback.ofFunction sys, Callback.ofFunction panic⟩

theorem uninitDerivedRun_ofFunction {Args : Type} (inputs : Args → PdaInputs)
    (sys : S → PdaRequest → Outcome S PdaReply U T)
    (panic : S → SearchPanic → Outcome S Empty U T) (before : S) (args : Args)
    (o : Outcome S Value U T) :
    uninitDerivedRun inputs (uninitFindIndex sys panic) before args o ↔
      (Address.Syscall.findOutcome panic (sys before (pdaRequest (inputs args)))).map
        (Outcome.map Prod.fst) = some o := by
  unfold uninitDerivedRun Callback.map
  constructor
  · rintro ⟨actual, step, rest⟩
    rw [(Address.Syscall.findRun_ofFunction sys panic before (inputs args) actual).mp step]
    exact congrArg some rest
  · intro h
    obtain ⟨actual, result, mapped⟩ := Option.map_eq_some_iff.mp h
    exact ⟨actual, (Address.Syscall.findRun_ofFunction sys panic before (inputs args) actual).mpr
      result, mapped⟩

abbrev seedIndex (hash : S → List Solanalib.Runtime.Bytes → Outcome S Value U T) : SeedIndex :=
  ⟨⟨S, U, T⟩, Callback.ofFunction hash⟩

def seedEval (hash : S → List Solanalib.Runtime.Bytes → Outcome S Value U T) (before : S) (args :
  SeedInputs) :
    Outcome S (Except Error Value) U T :=
  match seedError args with
  | some error => .returned (.error error) before
  | none => Outcome.map Except.ok (hash before (seedSlices args))

theorem seedRun_ofFunction (hash : S → List Solanalib.Runtime.Bytes → Outcome S Value U T)
    (before : S) (args : SeedInputs) (o : Outcome S (Except Error Value) U T) :
    seedRun (seedIndex hash) before args o ↔ seedEval hash before args = o := by
  unfold seedRun seedEval
  cases seedError args with
  | some error => exact eq_comm
  | none => exact Callback.map_ofFunction Except.ok hash before (seedSlices args) o

end Evaluation
end SolanalibTest.Conformance.Library.Families.AddressProfiles
