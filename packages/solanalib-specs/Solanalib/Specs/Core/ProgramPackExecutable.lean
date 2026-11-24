/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.ProgramPack

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.ProgramPack

/-- Executable interpretations retain the selected generic callbacks. These
equalities are interface interpretation facts, never SDK body proofs. -/
structure Executable (index : Index) where
  decode : index.State → Solanalib.Runtime.Bytes → Outcome index.State (Except index.Error
    index.Value) index.Unwind index.Terminal
  initialized : index.State → index.Value → Outcome index.State Bool index.Unwind index.Terminal
  drop : index.State → index.Value → Outcome index.State Unit index.Unwind index.Terminal
  double : index.State → index.Unwind → index.Unwind → index.Terminal
  decode_eq : index.unpackUnchecked = Callback.ofFunction decode
  initialized_eq : index.initialized = Callback.ofFunction initialized
  drop_eq : index.dropValue = Callback.ofFunction drop
  double_eq : index.doubleUnwind = fun state first later terminal => terminal = double state first
    later

def dropThen {R : Type} (index : Index) (exec : Executable index) (value : index.Value) :
    Outcome index.State R index.Unwind index.Terminal → Outcome index.State R index.Unwind
      index.Terminal
  | .returned result state => match exec.drop state value with
    | .returned () after => .returned result after
    | .unwound reason after => .unwound reason after
    | .terminated reason => .terminated reason
  | .unwound original state => match exec.drop state value with
    | .returned () after => .unwound original after
    | .unwound later after => .terminated (exec.double after original later)
    | .terminated reason => .terminated reason
  | .terminated reason => .terminated reason

theorem dropThen_graph {R : Type} (index : Index) (exec : Executable index) (value : index.Value)
    (pending final : Outcome index.State R index.Unwind index.Terminal) :
    Owned.cleanup index.doubleUnwind [fun state => index.dropValue state value] pending final ↔
      dropThen index exec value pending = final := by
  cases pending with
  | returned result state =>
    simp only [Owned.cleanup, exec.drop_eq, Callback.ofFunction]
    cases selected : exec.drop state value with
    | returned returnedUnit after => cases returnedUnit; simp [selected, dropThen, eq_comm]
    | unwound reason after => simp [selected, dropThen, eq_comm]
    | terminated reason => simp [selected, dropThen, eq_comm]
  | unwound original state =>
    simp only [Owned.cleanup, exec.drop_eq, Callback.ofFunction]
    cases selected : exec.drop state value with
    | returned returnedUnit after => cases returnedUnit; simp [selected, dropThen, eq_comm]
    | unwound reason after => simp [selected, dropThen, exec.double_eq, eq_comm]
    | terminated reason => simp [selected, dropThen, eq_comm]
  | terminated reason => exact eq_comm

def protect {R : Type} (index : Index) (exec : Executable index) (value : index.Value) :
    Outcome index.State R index.Unwind index.Terminal → Outcome index.State R index.Unwind
      index.Terminal
  | .returned result state => .returned result state
  | .unwound reason state => dropThen index exec value (.unwound reason state)
  | .terminated reason => .terminated reason

theorem protect_graph {R : Type} (index : Index) (exec : Executable index) (value : index.Value)
    (pending final : Outcome index.State R index.Unwind index.Terminal) :
    Owned.onUnwind index.doubleUnwind [fun state => index.dropValue state value] pending final ↔
      protect index exec value pending = final := by
  cases pending with
  | returned result state => exact eq_comm
  | unwound reason state => exact dropThen_graph index exec value _ _
  | terminated reason => exact eq_comm

theorem query_graph (index : Index) (exec : Executable index) (value : index.Value) :
    Owned.protect index.doubleUnwind [fun state => index.dropValue state value]
      (fun before (_ : Unit) => index.initialized before value) =
      Callback.ofFunction (fun before _ => protect index exec value (exec.initialized before
        value)) := by
  funext before args final
  apply propext
  simp only [Owned.protect, exec.initialized_eq, Callback.ofFunction]
  constructor
  · rintro ⟨pending, rfl, cleanup⟩
    exact (protect_graph index exec value _ _).mp cleanup
  · intro result
    exact ⟨_, rfl, (protect_graph index exec value _ _).mpr result⟩

def checkFn (index : Index) (exec : Executable index) (value : index.Value) (before : index.State) :
    Outcome index.State (Except index.Error index.Value) index.Unwind index.Terminal :=
  Outcome.bind (protect index exec value (exec.initialized before value)) fun initialized after =>
    if initialized then .returned (.ok value) after
    else dropThen index exec value (.returned (.error index.uninitializedAccount) after)

theorem check_graph (index : Index) (exec : Executable index) (value : index.Value)
    (before : index.State)
    (outcome : Outcome index.State (Except index.Error index.Value) index.Unwind index.Terminal) :
    check index value before () outcome ↔ checkFn index exec value before = outcome := by
  unfold check
  rw [query_graph index exec value]
  simp only [Callback.bind, Callback.ofFunction]
  constructor
  · rintro ⟨intermediate, rfl, rest⟩
    cases h : protect index exec value (exec.initialized before value) with
    | returned initialized after =>
      simp only [h] at rest
      cases initialized with
      | true => simp only [ite_true] at rest; simpa [checkFn, h] using rest.symm
      | false =>
        simp only [Bool.false_eq_true, ite_false] at rest
        rcases rest with ⟨pending, rfl, cleanup⟩
        simpa [checkFn, h] using (dropThen_graph index exec value _ _).mp cleanup
    | unwound reason after => simp only [h] at rest; simpa [checkFn, h] using rest.symm
    | terminated reason => simp only [h] at rest; simpa [checkFn, h] using rest.symm
  · intro result
    refine ⟨_, rfl, ?_⟩
    cases h : protect index exec value (exec.initialized before value) with
    | returned initialized after =>
      cases initialized with
      | true => simpa [checkFn, h] using result.symm
      | false =>
        refine ⟨_, rfl, ?_⟩
        apply (dropThen_graph index exec value _ _).mpr
        simpa [checkFn, h] using result
    | unwound reason after => simpa [checkFn, h] using result.symm
    | terminated reason => simpa [checkFn, h] using result.symm

def unpackFn (index : Index) (exec : Executable index) (before : index.State) (bytes :
  Solanalib.Runtime.Bytes) :
    Outcome index.State (Except index.Error index.Value) index.Unwind index.Terminal :=
  Outcome.bind (exec.decode before bytes) fun result after => match result with
    | .error error => .returned (.error error) after
    | .ok value => checkFn index exec value after

theorem unpack_graph (index : Index) (exec : Executable index) (before : index.State)
    (bytes : Solanalib.Runtime.Bytes)
    (outcome : Outcome index.State (Except index.Error index.Value) index.Unwind index.Terminal) :
    unpack index before bytes outcome ↔ unpackFn index exec before bytes = outcome := by
  simp only [unpack, Callback.bind, exec.decode_eq, Callback.ofFunction]
  constructor
  · rintro ⟨intermediate, rfl, rest⟩
    cases selected : exec.decode before bytes with
    | returned result after =>
      simp only [selected] at rest
      cases result with
      | error error => simpa [unpackFn, selected] using rest.symm
      | ok value =>
        simpa [unpackFn, selected] using (check_graph index exec value after outcome).mp rest
    | unwound reason after =>
      simp only [selected] at rest; simpa [unpackFn, selected] using rest.symm
    | terminated reason => simp only [selected] at rest; simpa [unpackFn, selected] using rest.symm
  · intro result
    refine ⟨_, rfl, ?_⟩
    cases selected : exec.decode before bytes with
    | returned result' after =>
      cases result' with
      | error error => simpa [unpackFn, selected] using result.symm
      | ok value => apply (check_graph index exec value after outcome).mpr; simpa [unpackFn,
        selected] using result
    | unwound reason after => simpa [unpackFn, selected] using result.symm
    | terminated reason => simpa [unpackFn, selected] using result.symm

end Solanalib.Specs.Core.ProgramPack
