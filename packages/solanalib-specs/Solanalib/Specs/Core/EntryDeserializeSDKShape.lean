/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.EntryDeserializeSDK

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.EntryDeserialize.SDK

/-- An ordinary result of one allocator continuation came from an ordinary allocator reply.
This lemma does not turn termination or missing finite outcomes into successful allocations. -/
theorem allocateThen_returned (index : Index) (before : State index.Aux) (site : Allocation)
    (next : State index.Aux → Option (Outcome (State index.Aux) Result Empty index.Terminal))
    (result : Result) (after : State index.Aux)
    (returned : allocateThen index before site next = some (.returned result after)) :
    ∃ allocator, index.allocate before.allocator ⟨site, before.bytes⟩ =
      some (.returned () allocator) ∧
      next { before with allocator := allocator } = some (.returned result after) := by
  unfold allocateThen at returned
  cases reply : index.allocate before.allocator ⟨site, before.bytes⟩ with
  | none => simp [reply] at returned
  | some outcome =>
    cases outcome with
    | returned value allocator =>
      cases value
      exact ⟨allocator, rfl, by simpa [reply] using returned⟩
    | unwound impossible _ => nomatch impossible
    | terminated reason => simp [reply] at returned

/-- Result views and vector identity do not depend on allocator-private state. -/
theorem process_result (index : Index) (views : Views) (vector : Nat) (slots : List Slot)
    (infos : List Info) (before after : State index.Aux) (result : Result)
    (returned : process index views vector slots infos before = some (.returned result after)) :
    result = ⟨views, vector⟩ := by
  induction slots generalizing infos before with
  | nil => exact (Outcome.returned.inj (Option.some.inj returned)).1.symm
  | cons slot rest induction =>
    cases duplicate : slot.duplicate with
    | some earlier =>
      simp only [process, duplicate] at returned
      cases found : infos[earlier]? with
      | none => simp [found] at returned
      | some info =>
        simp only [found] at returned
        exact induction _ _ returned
    | none =>
      simp only [process, duplicate] at returned
      obtain ⟨allocatedLamports, _, returned⟩ :=
        allocateThen_returned index _ _ _ _ _ returned
      obtain ⟨allocatedData, _, returned⟩ :=
        allocateThen_returned index _ _ _ _ _ returned
      exact induction _ _ returned

/-- The source vector and Rc counters have finite machine widths after a finite prefix.
The `2 * used` bound deliberately permits arbitrary logical handle aliasing in the helper:
a concrete fresh AccountInfo has distinct lamports and data cells, so its actual bound is tighter.
-/
structure Shape {Aux : Type} (vector used length : Nat) (state : State Aux) : Prop where
  bytes : state.bytes.length = length
  present : vector < state.vectors.length
  infos : (state.vectors.getD vector []).length = used
  counts : ∀ count ∈ state.rcStrong, count ≤ 2 * used

theorem counts_set {counts : List Nat} {bound index : Nat}
    (bounded : ∀ count ∈ counts, count ≤ bound) :
    ∀ count ∈ counts.set index (counts.getD index 0 + 1), count ≤ bound + 1 := by
  intro count member
  rcases (List.mem_or_eq_of_mem_set member).symm with same | old
  · subst count
    have value : counts.getD index 0 ≤ bound := by
      cases found : counts[index]? with
      | none => simp [List.getD, found]
      | some value =>
        simpa [List.getD, found] using bounded value (List.mem_of_getElem? found)
    omega
  · exact Nat.le_trans (bounded count old) (by omega)

theorem cloneInfo_counts {Aux : Type} (before : State Aux) (info : Info) (used : Nat)
    (bounded : ∀ count ∈ before.rcStrong, count ≤ 2 * used) :
    ∀ count ∈ (cloneInfo before info).rcStrong, count ≤ 2 * (used + 1) := by
  have once := counts_set (index := info.value.lamports.cell) bounded
  have twice := counts_set (index := info.value.data.cell) once
  simpa [cloneInfo, Nat.mul_add, Nat.add_assoc] using twice

theorem insertCell_counts {Aux : Type} (before : State Aux) (content : AccountInfo.Content)
    (buffer : Option AccountInfoSdk.Buffer) (bound : Nat)
    (positive : 1 ≤ bound) (bounded : ∀ count ∈ before.rcStrong, count ≤ bound) :
    ∀ count ∈ (insertCell before content buffer).2.rcStrong, count ≤ bound := by
  intro count member
  simp only [insertCell, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact bounded count member
  · exact positive

theorem push_length {Aux : Type} (before : State Aux) (vector : Nat) (infos : List Info) :
    (push before vector infos).vectors.length = before.vectors.length := by
  simp [push]

theorem push_infos {Aux : Type} (before : State Aux) (vector : Nat) (infos : List Info)
    (present : vector < before.vectors.length) :
    (push before vector infos).vectors.getD vector [] = infos := by
  simp [push, List.getD, present]

/-- The serialized input allocation keeps its extent, the vector holds every processed
account, and Rc counts stay within twice the number of processed slots. The header bounds
belong to the source geometry of the caller and are used exactly for the original-length writes. -/
theorem process_shape (index : Index) (views : Views) (vector length : Nat) (slots : List Slot)
    (infos : List Info) (used : Nat) (before after : State index.Aux) (result : Result)
    (shape : Shape vector used length before) (infoLength : infos.length = used)
    (headers : ∀ slot ∈ slots, slot.account.offset + 8 ≤ length)
    (returned : process index views vector slots infos before = some (.returned result after)) :
    Shape vector (used + slots.length) length after := by
  induction slots generalizing infos used before with
  | nil =>
    have same : before = after := (Outcome.returned.inj (Option.some.inj returned)).2
    simpa [same] using shape
  | cons slot rest induction =>
    have header := headers slot (by simp)
    have restHeaders : ∀ other ∈ rest, other.account.offset + 8 ≤ length :=
      fun other member => headers other (by simp [member])
    cases duplicate : slot.duplicate with
    | some earlier =>
      simp only [process, duplicate] at returned
      cases found : infos[earlier]? with
      | none => simp [found] at returned
      | some info =>
        simp only [found] at returned
        have step : Shape vector (used + 1) length
            (push (cloneInfo before info) vector (infos ++ [info])) := by
          refine ⟨shape.bytes, ?_, ?_, cloneInfo_counts before info used shape.counts⟩
          · simpa [push, cloneInfo] using shape.present
          · rw [push_infos _ _ _ (by simpa [cloneInfo] using shape.present)]
            simp [infoLength]
        have next := induction _ (used + 1) _ step (by simp [infoLength]) restHeaders returned
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next
    | none =>
      simp only [process, duplicate] at returned
      obtain ⟨allocatedLamports, _, returned⟩ :=
        allocateThen_returned index _ _ _ _ _ returned
      obtain ⟨allocatedData, _, returned⟩ :=
        allocateThen_returned index _ _ _ _ _ returned
      have step := induction _ (used + 1) _ (by
          refine ⟨?_, ?_, ?_, ?_⟩
          · change (overwrite before.bytes (slot.account.offset + 4)
              (Solanalib.Runtime.leBytes 4 slot.account.data.length)).length = length
            rw [overwrite_length _ _ _ (by
              have same := shape.bytes
              simp [Solanalib.Runtime.leBytes]
              omega), shape.bytes]
          · simpa [push, insertCell] using shape.present
          · rw [push_infos _ _ _ (by simpa [insertCell] using shape.present)]
            simp [infoLength]
          · change ∀ count ∈ (before.rcStrong ++ [1]) ++ [1], count ≤ 2 * (used + 1)
            intro count member
            simp only [List.mem_append, List.mem_singleton] at member
            rcases member with (member | rfl) | rfl
            · exact Nat.le_trans (shape.counts count member) (by omega)
            · omega
            · omega
        ) (by simp [infoLength]) restHeaders returned
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step

/-- A fresh account subworld returns one vector with the source count and finite Rc widths.
Other physical caller blocks can be framed by the source representation; freshness here concerns
only the newly constructed SDK objects, not the loader input or the live heap of the allocator. -/
theorem execute_shape (index : Index) (before after : State index.Aux) (result : Result)
    (parsed : Parsed) (parsedBytes : parse before.bytes = some parsed)
    (vectors : before.vectors = []) (counts : before.rcStrong = [])
    (headers : ∀ slot ∈ parsed.slots, slot.account.offset + 8 ≤ before.bytes.length)
    (returned : execute index before = some (.returned result after)) :
    result = ⟨parsed.views, 0⟩ ∧ Shape 0 parsed.slots.length before.bytes.length after := by
  have finish (allocator : index.Aux)
      (processed : process index parsed.views 0 parsed.slots []
        { before with vectors := [[]], allocator := allocator } = some (.returned result after)) :
      result = ⟨parsed.views, 0⟩ ∧ Shape 0 parsed.slots.length before.bytes.length after := by
    refine ⟨process_result index _ _ _ _ _ _ _ processed, ?_⟩
    have initial : Shape 0 0 before.bytes.length
        { before with vectors := [[]], allocator := allocator } := by
      refine ⟨rfl, by change 0 < 1; decide, rfl, ?_⟩
      simp [counts]
    simpa using process_shape index parsed.views 0 before.bytes.length parsed.slots [] 0 _ _ _
      initial rfl headers processed
  unfold execute at returned
  simp [parsedBytes, vectors] at returned
  split at returned
  · exact finish before.allocator returned
  · obtain ⟨allocator, _, processed⟩ := allocateThen_returned index _ _ _ _ _ returned
    apply finish allocator
    simpa [vectors] using processed

end Solanalib.Specs.Core.EntryDeserialize.SDK
