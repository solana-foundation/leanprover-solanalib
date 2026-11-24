/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoSdk

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountInfoSdk

/-- The legacy realloc argument. The newer resize fixes `zeroInit` to true. -/
structure ResizeArgs where
  info : AccountInfo.Value
  newLen : Nat
  zeroInit : Bool
  deriving DecidableEq, Repr

/-- A reached memory syscall may terminate; it cannot unwind across its C ABI.
The terminal exit intentionally has no invented post-state or guard release. -/
inductive ResizeTerminal where
  | zeroing
  deriving DecidableEq, Repr

/-- Source-level preparation stops at the reached zeroing call. Its state
already contains the new serialized length and local slice, and the exclusive
data guard is still live. -/
inductive ResizeStage where
  | finished (result : Except ProgramError.Value Unit) (state : State)
  | zero (guard : Borrow.Guard) (oldLen increase : Nat) (state : State)
  | malformed
  deriving Repr

def releaseData (state : State) (guard : Borrow.Guard) : State :=
  { state with borrow := (Borrow.release state.borrow guard).2 }

/-- Updating the shared slice preserves all backing bytes, including the
truncated tail. The subsequent zeroing call is a separate stage. -/
def resizeStorage (state : State) (info : AccountInfo.Value) (buffer : Buffer)
    (bytes : _root_.Solanalib.Runtime.Bytes) (newLen : Nat) : State :=
  let backing := bytes ++ buffer.spare
  { state with
    borrow := (Borrow.replaceCell state.borrow info.data (.data (backing.take newLen))).2
    buffers := state.buffers.set info.data.cell (some {
      buffer with serializedLen := newLen, spare := backing.drop newLen }) }

/-- Error order is borrow, unchanged-length success, then growth from the
original serialized length. No metadata writability check is inserted. -/
def prepareResize (state : State) (args : ResizeArgs) : ResizeStage :=
  let (acquired, borrowed) := Borrow.acquire state.borrow args.info.data .exclusive .whole
  match acquired with
  | .error .conflict | .error .sharedLimit =>
    .finished (.error .accountBorrowFailed) { state with borrow := borrowed }
  | .error _ => .malformed
  | .ok guard =>
    match Borrow.current borrowed guard with
    | .ok (.whole, .data bytes) =>
      let during := { state with borrow := borrowed }
      if args.newLen = bytes.length then .finished (.ok ()) (releaseData during guard)
      else match state.buffer args.info.data with
      | none => .malformed
      | some buffer =>
        if args.newLen - buffer.originalLen > 10240 then
          .finished (.error .invalidRealloc) (releaseData during guard)
        else
          let changed := resizeStorage during args.info buffer bytes args.newLen
          if args.zeroInit && bytes.length < args.newLen then
            .zero guard bytes.length (args.newLen - bytes.length) changed
          else .finished (.ok ()) (releaseData changed guard)
    | _ => .malformed

/-- A successful zeroing dependency overwrites only the newly exposed tail.
Spare backing outside that slice remains unchanged; guard destruction follows. -/
def completeZero (state : State) (guard : Borrow.Guard) (oldLen increase : Nat) : State :=
  match Borrow.current state.borrow guard with
  | .ok (.whole, .data bytes) =>
    releaseData { state with borrow :=
      (Borrow.write state.borrow guard (.data (bytes.take oldLen ++ List.replicate increase 0))).2 }
      guard
  | _ => state

/-- Exact finite reference outcomes, with the terminal
possibility of the memory operation retained only when zeroing is actually reached. -/
def resizeReference (state : State) (args : ResizeArgs) :
    Outcome State (Except ProgramError.Value Unit) Empty ResizeTerminal → Prop := fun outcome =>
  match prepareResize state args with
  | .malformed => False
  | .finished result after => outcome = .returned result after
  | .zero guard oldLen increase during =>
    outcome = .returned (.ok ()) (completeZero during guard oldLen increase) ∨
      outcome = .terminated .zeroing

/-- Compute the ordinary finite return, when all reached memory operations
return. This does not remove the terminal alternative of the primary reference. -/
def resizeNormal (state : State) (args : ResizeArgs) :
    Option (Except ProgramError.Value Unit × State) :=
  match prepareResize state args with
  | .malformed => none
  | .finished result after => some (result, after)
  | .zero guard oldLen increase during =>
    some (.ok (), completeZero during guard oldLen increase)

theorem resize_returned_iff (state : State) (args : ResizeArgs)
    (result : Except ProgramError.Value Unit) (after : State) :
    resizeReference state args (.returned result after) ↔
      resizeNormal state args = some (result, after) := by
  unfold resizeReference resizeNormal
  cases prepareResize state args <;> simp [eq_comm, and_comm]

/-- The selected typed cell and source-ordered admission for additional
storage. An existing lease or unchanged length needs no original-length header
or spare region. Capacity is required only after successful acquisition, a
changed length and the SDK growth check. It gives the represented slice its
requested length; pointer layout and legal access remain source bindings. -/
def ResizeReady (state : State) (args : ResizeArgs) : Prop :=
  state.borrow.Valid ∧ ∃ bytes policy,
    state.borrow.lookupCell args.info.data = some ⟨.data bytes, policy⟩ ∧
    (state.borrow.exclusiveCount args.info.data = 0 →
      state.borrow.sharedCount args.info.data = 0 → args.newLen ≠ bytes.length →
      ∃ buffer, state.buffer args.info.data = some buffer ∧
        (args.newLen - buffer.originalLen ≤ 10240 →
          args.newLen ≤ bytes.length + buffer.spare.length))

def ResizeStage.Valid : ResizeStage → Prop
  | .malformed => True
  | .finished _ state | .zero _ _ _ state => state.borrow.Valid

theorem releaseData_valid (state : State) (guard : Borrow.Guard)
    (valid : state.borrow.Valid) : (releaseData state guard).borrow.Valid :=
  Borrow.release_valid valid guard

theorem resizeStorage_valid (state : State) (info : AccountInfo.Value) (buffer : Buffer)
    (bytes : _root_.Solanalib.Runtime.Bytes) (newLen : Nat) (valid : state.borrow.Valid) :
    (resizeStorage state info buffer bytes newLen).borrow.Valid :=
  Borrow.replaceCell_valid valid info.data _

theorem prepareResize_valid (state : State) (args : ResizeArgs) (valid : state.borrow.Valid) :
    (prepareResize state args).Valid := by
  have acquiredValid := Borrow.acquire_valid valid args.info.data .exclusive AccountInfo.View.whole
  cases acquired : Borrow.acquire state.borrow args.info.data .exclusive AccountInfo.View.whole with
  | mk result borrowed =>
    have duringValid : borrowed.Valid := by simpa only [acquired] using acquiredValid
    cases result with
    | error error => cases error <;> simp [prepareResize, acquired, ResizeStage.Valid, duringValid]
    | ok guard =>
      simp only [prepareResize, acquired]
      split
      · rename_i bytes _
        split
        · exact releaseData_valid _ guard duringValid
        · split
          · trivial
          · rename_i buffer _
            split
            · exact releaseData_valid _ guard duringValid
            · have changedValid := resizeStorage_valid { state with borrow := borrowed }
                args.info buffer bytes args.newLen duringValid
              split
              · exact changedValid
              · exact releaseData_valid _ guard changedValid
      · trivial

theorem completeZero_valid (state : State) (guard : Borrow.Guard) (oldLen increase : Nat)
    (valid : state.borrow.Valid) : (completeZero state guard oldLen increase).borrow.Valid := by
  unfold completeZero
  split
  · exact releaseData_valid _ guard (Borrow.write_valid valid guard _)
  · exact valid

/-- Every normally returned resize releases its temporary data guard and
preserves the common borrow protocol. The exact graph retains all aliases. -/
def resizeContract :
    Solanalib.Contracts.Model State ResizeArgs (Except ProgramError.Value Unit) Empty
      ResizeTerminal where
  requires := ResizeReady
  post := fun before args outcome => resizeReference before args outcome ∧
    match outcome with
    | .returned _ after => after.borrow.Valid
    | .unwound impossible _ => nomatch impossible
    | .terminated _ => True

theorem resize_holds : resizeContract.Holds resizeReference := by
  intro state args outcome ready step
  refine ⟨step, ?_⟩
  have valid := prepareResize_valid state args ready.1
  cases stage : prepareResize state args with
  | malformed => simp [resizeReference, stage] at step
  | finished result after =>
    have same : outcome = .returned result after := by simpa [resizeReference, stage] using step
    subst outcome
    simpa [stage, ResizeStage.Valid] using valid
  | zero guard oldLen increase during =>
    have same := step
    simp only [resizeReference, stage] at same
    rcases same with same | same
    · subst outcome
      exact completeZero_valid _ _ _ _ (by simpa [stage, ResizeStage.Valid] using valid)
    · subst outcome
      trivial

/-- A represented selected data cell and buffer exclude the mathematical
malformed branch. This supplies a finite model outcome without assuming that
the real memory syscall terminates normally. -/
theorem prepareResize_not_malformed (state : State) (args : ResizeArgs)
    (ready : ResizeReady state args) : prepareResize state args ≠ .malformed := by
  obtain ⟨_, bytes, policy, present, storage⟩ := ready
  cases acquired : Borrow.acquire state.borrow args.info.data .exclusive AccountInfo.View.whole with
  | mk result borrowed =>
    cases result with
    | error error =>
      simp only [Borrow.acquire, present] at acquired
      split at acquired
      · cases acquired
        simp [prepareResize, Borrow.acquire, *]
      · cases acquired
    | ok guard =>
      have current := Borrow.acquire_current acquired present
      have free : state.borrow.exclusiveCount args.info.data = 0 ∧
          state.borrow.sharedCount args.info.data = 0 := by
        by_cases busy : state.borrow.exclusiveCount args.info.data ≠ 0 ∨
            state.borrow.sharedCount args.info.data ≠ 0
        · simp [Borrow.acquire, present, busy] at acquired
        · by_cases exclusive : state.borrow.exclusiveCount args.info.data = 0
          · by_cases shared : state.borrow.sharedCount args.info.data = 0
            · exact ⟨exclusive, shared⟩
            · exact False.elim (busy (Or.inr shared))
          · exact False.elim (busy (Or.inl exclusive))
      by_cases unchanged : args.newLen = bytes.length
      · simp [prepareResize, acquired, current, unchanged]
      · obtain ⟨buffer, backing, _⟩ := storage free.1 free.2 unchanged
        simp only [prepareResize, acquired, current, backing, unchanged, ↓reduceIte]
        split
        · simp
        · split <;> simp

theorem resize_exists (state : State) (args : ResizeArgs) (ready : ResizeReady state args) :
    ∃ outcome, resizeReference state args outcome := by
  have good := prepareResize_not_malformed state args ready
  cases stage : prepareResize state args with
  | malformed => exact False.elim (good stage)
  | finished result after => exact ⟨.returned result after, by simp [resizeReference, stage]⟩
  | zero guard oldLen increase during =>
    exact ⟨.returned (.ok ()) (completeZero during guard oldLen increase),
      by simp [resizeReference, stage]⟩

/-- The capacity premise gives the new local slice its exact requested length,
not a truncated take of an undersized allocation. -/
theorem resizeStorage_length (state : State) (info : AccountInfo.Value) (buffer : Buffer)
    (bytes : _root_.Solanalib.Runtime.Bytes) (newLen : Nat) (policy : Borrow.Policy)
    (present : state.borrow.lookupCell info.data = some ⟨.data bytes, policy⟩)
    (capacity : newLen ≤ bytes.length + buffer.spare.length) :
    ∃ resized, (resizeStorage state info buffer bytes newLen).borrow.lookupCell info.data =
      some ⟨.data resized, policy⟩ ∧ resized.length = newLen := by
  refine ⟨(bytes ++ buffer.spare).take newLen, Borrow.replaceCell_lookup present _, ?_⟩
  simp only [List.length_take, List.length_append]
  exact Nat.min_eq_left capacity

/-- Original-length accounting survives every successful storage resize. -/
theorem resizeStorage_originalLen (state : State) (info : AccountInfo.Value) (buffer : Buffer)
    (bytes : _root_.Solanalib.Runtime.Bytes) (newLen : Nat)
    (present : state.buffer info.data = some buffer) :
    ((resizeStorage state info buffer bytes newLen).buffer info.data).map Buffer.originalLen =
      some buffer.originalLen := by
  have bound : info.data.cell < state.buffers.length := by
    by_cases h : info.data.cell < state.buffers.length
    · exact h
    · simp [State.buffer, List.getElem?_eq_none (Nat.le_of_not_lt h)] at present
  simp [resizeStorage, State.buffer, List.getElem?_set_self bound]

def sampleResizeArgs : ResizeArgs := ⟨AccountInfo.sampleInfo, 5, true⟩

theorem sample_resizeReady : ResizeReady sample sampleResizeArgs := by
  refine ⟨AccountInfo.sample_valid.2.1, [10, 20, 30], AccountInfo.sampleProfile.policy, rfl, ?_⟩
  intro _ _ _
  exact ⟨⟨3, 3, [40, 50, 60]⟩, rfl, by intro _; decide⟩

end Solanalib.Specs.Core.AccountInfoSdk
