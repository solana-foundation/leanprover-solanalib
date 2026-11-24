/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.PinocchioAccount

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.PinocchioAccount

def i32Max : Nat := 2147483647
def maxIncrease : Nat := 10240

/-- A typed data cell; pointer layout and integer-width obligations are kept
separate from the precondition of the mathematical operation. -/
def DataPresent (state : State) (handle : Handle) : Prop :=
  ∃ data, state.content handle .data = some (.data data)

def replaceData (state : State) (handle : Handle) (data : Data) : State :=
  ((Borrow.replaceCell state.1 (state.field handle .data) (.data data)).2, state.2)

/-- Borrow conflict precedes conversion, unchanged-length success precedes
growth accounting, and only growth clears physical bytes. -/
def resize (state : State) (args : Handle × Nat) : Except ProgramError.Value Unit × State :=
  let data := state.data args.1
  if !available state args.1 .data .exclusive then (.error .accountBorrowFailed, state)
  else if i32Max < args.2 then (.error .invalidRealloc, state)
  else if args.2 = data.dataLen then (.ok (), state)
  else if (maxIncrease : Int) < data.resizeDelta + ((args.2 : Int) - data.dataLen) then
    (.error .invalidRealloc, state)
  else (.ok (), replaceData state args.1 (data.resize args.2))

def resizeContract : Solanalib.Contracts.Model State (Handle × Nat) (Except ProgramError.Value
  Unit) :=
  .returning (fun before args => DataPresent before args.1)
    (fun before args result after =>
      if !available before args.1 .data .exclusive then
        result = .error .accountBorrowFailed ∧ after = before
      else if i32Max < args.2 then result = .error .invalidRealloc ∧ after = before
      else if args.2 = (before.data args.1).dataLen then result = .ok () ∧ after = before
      else if (maxIncrease : Int) < (before.data args.1).resizeDelta +
          ((args.2 : Int) - (before.data args.1).dataLen) then
        result = .error .invalidRealloc ∧ after = before
      else result = .ok () ∧ after.2 = before.2 ∧
        Borrow.replaceCell before.1 (before.field args.1 .data)
          (.data ((before.data args.1).resize args.2)) = (.ok (), after.1))

theorem replaceData_success {state : State} {handle : Handle}
    (present : DataPresent state handle) (data : Data) :
    Borrow.replaceCell state.1 (state.field handle .data) (.data data) =
      (.ok (), (replaceData state handle data).1) := by
  obtain ⟨old, foundData⟩ := present
  unfold State.content at foundData
  cases found : state.1.lookupCell (state.field handle .data) with
  | none => simp [found] at foundData
  | some cell => simp [replaceData, Borrow.replaceCell, found]

theorem resize_reference : resizeContract.RealizedBy resize := by
  intro before args ready
  have update := replaceData_success ready ((before.data args.1).resize args.2)
  simp only [resizeContract, Solanalib.Contracts.Model.ensures,
    Solanalib.Contracts.Model.returning, resize]
  split <;> rename_i first
  · exact ⟨rfl, rfl⟩
  · split <;> rename_i second
    · exact ⟨rfl, rfl⟩
    · split <;> rename_i third
      · exact ⟨rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl, update⟩

theorem resize_satisfiable : resizeContract.Satisfiable :=
  ⟨sampleState, (sampleHandle, 2), sampleInput.data, rfl⟩

/-- The loader-consistent length counter discharges the actual i32 additions
and subtraction. It is a source-representation lemma, not an unused premise
on the mathematical resize contract. -/
theorem resize_arithmetic (data : Data) (newLen : Nat)
    (currentBound : data.dataLen ≤ i32Max) (entryBound : data.entryLen ≤ i32Max)
    (counter : data.resizeDelta = (data.dataLen : Int) - data.entryLen)
    (newBound : newLen ≤ i32Max) :
    -2147483648 ≤ (newLen : Int) - data.dataLen ∧
    (newLen : Int) - data.dataLen ≤ 2147483647 ∧
    -2147483648 ≤ data.resizeDelta + ((newLen : Int) - data.dataLen) ∧
    data.resizeDelta + ((newLen : Int) - data.dataLen) ≤ 2147483647 := by
  unfold i32Max at currentBound entryBound newBound
  omega

/-- The recorded counter continues to measure growth from entry. -/
theorem Data.resize_counter (data : Data) (newLen : Nat)
    (counter : data.resizeDelta = (data.dataLen : Int) - data.entryLen) :
    (data.resize newLen).resizeDelta = (newLen : Int) - data.entryLen := by
  simp only [Data.resize]
  omega

/-- Shrinking changes no allocated byte, including the hidden suffix. -/
theorem Data.shrink_backing (data : Data) (newLen : Nat) (shrinks : newLen ≤ data.dataLen) :
    (data.resize newLen).backing = data.backing := by
  simp [Data.resize, Nat.not_lt.mpr shrinks]

/-- Growing inside the admitted allocation clears the entire newly visible
range, including bytes that were visible before an earlier shrink. -/
theorem Data.grow_zeroes (data : Data) (newLen : Nat)
    (grows : data.dataLen < newLen) (capacity : newLen ≤ data.backing.length) :
    Solanalib.Runtime.slice (data.resize newLen).backing data.dataLen (newLen - data.dataLen) =
      List.replicate (newLen - data.dataLen) 0 := by
  have fits : data.dataLen + (List.replicate (newLen - data.dataLen) (0 : UInt8)).length ≤
      data.backing.length := by simp only [List.length_replicate]; omega
  simpa [Data.resize, grows] using Solanalib.Runtime.slice_writeAt_self fits

end Solanalib.Specs.Core.PinocchioAccount
