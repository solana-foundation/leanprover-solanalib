/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.PinocchioAccountResize
public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.PinocchioAccount

structure ZeroRequest where
  account : Handle
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

/-- The mathematical memory effect of sol_memset_ on the requested account
range. Address provenance, range admission and syscall binding are separate. -/
def zeroRange (state : State) (request : ZeroRequest) : State :=
  let data := state.data request.account
  replaceData state request.account { data with
    backing := Solanalib.Runtime.writeAt data.backing request.offset (List.replicate request.length
      0) }

/-- The source commits data_len and resize_delta before calling sol_memset_. -/
def resizeBeforeZero (state : State) (args : Handle × Nat) : State :=
  let data := state.data args.1
  replaceData state args.1 { (data.resize args.2) with backing := data.backing }

def resizeZeroRequest (state : State) (args : Handle × Nat) : ZeroRequest :=
  ⟨args.1, (state.data args.1).dataLen, args.2 - (state.data args.1).dataLen⟩

def resizeCallsZero (state : State) (args : Handle × Nat) : Bool :=
  match (resize state args).1 with
  | .ok () => decide ((state.data args.1).dataLen < args.2)
  | .error _ => false

/-- The memory primitive may terminate and has no C-ABI unwind. A normal
return has the exact range-write effect; auxiliary runtime state is retained. -/
structure ResizeIndex where
  Aux : Type
  Terminal : Type
  zero : Callback.Run (State × Aux) ZeroRequest Unit Empty Terminal
  zeroCorrect : ∀ before request after, zero before request (.returned () after) →
    after.1 = zeroRange before.1 request

abbrev ResizeIndex.World (index : ResizeIndex) := State × index.Aux

def zeroOutcome (index : ResizeIndex)
    (produced : Outcome index.World Unit Empty index.Terminal) :
    Outcome index.World (Except ProgramError.Value Unit) Empty index.Terminal :=
  Outcome.map (fun _ => .ok ()) produced

/-- Return without a syscall on errors, unchanged size and shrink. Successful
growth reaches the actual zeroing provider after the two header writes. -/
def resizeRunAt (index : ResizeIndex) (before : index.World) (args : Handle × Nat)
    (outcome : Outcome index.World (Except ProgramError.Value Unit) Empty index.Terminal) : Prop :=
  if resizeCallsZero before.1 args then
    ∃ produced, index.zero (resizeBeforeZero before.1 args, before.2)
      (resizeZeroRequest before.1 args) produced ∧ outcome = zeroOutcome index produced
  else outcome = .returned (resize before.1 args).1 ((resize before.1 args).2, before.2)

def zeroEffect (index : ResizeIndex) (before : index.World) (request : ZeroRequest) :
    Outcome index.World Unit Empty index.Terminal → Prop
  | .returned _ after => after.1 = zeroRange before.1 request
  | .unwound reason _ => nomatch reason
  | .terminated _ => True

def resizeCallContract (index : ResizeIndex) :
    Solanalib.Contracts.Model index.World (Handle × Nat) (Except ProgramError.Value Unit) Empty
      index.Terminal where
  requires := fun before args => DataPresent before.1 args.1
  post := fun before args outcome =>
    if resizeCallsZero before.1 args then
      Borrow.replaceCell before.1.1 (before.1.field args.1 .data)
        (.data { ((before.1.data args.1).resize args.2) with backing := (before.1.data
          args.1).backing }) =
          (.ok (), (resizeBeforeZero before.1 args).1) ∧
      ∃ produced, index.zero (resizeBeforeZero before.1 args, before.2)
        (resizeZeroRequest before.1 args) produced ∧
        zeroEffect index (resizeBeforeZero before.1 args, before.2) (resizeZeroRequest before.1
          args) produced ∧
        outcome = zeroOutcome index produced
    else outcome = .returned (resize before.1 args).1 ((resize before.1 args).2, before.2) ∧
      resizeContract.ensures before.1 args (resize before.1 args).1 (resize before.1 args).2

def resizeFamily : Family where
  Index := ResizeIndex
  State := ResizeIndex.World
  Args := fun _ => Handle × Nat
  Value := fun _ => Except ProgramError.Value Unit
  Unwind := fun _ => Empty
  Terminal := ResizeIndex.Terminal
  contract := resizeCallContract

def resizeCallRun : FamilyRun resizeFamily := resizeRunAt

theorem resizeCall_reference : FamilyReference resizeFamily resizeCallRun := by
  intro index before args outcome ready step
  change resizeRunAt index before args outcome at step
  change (resizeCallContract index).post before args outcome
  unfold resizeRunAt at step
  unfold resizeCallContract
  split at step <;> rename_i branch
  · simp only [branch]
    refine ⟨replaceData_success ready _, ?_⟩
    obtain ⟨produced, called, finished⟩ := step
    refine ⟨produced, called, ?_, finished⟩
    cases produced with
    | returned value after => cases value; exact index.zeroCorrect _ _ _ called
    | unwound reason _ => cases reason
    | terminated _ => trivial
  · simp only [branch]
    exact ⟨step, resize_reference before.1 args ready⟩

def resizeCallSample : ResizeIndex where
  Aux := Unit
  Terminal := Unit
  zero := Callback.ofFunction (fun before request => .returned () (zeroRange before.1 request,
    before.2))
  zeroCorrect := by intro before request after called; cases called; rfl

theorem resizeCall_hasExecution : FamilyHasExecution resizeFamily resizeCallRun resizeCallSample :=
  by
  let before : resizeCallSample.World := (sampleState, ())
  let args : Handle × Nat := (sampleHandle, 4)
  let after := (zeroRange (resizeBeforeZero sampleState args) (resizeZeroRequest sampleState args),
    ())
  refine ⟨before, args, .returned (.ok ()) after, ⟨sampleInput.data, rfl⟩, ?_⟩
  change resizeRunAt resizeCallSample before args (.returned (.ok ()) after)
  have growth : resizeCallsZero before.1 args = true := by decide
  rw [resizeRunAt, growth]
  exact ⟨.returned () after, rfl, rfl⟩

/-- A terminating zero primitive gives a terminating resize; the wrapper cannot
invent Ok(()) after it. The prerequisite is the same checked growth branch. -/
theorem resize_terminates (index : ResizeIndex) (before : index.World) (args : Handle × Nat)
    (growth : resizeCallsZero before.1 args = true) (reason : index.Terminal)
    (called : index.zero (resizeBeforeZero before.1 args, before.2)
      (resizeZeroRequest before.1 args) (.terminated reason)) :
    resizeRunAt index before args (.terminated reason) := by
  rw [resizeRunAt, growth]
  exact ⟨.terminated reason, called, rfl⟩

end Solanalib.Specs.Core.PinocchioAccount
