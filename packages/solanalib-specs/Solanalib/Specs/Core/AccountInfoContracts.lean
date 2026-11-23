/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfo
public import Solanalib.Specs.Core.BorrowValid

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountInfo

/-- A checked data borrow needs a protocol-valid world and a current data cell.
Target widths and the other AccountInfo cell are not premises of these results. -/
def DataBorrowReady (state : State) (info : Value) : Prop :=
  state.Valid ∧ ∃ bytes policy, state.lookupCell info.data = some ⟨.data bytes, policy⟩

/-- Each getter needs only the selected cell and a defined typed projection.
This excludes the malformed mathematical path without constraining other cells. -/
def ObservationReady (observation : Observation) (state : State) (info : Value) : Prop :=
  ∃ cell value, state.lookupCell (observation.handle info) = some cell ∧
    observation.project cell.value = some value

/-- A source-shaped AccountInfo supplies the smaller checked-borrow premise. -/
theorem Valid.dataBorrowReady {profile : Profile} {state : State} {info : Value}
    (valid : Valid profile state info) : DataBorrowReady state info := by
  obtain ⟨bytes, present, _⟩ := valid.2.2.2.2
  exact ⟨valid.2.1, bytes, profile.policy, present⟩

/-- A source-shaped AccountInfo supplies either selected getter projection. -/
theorem Valid.observationReady {profile : Profile} {state : State} {info : Value}
    (valid : Valid profile state info) (observation : Observation) :
    ObservationReady observation state info := by
  cases observation with
  | lamports =>
    obtain ⟨balance, present⟩ := valid.2.2.2.1
    exact ⟨_, balance.toNat, present, rfl⟩
  | dataLen =>
    obtain ⟨bytes, present, _⟩ := valid.2.2.2.2
    exact ⟨_, bytes.length, present, rfl⟩

/-- Borrow contracts retain the exact operation, preserve protocol validity,
and expose current typed data through every successfully returned guard. -/
def dataBorrowContract (mode : Borrow.Mode) :
    Solanalib.Contracts.Model State Args (Except ProgramError.Value Borrow.Guard) :=
  .returning (fun state args => DataBorrowReady state args.info)
    (fun before args result after =>
      tryBorrow mode args.info.data before = (result, after) ∧ after.Valid ∧
        match result with
        | .ok guard => ∃ bytes, Borrow.current after guard = .ok (.whole, .data bytes)
        | .error _ => True)

/-- Unchecked observations can panic on conflict or shared-counter saturation.
An ordinary error return is not an outcome of this contract. -/
def observationContract (observation : Observation) :
    Solanalib.Contracts.Model State Args Nat Panic Panic where
  requires := fun state args => ObservationReady observation state args.info
  post := observePost observation

/-- Clone preserves metadata, both aliases and the borrow world. Rust reference
count overflow and allocation-level representation are separate bindings. -/
def cloneContract : Solanalib.Contracts.Model State Args Value :=
  .returning (fun _ _ => True)
    (fun before args value after => value = args.info ∧ after = before)

def cloneReference (state : State) (args : Args) : Value × State := (clone args.info, state)

theorem dataBorrowReference_realizes (mode : Borrow.Mode) :
    (dataBorrowContract mode).RealizedBy
      (fun state args => tryBorrow mode args.info.data state) := by
  intro state args ready
  obtain ⟨valid, bytes, policy, present⟩ := ready
  have invariant := Borrow.acquire_valid valid args.info.data mode View.whole
  cases acquired : Borrow.acquire state args.info.data mode View.whole with
  | mk result after =>
    have afterValid : after.Valid := by simpa only [acquired] using invariant
    cases result with
    | error error =>
      simp only [tryBorrow, acquired, Except.mapError]
      exact ⟨by simp [tryBorrow, acquired, Except.mapError], afterValid, trivial⟩
    | ok guard =>
      simp only [tryBorrow, acquired, Except.mapError]
      exact ⟨by simp [tryBorrow, acquired, Except.mapError], afterValid,
        bytes, Borrow.acquire_current acquired present⟩

theorem observationReference_holds (observation : Observation) :
    (observationContract observation).Holds (observeReference observation) := by
  intro _ _ _ _ step
  exact step

theorem cloneReference_realizes : cloneContract.RealizedBy cloneReference := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

end Solanalib.Specs.Core.AccountInfo
