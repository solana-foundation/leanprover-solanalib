/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoFacts
public import Solanalib.Specs.Core.AnchorAccount
public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorViewsLamports

/-- the default getter of Lamports invokes the actual AsRef implementation before
reading the current account cell. AsRef may mutate that cell, choose another
alias, unwind or terminate. The panic dependency represents the failure policy of RefCell::borrow,
not a Result::Err or an assumed successful borrow. -/
structure Types where
  Aux : Type
  Input : Type
  Unwind : Type
  Terminal : Type
  asRef : Callback.Run (AccountInfo.State × Aux) Input AccountInfo.Value Unwind Terminal
  panic : Callback.Run (AccountInfo.State × Aux) AccountInfo.Panic Empty Unwind Terminal

/-- Read current lamports using the existing acquisition/read/release model.
The returned account and state of the callback determine both value and conflict. -/
def read (types : Types) :
    Callback.Run (AccountInfo.State × types.Aux) AccountInfo.Value Nat
      types.Unwind types.Terminal :=
  fun before info final =>
    match AccountInfo.observe .lamports before.1 info with
    | (.value value, after) => final = .returned value (after, before.2)
    | (.borrowFailed, after) =>
      Callback.map (fun impossible : Empty => nomatch impossible)
        types.panic (after, before.2) .borrowFailed final
    | (.malformed, _) => False

/-- The source invokes AsRef once and reads only after it returns normally. -/
def run (types : Types) :
    Callback.Run (AccountInfo.State × types.Aux) types.Input Nat
      types.Unwind types.Terminal :=
  Callback.bind types.asRef fun info state => read types state info

/-- Only reached returned references need a currently typed lamports cell.
There is no non-conflict, success, termination or account-data premise. -/
def Ready (types : Types) (before : AccountInfo.State × types.Aux) (args : types.Input) : Prop :=
  ∀ info after, types.asRef before args (.returned info after) →
    AccountInfo.ObservationReady .lamports after.1 info

def family : Family where
  Index := Types
  State := fun types => AccountInfo.State × types.Aux
  Args := Types.Input
  Value := fun _ => Nat
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun types => { requires := Ready types, post := run types }

def reference : FamilyRun family := run

theorem reference_holds : FamilyReference family reference := by
  intro _ _ _ _ _ called
  exact called

/-- The reached typed-cell premise rules out loss of the source continuation
through the malformed helper branch. Borrow conflict remains a real panic. -/
theorem reached_read_defined (types : Types)
    {before after : AccountInfo.State × types.Aux} {args : types.Input}
    (ready : Ready types before args) {info : AccountInfo.Value}
    (called : types.asRef before args (.returned info after)) :
    (AccountInfo.observe .lamports after.1 info).1 ≠ .malformed :=
  AccountInfo.observe_not_malformed .lamports after.1 info (ready info after called)

/-- A returned callback followed by an observed balance yields that balance,
the actual borrow history, and the auxiliary effects of the callback. -/
theorem returned (types : Types)
    {before after : AccountInfo.State × types.Aux} {args : types.Input}
    {info : AccountInfo.Value} {value : Nat} {finished : AccountInfo.State}
    (called : types.asRef before args (.returned info after))
    (observed : AccountInfo.observe .lamports after.1 info = (.value value, finished)) :
    run types before args (.returned value (finished, after.2)) := by
  exact ⟨.returned info after, called, by simp [read, observed]⟩

/-- The closed sample invokes AsRef once, retaining its ordered effect. -/
def sample : Types where
  Aux := List String
  Input := Unit
  Unwind := String
  Terminal := String
  asRef := Callback.ofFunction fun before _ =>
    .returned AccountInfo.sampleInfo (before.1, before.2 ++ ["as_ref"])
  panic := Callback.ofFunction fun before _ => .unwound "borrow failed" before

theorem sample_ready : Ready sample (AccountInfo.sampleState, []) () := by
  intro info after called
  cases called
  exact AccountInfo.Valid.observationReady AccountInfo.sample_valid .lamports

theorem reference_execution : FamilyHasExecution family reference sample := by
  refine ⟨(AccountInfo.sampleState, []), (),
    .returned (40 : Nat) (⟨AccountInfo.sampleState.cells, [none]⟩, ["as_ref"]), sample_ready, ?_⟩
  apply returned sample (info := AccountInfo.sampleInfo) (args := ())
    (before := (AccountInfo.sampleState, []))
    (after := (AccountInfo.sampleState, ["as_ref"])) rfl
  rfl

end Solanalib.Specs.Core.AnchorViewsLamports
