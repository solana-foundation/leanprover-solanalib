/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.ProgramOption
public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.FieldReference
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.ProgramOption

/-- Variant inspection neither moves nor evaluates the payload. -/
def isNone {T : Type} (value : Value T) : Bool := !isSome value

/-- Generic absent-variant inspection. Source memory admission is separate. -/
def isNoneFamily : Family where
  Index := Type
  State := fun _ => Unit
  Args := Value
  Value := fun _ => Bool
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => .returning (fun _ _ => True)
    (fun before value result after => after = before ∧ result = isNone value)

def isNoneRun : FamilyRun isNoneFamily :=
  fun _ => returnsOf fun before value => (isNone value, before)

theorem isNoneReference : FamilyReference isNoneFamily isNoneRun := by
  intro _ before value outcome _ step
  cases outcome with
  | returned result after => cases step; exact ⟨rfl, rfl⟩
  | unwound reason _ | terminated reason => cases reason

abbrev isNoneSample : Type := Empty

theorem isNoneExecution : FamilyHasExecution isNoneFamily isNoneRun isNoneSample := by
  unfold FamilyHasExecution
  dsimp only [isNoneFamily, isNoneSample, Solanalib.Contracts.Model.HasExecution]
  exact ⟨(), .none, .returned true (), trivial, rfl⟩

theorem isNoneSatisfiable : FamilySatisfiable isNoneFamily isNoneSample :=
  isNoneExecution.satisfiable

/-- Reborrow the payload field of the same parent. The Boolean is the observed
discriminant; neither the parent nor the payload is copied or consumed. The source binding must
relate this observation to the actual live shared borrow. -/
def asRef {Parent : Type} (parent : Parent) (present : Bool) :
    Value (FieldReference Parent Unit) :=
  if present then .some ⟨parent, ()⟩ else .none

/-- Retain parent identity in a field reference, rather than a payload snapshot. -/
def asRefFamily : Family where
  Index := Type
  State := fun _ => Unit
  Args := fun Parent => Parent × Bool
  Value := fun Parent => Value (FieldReference Parent Unit)
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = asRef args.1 args.2)

def asRefRun : FamilyRun asRefFamily :=
  fun _ => returnsOf fun before args => (asRef args.1 args.2, before)

theorem asRefReference : FamilyReference asRefFamily asRefRun := by
  intro _ before args outcome _ step
  cases outcome with
  | returned result after => cases step; exact ⟨rfl, rfl⟩
  | unwound reason _ | terminated reason => cases reason

abbrev asRefSample : Type := Nat

theorem asRefExecution : FamilyHasExecution asRefFamily asRefRun asRefSample := by
  unfold FamilyHasExecution
  dsimp only [asRefFamily, asRefSample, Solanalib.Contracts.Model.HasExecution]
  exact ⟨(), (7, true), .returned (.some ⟨7, ()⟩) (), trivial, rfl⟩

theorem asRefSatisfiable : FamilySatisfiable asRefFamily asRefSample :=
  asRefExecution.satisfiable

/-- Conversion changes only the outer enum; a payload is moved exactly once. -/
def toOption {T : Type} : Value T → Option T
  | .none => none
  | .some value => some value

def intoOptionFamily : Family where
  Index := Type
  State := fun _ => Unit
  Args := Value
  Value := Option
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => .returning (fun _ _ => True)
    (fun before value result after => after = before ∧ result = toOption value)

def intoOptionRun : FamilyRun intoOptionFamily :=
  fun _ => returnsOf fun before value => (toOption value, before)

theorem intoOptionReference : FamilyReference intoOptionFamily intoOptionRun := by
  intro _ before value outcome _ step
  cases outcome with
  | returned result after => cases step; exact ⟨rfl, rfl⟩
  | unwound reason _ | terminated reason => cases reason

abbrev intoOptionSample : Type := Nat

theorem intoOptionExecution : FamilyHasExecution intoOptionFamily intoOptionRun
    intoOptionSample := by
  unfold FamilyHasExecution
  dsimp only [intoOptionFamily, intoOptionSample, Solanalib.Contracts.Model.HasExecution]
  exact ⟨(), .some 7, .returned (some 7) (), trivial, rfl⟩

theorem intoOptionSatisfiable : FamilySatisfiable intoOptionFamily intoOptionSample :=
  intoOptionExecution.satisfiable

/-- Types and the actual borrowed payload comparison. Equality may mutate
interior state, unwind, terminate or have no finite outcome. -/
structure EqIndex where
  State : Type
  T : Type
  Unwind : Type
  Terminal : Type
  equal : Callback.Run State (T × T) Bool Unwind Terminal

/-- Derived equality compares payloads only when both discriminants are Some. -/
def eqRun (index : EqIndex) : Callback.Run index.State (Value index.T × Value index.T)
    Bool index.Unwind index.Terminal := fun before args outcome =>
  match args with
  | (.none, .none) => outcome = .returned true before
  | (.some left, .some right) => index.equal before (left, right) outcome
  | _ => outcome = .returned false before

def eqFamily : Family where
  Index := EqIndex
  State := EqIndex.State
  Args := fun index => Value index.T × Value index.T
  Value := fun _ => Bool
  Unwind := EqIndex.Unwind
  Terminal := EqIndex.Terminal
  contract := fun index => ⟨fun _ _ => True, eqRun index⟩

theorem eqReference : FamilyReference eqFamily eqRun := fun _ _ _ _ _ run => run

abbrev eqSample : EqIndex where
  State := Nat
  T := Nat
  Unwind := String
  Terminal := String
  equal := Callback.ofFunction fun before args => .returned (args.1 == args.2) (before + 1)

theorem eqExecution : FamilyHasExecution eqFamily eqRun eqSample := by
  unfold FamilyHasExecution
  dsimp only [eqFamily, eqSample, Solanalib.Contracts.Model.HasExecution]
  exact ⟨0, (.some 7, .some 7), .returned true 1, trivial, rfl⟩

theorem eqSatisfiable : FamilySatisfiable eqFamily eqSample := eqExecution.satisfiable

/-- `contains` compares the borrowed query on the left with the payload on the
right. The source permits different query and payload types. -/
structure ContainsIndex where
  State : Type
  T : Type
  Query : Type
  Unwind : Type
  Terminal : Type
  equal : Callback.Run State (Query × T) Bool Unwind Terminal

def containsRun (index : ContainsIndex) :
    Callback.Run index.State (Value index.T × index.Query) Bool index.Unwind index.Terminal :=
  fun before args outcome => match args.1 with
  | .none => outcome = .returned false before
  | .some value => index.equal before (args.2, value) outcome

def containsFamily : Family where
  Index := ContainsIndex
  State := ContainsIndex.State
  Args := fun index => Value index.T × index.Query
  Value := fun _ => Bool
  Unwind := ContainsIndex.Unwind
  Terminal := ContainsIndex.Terminal
  contract := fun index => ⟨fun _ _ => True, containsRun index⟩

theorem containsReference : FamilyReference containsFamily containsRun :=
  fun _ _ _ _ _ run => run

abbrev containsSample : ContainsIndex where
  State := Nat
  T := Nat
  Query := Nat
  Unwind := String
  Terminal := String
  equal := Callback.ofFunction fun before args => .returned (args.1 == args.2) (before + 1)

theorem containsExecution : FamilyHasExecution containsFamily containsRun containsSample := by
  unfold FamilyHasExecution
  dsimp only [containsFamily, containsSample, Solanalib.Contracts.Model.HasExecution]
  exact ⟨0, (.some 7, 7), .returned true 1, trivial, rfl⟩

theorem containsSatisfiable : FamilySatisfiable containsFamily containsSample :=
  containsExecution.satisfiable

/-- A panic provider has no ordinary result. Its effects, unwind reason and
terminal behavior belong to the actual panic runtime interpretation. -/
structure UnwrapIndex where
  State : Type
  T : Type
  Unwind : Type
  Terminal : Type
  panic : Callback.Run State String Empty Unwind Terminal

/-- The literal diagnostic of every reviewed `COption::unwrap`. -/
def unwrapMessage : String := "called `COption::unwrap()` on a `COption::None` value"

def unwrapRun (index : UnwrapIndex) :
    Callback.Run index.State (Value index.T) index.T index.Unwind index.Terminal :=
  fun before value outcome => match value with
  | .some value => outcome = .returned value before
  | .none => Callback.map Empty.elim index.panic before unwrapMessage outcome

def unwrapFamily : Family where
  Index := UnwrapIndex
  State := UnwrapIndex.State
  Args := fun index => Value index.T
  Value := UnwrapIndex.T
  Unwind := UnwrapIndex.Unwind
  Terminal := UnwrapIndex.Terminal
  contract := fun index => ⟨fun _ _ => True, unwrapRun index⟩

theorem unwrapReference : FamilyReference unwrapFamily unwrapRun := fun _ _ _ _ _ run => run

abbrev unwrapSample : UnwrapIndex where
  State := Unit
  T := Nat
  Unwind := String
  Terminal := String
  panic := Callback.ofFunction fun before message => .unwound message before

theorem unwrapExecution : FamilyHasExecution unwrapFamily unwrapRun unwrapSample := by
  unfold FamilyHasExecution
  dsimp only [unwrapFamily, unwrapSample, Solanalib.Contracts.Model.HasExecution]
  exact ⟨(), .none, .unwound unwrapMessage (), trivial, .unwound unwrapMessage (), rfl, rfl⟩

theorem unwrapSatisfiable : FamilySatisfiable unwrapFamily unwrapSample :=
  unwrapExecution.satisfiable

/-- FnOnce owns both the closure and the passed payload. Its provider includes
their internal cleanup on every exit. In the None branch only the unused
closure is dropped, at this call site and in the current state. -/
structure MapIndex where
  State : Type
  T : Type
  U : Type
  Closure : Type
  Unwind : Type
  Terminal : Type
  call : Callback.Run State (Closure × T) U Unwind Terminal
  dropClosure : Callback.Run State Closure Unit Unwind Terminal

def mapRun (index : MapIndex) : Callback.Run index.State (Value index.T × index.Closure)
    (Value index.U) index.Unwind index.Terminal := fun before args outcome =>
  match args.1 with
  | .some value => Callback.map Value.some index.call before (args.2, value) outcome
  | .none => Callback.map (fun _ => Value.none) index.dropClosure before args.2 outcome

def mapFamily : Family where
  Index := MapIndex
  State := MapIndex.State
  Args := fun index => Value index.T × index.Closure
  Value := fun index => Value index.U
  Unwind := MapIndex.Unwind
  Terminal := MapIndex.Terminal
  contract := fun index => ⟨fun _ _ => True, mapRun index⟩

theorem mapReference : FamilyReference mapFamily mapRun := fun _ _ _ _ _ run => run

abbrev mapSample : MapIndex where
  State := Nat
  T := Nat
  U := Nat
  Closure := Nat
  Unwind := String
  Terminal := String
  call := Callback.ofFunction fun before args => .returned (args.1 + args.2) (before + 1)
  dropClosure := Callback.ofFunction fun before _ => .returned () (before + 1)

theorem mapExecution : FamilyHasExecution mapFamily mapRun mapSample := by
  unfold FamilyHasExecution
  dsimp only [mapFamily, mapSample, Solanalib.Contracts.Model.HasExecution]
  exact ⟨0, (.some 7, 3), .returned (.some 10) 1, trivial, .returned 10 1, rfl, rfl⟩

theorem mapSatisfiable : FamilySatisfiable mapFamily mapSample := mapExecution.satisfiable

/-- How the selected source lowering treats a value already moved into the
return place when a later local destructor unwinds. The pinned rustc leaves
it retained (rust-lang/rust#47949); a lowering that cleans it uses `drop`. -/
inductive ReturnPlace where
  | retain
  | drop
  deriving DecidableEq, Repr

/-- The already evaluated fallback is a separate owner. Some drops it before
returning the payload; None moves it without any destructor. -/
structure UnwrapOrIndex where
  State : Type
  T : Type
  Unwind : Type
  Terminal : Type
  dropValue : Callback.Run State T Unit Unwind Terminal
  returnPlace : ReturnPlace
  doubleUnwind : Owned.DoubleUnwind State Unwind Terminal

def unwrapOrRun (index : UnwrapOrIndex) : Callback.Run index.State (Value index.T × index.T)
    index.T index.Unwind index.Terminal := fun before args outcome =>
  match args.1 with
  | .none => outcome = .returned args.2 before
  | .some value => ∃ pending,
      Callback.map (fun _ => value) index.dropValue before args.2 pending ∧
      match index.returnPlace with
      | .retain => outcome = pending
      | .drop => Owned.onUnwind index.doubleUnwind
          [fun state final => index.dropValue state value final] pending outcome

def unwrapOrFamily : Family where
  Index := UnwrapOrIndex
  State := UnwrapOrIndex.State
  Args := fun index => Value index.T × index.T
  Value := UnwrapOrIndex.T
  Unwind := UnwrapOrIndex.Unwind
  Terminal := UnwrapOrIndex.Terminal
  contract := fun index => ⟨fun _ _ => True, unwrapOrRun index⟩

theorem unwrapOrReference : FamilyReference unwrapOrFamily unwrapOrRun :=
  fun _ _ _ _ _ run => run

abbrev unwrapOrSample : UnwrapOrIndex where
  State := Nat
  T := Nat
  Unwind := String
  Terminal := String
  dropValue := Callback.ofFunction fun before _ => .returned () (before + 1)
  returnPlace := .retain
  doubleUnwind := fun _ _ _ reason => reason = "double panic"

theorem unwrapOrExecution : FamilyHasExecution unwrapOrFamily unwrapOrRun unwrapOrSample := by
  unfold FamilyHasExecution
  dsimp only [unwrapOrFamily, unwrapOrSample, Solanalib.Contracts.Model.HasExecution]
  exact ⟨0, (.some 7, 8), .returned 7 1, trivial, .returned 7 1,
    ⟨.returned () 1, rfl, rfl⟩, rfl⟩

theorem unwrapOrSatisfiable : FamilySatisfiable unwrapOrFamily unwrapOrSample :=
  unwrapOrExecution.satisfiable

/-- Default is called only for None; it can have every callback exit. -/
structure DefaultIndex where
  State : Type
  T : Type
  Unwind : Type
  Terminal : Type
  defaultValue : Callback.Run State Unit T Unwind Terminal

def unwrapOrDefaultRun (index : DefaultIndex) :
    Callback.Run index.State (Value index.T) index.T index.Unwind index.Terminal :=
  fun before value outcome => match value with
  | .some value => outcome = .returned value before
  | .none => index.defaultValue before () outcome

def unwrapOrDefaultFamily : Family where
  Index := DefaultIndex
  State := DefaultIndex.State
  Args := fun index => Value index.T
  Value := DefaultIndex.T
  Unwind := DefaultIndex.Unwind
  Terminal := DefaultIndex.Terminal
  contract := fun index => ⟨fun _ _ => True, unwrapOrDefaultRun index⟩

theorem unwrapOrDefaultReference : FamilyReference unwrapOrDefaultFamily unwrapOrDefaultRun :=
  fun _ _ _ _ _ run => run

abbrev unwrapOrDefaultSample : DefaultIndex where
  State := Nat
  T := Nat
  Unwind := String
  Terminal := String
  defaultValue := Callback.ofFunction fun before _ => .returned 9 (before + 1)

theorem unwrapOrDefaultExecution : FamilyHasExecution unwrapOrDefaultFamily unwrapOrDefaultRun
    unwrapOrDefaultSample := by
  unfold FamilyHasExecution
  dsimp only [unwrapOrDefaultFamily, unwrapOrDefaultSample, Solanalib.Contracts.Model.HasExecution]
  exact ⟨0, .none, .returned 9 1, trivial, rfl⟩

theorem unwrapOrDefaultSatisfiable :
    FamilySatisfiable unwrapOrDefaultFamily unwrapOrDefaultSample :=
  unwrapOrDefaultExecution.satisfiable

/-- The None unwrap branch cannot manufacture an ordinary value even if T
is inhabited: the return type of the panic provider is Empty. -/
theorem unwrap_none_ne_returned (index : UnwrapIndex) (before after : index.State)
    (value : index.T) : ¬ unwrapRun index before .none (.returned value after) := by
  rintro ⟨pending, _, equal⟩
  cases pending with
  | returned impossible _ => cases impossible
  | unwound _ _ | terminated _ => cases equal

/-- Mixed variants never evaluate a payload comparison or alter its state. -/
theorem eq_mixed (index : EqIndex) (before : index.State) (value : index.T)
    (outcome : Outcome index.State Bool index.Unwind index.Terminal) :
    eqRun index before (.none, .some value) outcome ↔ outcome = .returned false before := Iff.rfl

/-- A missing payload does not call FnOnce; it drops the unused closure. -/
theorem map_none (index : MapIndex) (before : index.State) (closure : index.Closure)
    (outcome : Outcome index.State (Value index.U) index.Unwind index.Terminal) :
    mapRun index before (.none, closure) outcome ↔
      Callback.map (fun _ => Value.none) index.dropClosure before closure outcome := Iff.rfl

end Solanalib.Specs.Core.ProgramOption
