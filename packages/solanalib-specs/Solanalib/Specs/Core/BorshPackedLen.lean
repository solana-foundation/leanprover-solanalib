/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.Callback
public import Solanalib.Runtime.Basic

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.BorshPackedLen

/-- Operations available to a serializer at the private WriteCounter. Effects
represent the operations of the selected `T::serialize` implementation, including
its local cleanup. They cannot directly read or modify the private count. -/
inductive Command (Control EffectArg EffectValue Error Unwind : Type) where
  | done (result : Except Error Unit)
  | unwind (reason : Unwind)
  | write (bytes : Solanalib.Runtime.Bytes) (next : Except Unwind Nat → Control)
  | advance (next : Control)
  | effect (args : EffectArg) (next : Except Unwind EffectValue → Control)

/-- The serializer may be an arbitrary state machine, including a loop.
Only finite executions inhabit `Runs`; no termination of an arbitrary trait
implementation is assumed. The word size and overflow policy of the counter are
explicit build choices, independent of the type and effects of the serializer. -/
structure Index where
  State : Type
  Value : Type
  Error : Type
  Unwind : Type
  Terminal : Type
  Control : Type
  EffectArg : Type
  EffectValue : Type
  wordBits : Nat
  checkedOverflow : Bool
  start : Value → Control
  command : Control → Command Control EffectArg EffectValue Error Unwind
  effects : Callback.Run State EffectArg EffectValue Unwind Terminal
  overflow : Callback.Run State Unit Empty Unwind Terminal

/-- One counter write returns its complete input length. A checked overflow
calls the selected panic policy before updating the count. -/
def write (index : Index) (count : Nat) (bytes : Solanalib.Runtime.Bytes) :
    Callback.Run index.State Unit (Nat × Nat) index.Unwind index.Terminal :=
  fun before _ outcome =>
    if index.checkedOverflow ∧ 2^index.wordBits ≤ count + bytes.length then
      Callback.map Empty.elim index.overflow before () outcome
    else outcome = .returned (bytes.length, (count + bytes.length) % 2^index.wordBits) before

/-- The exact finite dialogue between the chosen serializer and the counter.
An ordinary serialization error is returned unchanged. Flush succeeds without
changing the counter. Every external effect uses the actual current state. -/
inductive Runs (index : Index) : index.Control → Nat → index.State →
    Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal → Prop
  | done (control : index.Control) (count : Nat) (state : index.State)
      (result : Except index.Error Unit)
      (selected : index.command control = .done result) :
      Runs index control count state
        (.returned (result.map (fun _ => count)) state)
  | unwind (control : index.Control) (count : Nat) (state : index.State)
      (reason : index.Unwind) (selected : index.command control = .unwind reason) :
      Runs index control count state (.unwound reason state)
  | writeReturn (control : index.Control) (count : Nat) (before after : index.State)
      (bytes : Solanalib.Runtime.Bytes) (next : Except index.Unwind Nat → index.Control) (amount
        updated : Nat)
      (outcome : Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal)
      (selected : index.command control = .write bytes next)
      (written : write index count bytes before () (.returned (amount, updated) after))
      (rest : Runs index (next (.ok amount)) updated after outcome) :
      Runs index control count before outcome
  | writeUnwind (control : index.Control) (count : Nat) (before after : index.State)
      (bytes : Solanalib.Runtime.Bytes) (next : Except index.Unwind Nat → index.Control) (reason :
        index.Unwind)
      (outcome : Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal)
      (selected : index.command control = .write bytes next)
      (written : write index count bytes before () (.unwound reason after))
      (rest : Runs index (next (.error reason)) count after outcome) :
      Runs index control count before outcome
  | writeTerminal (control : index.Control) (count : Nat) (before : index.State)
      (bytes : Solanalib.Runtime.Bytes) (next : Except index.Unwind Nat → index.Control) (reason :
        index.Terminal)
      (selected : index.command control = .write bytes next)
      (written : write index count bytes before () (.terminated reason)) :
      Runs index control count before (.terminated reason)
  | advance (control next : index.Control) (count : Nat) (before : index.State)
      (outcome : Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal)
      (selected : index.command control = .advance next)
      (rest : Runs index next count before outcome) : Runs index control count before outcome
  | effectReturn (control : index.Control) (count : Nat) (before after : index.State)
      (args : index.EffectArg) (next : Except index.Unwind index.EffectValue → index.Control)
      (value : index.EffectValue)
      (outcome : Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal)
      (selected : index.command control = .effect args next)
      (effect : index.effects before args (.returned value after))
      (rest : Runs index (next (.ok value)) count after outcome) :
      Runs index control count before outcome
  | effectUnwind (control : index.Control) (count : Nat) (before after : index.State)
      (args : index.EffectArg) (next : Except index.Unwind index.EffectValue → index.Control)
        (reason : index.Unwind)
      (outcome : Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal)
      (selected : index.command control = .effect args next)
      (effect : index.effects before args (.unwound reason after))
      (rest : Runs index (next (.error reason)) count after outcome) :
      Runs index control count before outcome
  | effectTerminal (control : index.Control) (count : Nat) (before : index.State)
      (args : index.EffectArg) (next : Except index.Unwind index.EffectValue → index.Control)
        (reason : index.Terminal)
      (selected : index.command control = .effect args next)
      (effect : index.effects before args (.terminated reason)) :
      Runs index control count before (.terminated reason)

def run (index : Index) (before : index.State) (value : index.Value) :=
  Runs index (index.start value) 0 before

def family : Family where
  Index := Index
  State := Index.State
  Args := Index.Value
  Value := fun index => Except index.Error Nat
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => { requires := fun _ _ => True, post := run index }

def reference : FamilyRun family := run

theorem reference_holds : FamilyReference family reference := fun _ _ _ _ _ execution => execution

/-- A serializer can use the default write_all operation as this command.
The counter always consumes a nonempty slice completely. For an empty slice
the default method skips Write::write, and there is no counter change. -/
def writeAll {Control EffectArg EffectValue Error Unwind : Type} (bytes : Solanalib.Runtime.Bytes)
    (next : Except Unwind Unit → Control) : Command Control EffectArg EffectValue Error Unwind :=
  if bytes.isEmpty then .advance (next (.ok ()))
  else .write bytes (fun result => next (result.map (fun _ => ())))

/-- Functional callbacks used only for executable replay and closed witnesses. -/
structure Executable (index : Index) where
  effects : index.State → index.EffectArg →
    Outcome index.State index.EffectValue index.Unwind index.Terminal
  overflow : index.State → Unit → Outcome index.State Empty index.Unwind index.Terminal
  effects_eq : index.effects = Callback.ofFunction effects
  overflow_eq : index.overflow = Callback.ofFunction overflow

def writeFn (index : Index) (exec : Executable index) (count : Nat)
    (bytes : Solanalib.Runtime.Bytes) (before : index.State) :
    Outcome index.State (Nat × Nat) index.Unwind index.Terminal :=
  if index.checkedOverflow ∧ 2^index.wordBits ≤ count + bytes.length then
    Outcome.map Empty.elim (exec.overflow before ())
  else .returned (bytes.length, (count + bytes.length) % 2^index.wordBits) before

theorem writeFn_admitted (index : Index) (exec : Executable index) (count : Nat)
    (bytes : Solanalib.Runtime.Bytes) (before : index.State) :
    write index count bytes before () (writeFn index exec count bytes before) := by
  unfold write writeFn
  split
  · rw [exec.overflow_eq]
    exact ⟨exec.overflow before (), rfl, rfl⟩
  · rfl

theorem writeFn_graph (index : Index) (exec : Executable index) (count : Nat)
    (bytes : Solanalib.Runtime.Bytes) (before : index.State)
    (outcome : Outcome index.State (Nat × Nat) index.Unwind index.Terminal) :
    write index count bytes before () outcome ↔
      writeFn index exec count bytes before = outcome := by
  unfold write writeFn
  split
  · rw [exec.overflow_eq]
    exact Callback.map_ofFunction _ _ _ _ _
  · exact eq_comm

/-- Bounded replay of a possibly looping serializer. Running out of fuel
reports no result; it never creates a source error or terminal exit. -/
def runFuel (index : Index) (exec : Executable index) : Nat → index.Control → Nat →
    index.State → Option (Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal)
  | 0, _, _, _ => none
  | fuel + 1, control, count, before =>
    match index.command control with
    | .done result => some (.returned (result.map (fun _ => count)) before)
    | .unwind reason => some (.unwound reason before)
    | .advance next => runFuel index exec fuel next count before
    | .write bytes next =>
      match writeFn index exec count bytes before with
      | .returned (amount, updated) after => runFuel index exec fuel (next (.ok amount)) updated
        after
      | .unwound reason after => runFuel index exec fuel (next (.error reason)) count after
      | .terminated reason => some (.terminated reason)
    | .effect args next =>
      match exec.effects before args with
      | .returned value after => runFuel index exec fuel (next (.ok value)) count after
      | .unwound reason after => runFuel index exec fuel (next (.error reason)) count after
      | .terminated reason => some (.terminated reason)

/-- Every finite executable replay is an execution of the registered relation. -/
theorem runFuel_sound (index : Index) (exec : Executable index) (fuel : Nat)
    (control : index.Control) (count : Nat) (before : index.State)
    (outcome : Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal)
    (computed : runFuel index exec fuel control count before = some outcome) :
    Runs index control count before outcome := by
  induction fuel generalizing control count before with
  | zero => cases computed
  | succ fuel ih =>
    simp only [runFuel] at computed
    cases selected : index.command control with
    | done result =>
      simp only [selected] at computed
      cases computed
      exact .done control count before result selected
    | unwind reason =>
      simp only [selected] at computed
      cases computed
      exact .unwind control count before reason selected
    | advance next =>
      simp only [selected] at computed
      exact .advance control next count before outcome selected (ih _ _ _ computed)
    | write bytes next =>
      simp only [selected] at computed
      have admitted := writeFn_admitted index exec count bytes before
      cases written : writeFn index exec count bytes before with
      | returned pair after =>
        rcases pair with ⟨amount, updated⟩
        rw [written] at computed admitted
        exact .writeReturn control count before after bytes next amount updated outcome
          selected admitted (ih _ _ _ computed)
      | unwound reason after =>
        rw [written] at computed admitted
        exact .writeUnwind control count before after bytes next reason outcome selected
          admitted (ih _ _ _ computed)
      | terminated reason =>
        rw [written] at computed admitted
        cases computed
        exact .writeTerminal control count before bytes next reason selected admitted
    | effect args next =>
      simp only [selected] at computed
      have admitted : index.effects before args (exec.effects before args) := by
        rw [exec.effects_eq]
        rfl
      cases effect : exec.effects before args with
      | returned value after =>
        rw [effect] at computed admitted
        exact .effectReturn control count before after args next value outcome
          selected admitted (ih _ _ _ computed)
      | unwound reason after =>
        rw [effect] at computed admitted
        exact .effectUnwind control count before after args next reason outcome selected
          admitted (ih _ _ _ computed)
      | terminated reason =>
        rw [effect] at computed admitted
        cases computed
        exact .effectTerminal control count before args next reason selected admitted

/-- A completed replay determines every finite outcome at a functional index;
the fuel bound does not weaken the decided relation. -/
theorem runFuel_agrees (index : Index) (exec : Executable index)
    {control : index.Control} {count : Nat} {before : index.State}
    {outcome : Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal}
    (execution : Runs index control count before outcome) :
    ∀ fuel actual, runFuel index exec fuel control count before = some actual → outcome = actual :=
      by
  induction execution with
  | done control count state result selected =>
    intro fuel actual computed
    cases fuel with
    | zero => cases computed
    | succ fuel => simpa only [runFuel, selected, Option.some.injEq] using computed
  | unwind control count state reason selected =>
    intro fuel actual computed
    cases fuel with
    | zero => cases computed
    | succ fuel => simpa only [runFuel, selected, Option.some.injEq] using computed
  | advance control next count before outcome selected rest ih =>
    intro fuel actual computed
    cases fuel with
    | zero => cases computed
    | succ fuel => exact ih fuel actual (by simpa only [runFuel, selected] using computed)
  | writeReturn control count before after bytes next amount updated outcome selected written rest
    ih =>
    have graph := (writeFn_graph index exec count bytes before _).mp written
    intro fuel actual computed
    cases fuel with
    | zero => cases computed
    | succ fuel => exact ih fuel actual (by simpa only [runFuel, selected, graph] using computed)
  | writeUnwind control count before after bytes next reason outcome selected written rest ih =>
    have graph := (writeFn_graph index exec count bytes before _).mp written
    intro fuel actual computed
    cases fuel with
    | zero => cases computed
    | succ fuel => exact ih fuel actual (by simpa only [runFuel, selected, graph] using computed)
  | writeTerminal control count before bytes next reason selected written =>
    have graph := (writeFn_graph index exec count bytes before _).mp written
    intro fuel actual computed
    cases fuel with
    | zero => cases computed
    | succ fuel => simpa only [runFuel, selected, graph, Option.some.injEq] using computed
  | effectReturn control count before after args next value outcome selected effect rest ih =>
    rw [exec.effects_eq] at effect
    simp only [Callback.ofFunction] at effect
    intro fuel actual computed
    cases fuel with
    | zero => cases computed
    | succ fuel => exact ih fuel actual (by simpa only [runFuel, selected, effect] using computed)
  | effectUnwind control count before after args next reason outcome selected effect rest ih =>
    rw [exec.effects_eq] at effect
    simp only [Callback.ofFunction] at effect
    intro fuel actual computed
    cases fuel with
    | zero => cases computed
    | succ fuel => exact ih fuel actual (by simpa only [runFuel, selected, effect] using computed)
  | effectTerminal control count before args next reason selected effect =>
    rw [exec.effects_eq] at effect
    simp only [Callback.ofFunction] at effect
    intro fuel actual computed
    cases fuel with
    | zero => cases computed
    | succ fuel => simpa only [runFuel, selected, effect, Option.some.injEq] using computed

theorem runFuel_graph (index : Index) (exec : Executable index) (fuel : Nat)
    (control : index.Control) (count : Nat) (before : index.State)
    (expected : Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal)
    (computed : runFuel index exec fuel control count before = some expected)
    (outcome : Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal) :
    Runs index control count before outcome ↔ expected = outcome :=
  ⟨fun run => (runFuel_agrees index exec run fuel expected computed).symm,
    fun same => same ▸ runFuel_sound index exec fuel control count before expected computed⟩

/-- A normal serializer of one byte slice; the index remains fully generic. -/
def sample : Index where
  State := Unit
  Value := Solanalib.Runtime.Bytes
  Error := Nat
  Unwind := Nat
  Terminal := Nat
  Control := Option Solanalib.Runtime.Bytes
  EffectArg := Unit
  EffectValue := Unit
  wordBits := 64
  checkedOverflow := true
  start := some
  command := fun | some bytes => .write bytes (fun _ => none) | none => .done (.ok ())
  effects := Callback.ofFunction fun state _ => .returned () state
  overflow := Callback.ofFunction fun state _ => .unwound 1 state

def sampleExecutable : Executable sample where
  effects := fun state _ => .returned () state
  overflow := fun state _ => .unwound (1 : Nat) state
  effects_eq := rfl
  overflow_eq := rfl

theorem sample_execution : FamilyHasExecution family reference sample := by
  refine ⟨(), [1, 2, 3], .returned (.ok 3) (), trivial, ?_⟩
  exact runFuel_sound sample sampleExecutable 2 (some [1, 2, 3]) 0 () _ rfl

theorem sample_satisfiable : FamilySatisfiable family sample := sample_execution.satisfiable

end Solanalib.Specs.Core.BorshPackedLen
