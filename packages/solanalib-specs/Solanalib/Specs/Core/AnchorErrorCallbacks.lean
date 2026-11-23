/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorError
public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorError

structure ValuesArgs (ProgramError Left Right : Type) where
  error : Value ProgramError
  left : Left
  right : Right

/-- Both conversions have returned. Scope cleanup includes replacement of the
old comparison and destruction of the consumed operands. If that cleanup
unwinds, its relation includes all remaining unwind cleanup before reporting
the resulting state. No destructor is assumed to preserve state. -/
structure NormalCleanupArgs (ProgramError Left Right : Type) where
  values : ValuesArgs ProgramError Left Right
  leftText : String
  rightText : String

def NormalCleanupArgs.result {ProgramError Left Right : Type}
    (args : NormalCleanupArgs ProgramError Left Right) : Value ProgramError :=
  args.values.error.replaceCompared (.values args.leftText args.rightText)

/-- Cleanup after a conversion panics. `leftText = none` means the first
conversion did not return; `some text` means only the first one returned.
The original error has not yet had its comparison replaced. -/
structure UnwindCleanupArgs (ProgramError Left Right Unwind : Type) where
  values : ValuesArgs ProgramError Left Right
  reason : Unwind
  leftText : Option String

/-- Explicit trait and scope-cleanup interfaces for `with_values`. Ordinary
`ToString` returns a String, not a `Result`. A second panic during unwind
cleanup is terminal; successful cleanup resumes the original panic. -/
structure ValuesCallbacks (State ProgramError Left Right Unwind Terminal : Type) where
  left : Callback.Run State Left String Unwind Terminal
  right : Callback.Run State Right String Unwind Terminal
  normalCleanup : Callback.Run State (NormalCleanupArgs ProgramError Left Right)
    Unit Unwind Terminal
  unwindCleanup : Callback.Run State (UnwindCleanupArgs ProgramError Left Right Unwind)
    Unit Empty Terminal

/-- Complete the unwind cleanup of a conversion before exposing its finite exit.
Terminal conversion exits do not run cleanup; normal returns keep their exact
text and state. -/
def completeString {State ProgramError Left Right Input Unwind Terminal : Type}
    (cleanup : Callback.Run State (UnwindCleanupArgs ProgramError Left Right Unwind)
      Unit Empty Terminal)
    (args : ValuesArgs ProgramError Left Right) (leftText : Option String)
    (conversion : Callback.Run State Input String Unwind Terminal) :
    Callback.Run State Input String Unwind Terminal :=
  fun before input outcome => ∃ raw, conversion before input raw ∧
    match raw with
    | .returned text after => outcome = .returned text after
    | .terminated reason => outcome = .terminated reason
    | .unwound reason actual => ∃ cleaned,
        cleanup actual ⟨args, reason, leftText⟩ cleaned ∧
        match cleaned with
        | .returned _ after => outcome = .unwound reason after
        | .terminated terminal => outcome = .terminated terminal
        | .unwound impossible _ => nomatch impossible

/-- The postcondition sequences two explicit conversions and then cleanup.
Every continuation receives the actual state of the preceding callback. -/
def withValuesPost {State ProgramError Left Right Unwind Terminal : Type}
    (callbacks : ValuesCallbacks State ProgramError Left Right Unwind Terminal)
    (before : State) (args : ValuesArgs ProgramError Left Right) :
    Outcome State (Value ProgramError) Unwind Terminal → Prop :=
  Callback.bind (completeString callbacks.unwindCleanup args none callbacks.left)
    (fun leftText middle =>
      Callback.bind
        (completeString callbacks.unwindCleanup args (some leftText) callbacks.right)
        (fun rightText actual =>
          Callback.map (fun (_ : Unit) =>
              args.error.replaceCompared (.values leftText rightText))
            callbacks.normalCleanup actual ⟨args, leftText, rightText⟩)
        middle args.right)
    before args.left

def withValuesContract {State ProgramError Left Right Unwind Terminal : Type}
    (callbacks : ValuesCallbacks State ProgramError Left Right Unwind Terminal) :
    Solanalib.Contracts.Model State (ValuesArgs ProgramError Left Right)
      (Value ProgramError) Unwind Terminal where
  requires := fun _ _ => True
  post := withValuesPost callbacks

/-- A small operational reference relation: a conversion or cleanup can fail,
and a failed first conversion has no transition to a second conversion. This
relation also admits nondeterministic and nonterminating callback interfaces. -/
inductive ValuesRun {State ProgramError Left Right Unwind Terminal : Type}
    (callbacks : ValuesCallbacks State ProgramError Left Right Unwind Terminal)
    (before : State) (args : ValuesArgs ProgramError Left Right) :
    Outcome State (Value ProgramError) Unwind Terminal → Prop where
  | returned {leftText rightText : String} {middle actual after : State}
      (left : callbacks.left before args.left (.returned leftText middle))
      (right : callbacks.right middle args.right (.returned rightText actual))
      (cleanup : callbacks.normalCleanup actual ⟨args, leftText, rightText⟩
        (.returned () after)) :
      ValuesRun callbacks before args
        (.returned (args.error.replaceCompared (.values leftText rightText)) after)
  | cleanupUnwound {leftText rightText : String} {middle actual after : State}
      {reason : Unwind}
      (left : callbacks.left before args.left (.returned leftText middle))
      (right : callbacks.right middle args.right (.returned rightText actual))
      (cleanup : callbacks.normalCleanup actual ⟨args, leftText, rightText⟩
        (.unwound reason after)) :
      ValuesRun callbacks before args (.unwound reason after)
  | cleanupTerminated {leftText rightText : String} {middle actual : State}
      {reason : Terminal}
      (left : callbacks.left before args.left (.returned leftText middle))
      (right : callbacks.right middle args.right (.returned rightText actual))
      (cleanup : callbacks.normalCleanup actual ⟨args, leftText, rightText⟩
        (.terminated reason)) :
      ValuesRun callbacks before args (.terminated reason)
  | leftUnwound {actual after : State} {reason : Unwind}
      (left : callbacks.left before args.left (.unwound reason actual))
      (cleanup : callbacks.unwindCleanup actual ⟨args, reason, none⟩
        (.returned () after)) :
      ValuesRun callbacks before args (.unwound reason after)
  | leftCleanupTerminated {actual : State} {reason : Unwind} {terminal : Terminal}
      (left : callbacks.left before args.left (.unwound reason actual))
      (cleanup : callbacks.unwindCleanup actual ⟨args, reason, none⟩
        (.terminated terminal)) :
      ValuesRun callbacks before args (.terminated terminal)
  | leftTerminated {reason : Terminal}
      (left : callbacks.left before args.left (.terminated reason)) :
      ValuesRun callbacks before args (.terminated reason)
  | rightUnwound {leftText : String} {middle actual after : State} {reason : Unwind}
      (left : callbacks.left before args.left (.returned leftText middle))
      (right : callbacks.right middle args.right (.unwound reason actual))
      (cleanup : callbacks.unwindCleanup actual ⟨args, reason, some leftText⟩
        (.returned () after)) :
      ValuesRun callbacks before args (.unwound reason after)
  | rightCleanupTerminated {leftText : String} {middle actual : State}
      {reason : Unwind} {terminal : Terminal}
      (left : callbacks.left before args.left (.returned leftText middle))
      (right : callbacks.right middle args.right (.unwound reason actual))
      (cleanup : callbacks.unwindCleanup actual ⟨args, reason, some leftText⟩
        (.terminated terminal)) :
      ValuesRun callbacks before args (.terminated terminal)
  | rightTerminated {leftText : String} {middle : State} {reason : Terminal}
      (left : callbacks.left before args.left (.returned leftText middle))
      (right : callbacks.right middle args.right (.terminated reason)) :
      ValuesRun callbacks before args (.terminated reason)

theorem completeString_returned
    {State ProgramError Left Right Input Unwind Terminal : Type}
    (cleanup : Callback.Run State (UnwindCleanupArgs ProgramError Left Right Unwind)
      Unit Empty Terminal)
    (args : ValuesArgs ProgramError Left Right) (leftText : Option String)
    {conversion : Callback.Run State Input String Unwind Terminal}
    {before after : State} {input : Input} {text : String}
    (returned : conversion before input (.returned text after)) :
    completeString cleanup args leftText conversion before input (.returned text after) :=
  ⟨.returned text after, returned, rfl⟩

theorem completeString_unwound
    {State ProgramError Left Right Input Unwind Terminal : Type}
    {cleanup : Callback.Run State (UnwindCleanupArgs ProgramError Left Right Unwind)
      Unit Empty Terminal}
    {args : ValuesArgs ProgramError Left Right} {leftText : Option String}
    {conversion : Callback.Run State Input String Unwind Terminal}
    {before actual after : State} {input : Input} {reason : Unwind}
    (unwound : conversion before input (.unwound reason actual))
    (cleaned : cleanup actual ⟨args, reason, leftText⟩ (.returned () after)) :
    completeString cleanup args leftText conversion before input (.unwound reason after) :=
  ⟨.unwound reason actual, unwound, .returned () after, cleaned, rfl⟩

theorem completeString_cleanupTerminated
    {State ProgramError Left Right Input Unwind Terminal : Type}
    {cleanup : Callback.Run State (UnwindCleanupArgs ProgramError Left Right Unwind)
      Unit Empty Terminal}
    {args : ValuesArgs ProgramError Left Right} {leftText : Option String}
    {conversion : Callback.Run State Input String Unwind Terminal}
    {before actual : State} {input : Input} {reason : Unwind} {terminal : Terminal}
    (unwound : conversion before input (.unwound reason actual))
    (cleaned : cleanup actual ⟨args, reason, leftText⟩ (.terminated terminal)) :
    completeString cleanup args leftText conversion before input (.terminated terminal) :=
  ⟨.unwound reason actual, unwound, .terminated terminal, cleaned, rfl⟩

theorem completeString_terminated
    {State ProgramError Left Right Input Unwind Terminal : Type}
    (cleanup : Callback.Run State (UnwindCleanupArgs ProgramError Left Right Unwind)
      Unit Empty Terminal)
    (args : ValuesArgs ProgramError Left Right) (leftText : Option String)
    {conversion : Callback.Run State Input String Unwind Terminal}
    {before : State} {input : Input} {reason : Terminal}
    (terminated : conversion before input (.terminated reason)) :
    completeString cleanup args leftText conversion before input (.terminated reason) :=
  ⟨.terminated reason, terminated, rfl⟩

/-- Unwind cleanup cannot convert a failed conversion into a returned String. -/
theorem completeString_returned_iff
    {State ProgramError Left Right Input Unwind Terminal : Type}
    (cleanup : Callback.Run State (UnwindCleanupArgs ProgramError Left Right Unwind)
      Unit Empty Terminal)
    (args : ValuesArgs ProgramError Left Right) (leftText : Option String)
    (conversion : Callback.Run State Input String Unwind Terminal)
    (before after : State) (input : Input) (text : String) :
    completeString cleanup args leftText conversion before input (.returned text after) ↔
      conversion before input (.returned text after) := by
  constructor
  · rintro ⟨raw, converted, step⟩
    cases raw with
    | returned value state => cases step; exact converted
    | terminated reason => cases step
    | unwound reason state =>
      obtain ⟨cleaned, _, result⟩ := step
      cases cleaned with
      | returned value final => cases result
      | terminated terminal => cases result
      | unwound impossible final => cases impossible
  · exact completeString_returned cleanup args leftText

/-- A returned Error requires both conversions and normal cleanup to return.
The result replaces exactly the comparison, and its state is the cleanup state. -/
theorem withValuesPost_returned_iff
    {State ProgramError Left Right Unwind Terminal : Type}
    (callbacks : ValuesCallbacks State ProgramError Left Right Unwind Terminal)
    (before : State) (args : ValuesArgs ProgramError Left Right)
    (result : Value ProgramError) (after : State) :
    withValuesPost callbacks before args (.returned result after) ↔
      ∃ leftText rightText middle actual,
        callbacks.left before args.left (.returned leftText middle) ∧
        callbacks.right middle args.right (.returned rightText actual) ∧
        callbacks.normalCleanup actual ⟨args, leftText, rightText⟩ (.returned () after) ∧
        result = args.error.replaceCompared (.values leftText rightText) := by
  constructor
  · rintro ⟨leftExit, left, next⟩
    cases leftExit with
    | unwound reason state => cases next
    | terminated reason => cases next
    | returned leftText middle =>
      have leftReturned := (completeString_returned_iff _ _ _ _ _ _ _ _).mp left
      obtain ⟨rightExit, right, finish⟩ := next
      cases rightExit with
      | unwound reason state => cases finish
      | terminated reason => cases finish
      | returned rightText actual =>
        have rightReturned := (completeString_returned_iff _ _ _ _ _ _ _ _).mp right
        obtain ⟨cleanupExit, cleanup, equality⟩ := finish
        cases cleanupExit with
        | unwound reason state => cases equality
        | terminated reason => cases equality
        | returned cleanupResult final =>
          cases cleanupResult
          cases equality
          exact ⟨leftText, rightText, middle, actual, leftReturned, rightReturned, cleanup, rfl⟩
  · rintro ⟨leftText, rightText, middle, actual, left, right, cleanup, rfl⟩
    exact ⟨_, completeString_returned _ _ _ left,
      _, completeString_returned _ _ _ right, _, cleanup, rfl⟩

/-- Every finite operational reference exit satisfies the sequenced contract. -/
theorem valuesRun_holds {State ProgramError Left Right Unwind Terminal : Type}
    (callbacks : ValuesCallbacks State ProgramError Left Right Unwind Terminal) :
    (withValuesContract callbacks).Holds (ValuesRun callbacks) := by
  intro before args outcome _ run
  change withValuesPost callbacks before args outcome
  cases run with
  | returned left right cleanup =>
    exact ⟨_, completeString_returned _ _ _ left,
      _, completeString_returned _ _ _ right, _, cleanup, rfl⟩
  | cleanupUnwound left right cleanup =>
    exact ⟨_, completeString_returned _ _ _ left,
      _, completeString_returned _ _ _ right, _, cleanup, rfl⟩
  | cleanupTerminated left right cleanup =>
    exact ⟨_, completeString_returned _ _ _ left,
      _, completeString_returned _ _ _ right, _, cleanup, rfl⟩
  | leftUnwound left cleanup =>
    exact ⟨_, completeString_unwound left cleanup, rfl⟩
  | leftCleanupTerminated left cleanup =>
    exact ⟨_, completeString_cleanupTerminated left cleanup, rfl⟩
  | leftTerminated left =>
    exact ⟨_, completeString_terminated _ _ _ left, rfl⟩
  | rightUnwound left right cleanup =>
    exact ⟨_, completeString_returned _ _ _ left,
      _, completeString_unwound right cleanup, rfl⟩
  | rightCleanupTerminated left right cleanup =>
    exact ⟨_, completeString_returned _ _ _ left,
      _, completeString_cleanupTerminated right cleanup, rfl⟩
  | rightTerminated left right =>
    exact ⟨_, completeString_returned _ _ _ left,
      _, completeString_terminated _ _ _ right, rfl⟩

end Solanalib.Specs.Core.AnchorError
