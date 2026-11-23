/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.error
public import Init.Data.String.Lemmas.Intercalate

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.Error

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AnchorError
open Solanalib.Specs.AnchorLang.error.Error

abbrev ErrorValue := Solanalib.Specs.AnchorLang.error.Error

def anchor : AnchorValue :=
  ⟨"ConstraintRaw", 2003, "A raw constraint was violated",
    some (.source ⟨"account.rs", 42⟩), some (.values "old left" "old right")⟩

def program : ProgramValue ProgramError.Value :=
  ⟨.accountBorrowFailed, some (.accountName "vault"), some (.pubkeys .zero (.ofNat 1))⟩

/-- A client composes two contracts without unfolding either implementation. -/
theorem from_then_pubkeys {State : Type}
    (wrap : State → AnchorValue → ErrorValue × State)
    (put : State → AnchorError.PubkeysArgs ProgramError.Value → ErrorValue × State)
    (wrapContract : (from_anchor_error_observation_contract State).RealizedBy wrap)
    (putContract : (with_pubkeys_observation_contract State).RealizedBy put)
    (before : State) (payload : AnchorValue) (left right : _root_.Solanalib.Runtime.Pubkey) :
    (put (wrap before payload).2 ⟨(wrap before payload).1, left, right⟩).1 =
        .anchor { payload with compared := some (.pubkeys left right) } ∧
      (put (wrap before payload).2 ⟨(wrap before payload).1, left, right⟩).2 = before := by
  have wrapped := wrapContract before payload trivial
  have changed := putContract (wrap before payload).2
    ⟨(wrap before payload).1, left, right⟩ trivial
  change (wrap before payload).2 = before ∧
    (wrap before payload).1 = .anchor payload at wrapped
  change (put _ _).2 = (wrap before payload).2 ∧
    (put _ _).1 = ((wrap before payload).1).replaceCompared (.pubkeys left right) at changed
  constructor
  · rw [changed.2, wrapped.2]
    rfl
  · exact changed.1.trans wrapped.1

/-- Program error identity and account-name origin survive enrichment. -/
theorem program_pubkeys_preserves_payload :
    withPubkeysReference (State := Unit) ()
        ⟨.program program, .ofNat 7, .ofNat 8⟩ =
      (.program { program with compared := some (.pubkeys (.ofNat 7) (.ofNat 8)) }, ()) := rfl

/-- Repeated enrichment replaces the previous comparison rather than accumulating it. -/
theorem replacement_keeps_last_comparison :
    ((Value.anchor anchor : ErrorValue).replaceCompared (.values "x" "y")).replaceCompared
        (.pubkeys (.ofNat 3) (.ofNat 4)) =
      .anchor { anchor with compared := some (.pubkeys (.ofNat 3) (.ofNat 4)) } := rfl

abbrev Trace := List String

def args : ValuesArgs ProgramError.Value Unit Unit := ⟨.anchor anchor, (), ()⟩

/-- The right conversion observes the state written by the left conversion. -/
def traced : ValuesCallbacks Trace ProgramError.Value Unit Unit String String where
  left := Callback.ofFunction (fun before _ => .returned "left value" (before ++ ["left"]))
  right := Callback.ofFunction (fun before _ =>
    .returned (String.intercalate ":" before) (before ++ ["right"]))
  normalCleanup := Callback.ofFunction (fun before _ =>
    .returned () (before ++ ["normal cleanup"]))
  unwindCleanup := Callback.ofFunction (fun before request =>
    .returned () (before ++ [if request.leftText.isSome then
      "cleanup with first string" else "cleanup before first return"]))

def successResult : ErrorValue :=
  .anchor { anchor with compared := some (.values "left value" "entry:left") }

theorem conversions_and_cleanup_run_in_order :
    ValuesRun traced ["entry"] args
      (.returned successResult ["entry", "left", "right", "normal cleanup"]) := by
  apply ValuesRun.returned (leftText := "left value") (rightText := "entry:left")
    (middle := ["entry", "left"]) (actual := ["entry", "left", "right"]) rfl ?_ rfl
  change Outcome.returned (String.intercalate ":" ["entry", "left"])
      ["entry", "left", "right"] = _
  rw [String.intercalate_cons_cons, String.intercalate_singleton]
  rfl

theorem success_satisfies_contract :
    (withValuesContract traced).post ["entry"] args
      (.returned successResult ["entry", "left", "right", "normal cleanup"]) :=
  valuesRun_holds traced _ _ _ trivial conversions_and_cleanup_run_in_order

/-- The general returned-exit rule preserves all non-comparison error fields. -/
theorem returned_error_preserves_origin
    {State Left Right Unwind Terminal : Type}
    (callbacks : ValuesCallbacks State ProgramError.Value Left Right Unwind Terminal)
    {before after : State} {input : ValuesArgs ProgramError.Value Left Right}
    {result : ErrorValue}
    (post : (withValuesContract callbacks).post before input (.returned result after)) :
    result.origin = input.error.origin := by
  obtain ⟨_, _, _, _, _, _, _, resultEq⟩ :=
    (withValuesPost_returned_iff callbacks before input result after).mp post
  rw [resultEq, Value.replaceCompared_origin]

def firstPanic : ValuesCallbacks Trace ProgramError.Value Unit Unit String String :=
  { traced with
    left := Callback.ofFunction (fun before _ =>
      .unwound "left panic" (before ++ ["left write"]))
    right := fun _ _ _ => False
    normalCleanup := fun _ _ _ => False }

/-- Even an impossible right callback is harmless after the first panic.
The write before the panic and the subsequent cleanup write both remain. -/
theorem first_panic_skips_right_and_retains_effects :
    ValuesRun firstPanic ["entry"] args
      (.unwound "left panic" ["entry", "left write", "cleanup before first return"]) :=
  .leftUnwound rfl rfl

theorem first_panic_cannot_return (result : ErrorValue) (after : Trace) :
    ¬ (withValuesContract firstPanic).post ["entry"] args (.returned result after) := by
  intro post
  obtain ⟨_, _, _, _, left, _, _, _⟩ :=
    (withValuesPost_returned_iff firstPanic _ _ _ _).mp post
  simp [firstPanic, Callback.ofFunction] at left

theorem first_panic_cannot_rollback :
    ¬ (withValuesContract firstPanic).post ["entry"] args
      (.unwound "left panic" ["entry"]) := by
  simp [withValuesContract, withValuesPost, completeString, Callback.bind,
    Callback.ofFunction, firstPanic, traced]

def secondPanic : ValuesCallbacks Trace ProgramError.Value Unit Unit String String :=
  { traced with
    right := Callback.ofFunction (fun before _ =>
      .unwound "right panic" (before ++ ["right write"]))
    normalCleanup := fun _ _ _ => False }

/-- A panic in the second conversion cleans up the already-created first String. -/
theorem second_panic_cleans_first_string :
    ValuesRun secondPanic ["entry"] args
      (.unwound "right panic" ["entry", "left", "right write", "cleanup with first string"]) :=
  .rightUnwound rfl rfl rfl

def cleanupPanic : ValuesCallbacks Trace ProgramError.Value Unit Unit String String :=
  { traced with normalCleanup := Callback.ofFunction (fun before _ =>
      .unwound "drop panic" (before ++ ["drop write"])) }

/-- A destructor may panic after both conversions. No successful Error return is invented. -/
theorem cleanup_panic_preserves_its_effect :
    ValuesRun cleanupPanic ["entry"] args
      (.unwound "drop panic" ["entry", "left", "right", "drop write"]) :=
  .cleanupUnwound rfl rfl rfl

def doublePanic : ValuesCallbacks Trace ProgramError.Value Unit Unit String String :=
  { secondPanic with unwindCleanup := Callback.ofFunction (fun _ _ =>
      .terminated "panic during unwind cleanup") }

theorem panic_during_unwind_cleanup_is_terminal :
    ValuesRun doublePanic ["entry"] args (.terminated "panic during unwind cleanup") :=
  .rightCleanupTerminated rfl rfl rfl

def terminalFirst : ValuesCallbacks Trace ProgramError.Value Unit Unit String String where
  left := Callback.ofFunction (fun _ _ => .terminated "abort")
  right := fun _ _ _ => False
  normalCleanup := fun _ _ _ => False
  unwindCleanup := fun _ _ _ => False

/-- Immediate terminal exits require neither a second conversion nor cleanup. -/
theorem abort_skips_all_following_callbacks :
    ValuesRun terminalFirst ["entry"] args (.terminated "abort") :=
  .leftTerminated rfl

/-- Each supplied scalar conversion contributes its own text in the observed
`(usize, i32)` specialization; the complete existing diagnostic payload remains. -/
theorem scalar_sample_keeps_each_conversion :
    (with_values_observation_contract with_values_observation_sample).post ()
      ⟨.anchor anchor, (7 : UInt64), (-3 : Int32)⟩
      (.returned (.anchor { anchor with compared := some (.values
        (toString (7 : UInt64)) (toString (-3 : Int32))) }) ()) := by
  apply valuesRun_holds with_values_observation_sample.callbacks _ _ _ trivial
  exact ValuesRun.returned rfl rfl rfl

end SolanalibTest.Specs.AnchorLang.Error
