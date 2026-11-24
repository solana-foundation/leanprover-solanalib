/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorConstruct
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorEffects

/-- The `?` operator in the SDK preserves an owned error identity on an ordinary error and
continues only after success, using the actual state of that return. -/
def resultBind {State Args Error First Last Unwind Terminal : Type}
    (first : Callback.Run State Args (Except Error First) Unwind Terminal)
    (next : First → State → Outcome State (Except Error Last) Unwind Terminal → Prop) :
    Callback.Run State Args (Except Error Last) Unwind Terminal :=
  Callback.bind first fun result after outcome => match result with
    | .error error => outcome = .returned (.error error) after
    | .ok value => next value after outcome

/-- A one-resource unwind protector cannot turn an unwinding or terminal
body into a normal return, regardless of its destructor outcomes. -/
theorem protected_returned {State Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drop : Owned.DropAction State Unwind Terminal)
    {pending : Outcome State Value Unwind Terminal} {value : Value} {after : State}
    (finished : Owned.onUnwind double [drop] pending (.returned value after)) :
    pending = .returned value after := by
  cases pending with
  | returned result state => exact finished.symm
  | unwound reason state =>
    obtain ⟨dropped, _, next⟩ := finished
    cases dropped with
    | returned _ _ => cases next
    | unwound _ _ => obtain ⟨_, _, impossible⟩ := next; cases impossible
    | terminated _ => cases next
  | terminated _ => cases finished

/-- A finite callback exit while an SDK local owns a data guard must preserve
that lease and the protected data. Captured auxiliary state and other cells may
change. A terminal exit has no state on which to impose a frame. -/
def guardFrame {Aux Value Unwind Terminal : Type}
    (before : AnchorAccount.World Aux) (guard : Borrow.Guard)
    (outcome : Outcome (AnchorAccount.World Aux) Value Unwind Terminal) : Prop :=
  AccountInfo.GuardCallback.Frame before guard outcome

/-- Run a dependency under the held local guard and release it after either
normal return or unwind. This raw relation does not filter by the frame; the
source caller requires universal admission before invoking it. Cleanup uses
the actual state of the callback. This wrapper is not used when `Ref::map` transfers
the lease into the returned value. -/
def withGuard {Aux Args Value Unwind Terminal : Type}
    (guard : Borrow.Guard)
    (run : Callback.Run (AnchorAccount.World Aux) Args Value Unwind Terminal) :
    Callback.Run (AnchorAccount.World Aux) Args Value Unwind Terminal :=
  AccountInfo.GuardCallback.withGuard guard run

/-- A source-local release cannot call user code or unwind. A malformed lease
has no modeled execution, rather than fabricating a successful destructor. -/
def releaseGuard {Aux Terminal : Type} (guard : Borrow.Guard) :
    Owned.DropAction (AnchorAccount.World Aux) Empty Terminal :=
  fun before outcome => match Borrow.release before.1 guard with
    | (.ok (), after) => outcome = .returned () (after, before.2)
    | (.error _, _) => False

/-- Framing and release retain the effects outside the protected cell. This
is an observation about the actual released state, not rollback. -/
theorem releaseGuard_aux {Aux Terminal : Type} (guard : Borrow.Guard)
    {before after : AnchorAccount.World Aux}
    (run : releaseGuard (Terminal := Terminal) guard before (.returned () after)) :
    after.2 = before.2 := by
  unfold releaseGuard at run
  split at run
  next _ state => cases run; rfl
  next => contradiction

/-- A terminal dependency outcome passes through local-guard cleanup without
inventing a post-state or a guard-release event. -/
theorem withGuard_terminal {Aux Args Value Unwind Terminal : Type}
    (guard : Borrow.Guard)
    (run : Callback.Run (AnchorAccount.World Aux) Args Value Unwind Terminal)
    (before : AnchorAccount.World Aux) (args : Args) (reason : Terminal)
    (step : run before args (.terminated reason)) :
    withGuard guard run before args (.terminated reason) := by
  exact ⟨.terminated reason, step, rfl⟩

end Solanalib.Specs.Core.AnchorEffects
