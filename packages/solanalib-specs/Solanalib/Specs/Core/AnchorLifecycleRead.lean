/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycle

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World ConstructorUnwind ConstructorTerminal)

/-- An infallible AccountInfo getter retains its actual RefCell panic. It does
not convert a borrow panic to an ordinary Anchor or ProgramError. -/
def observe {Aux Unwind Terminal : Type} (field : AccountInfo.Observation) :
    Callback.Run (World Aux) AccountInfo.Args Nat
      (ConstructorUnwind Unwind) (ConstructorTerminal Terminal) :=
  fun before args outcome =>
    match AccountInfo.observe field before.1 args.info with
    | (.malformed, _) => False
    | (.value value, after) => outcome = .returned value (after, before.2)
    | (.borrowFailed, after) =>
      if args.profile.aborts then outcome = .terminated (.inl .borrowFailed)
      else outcome = .unwound (.inl .borrowFailed) (after, before.2)

/-- Only the selected source read must be represented. Checked borrow failure
is admitted, along with its selected unwind/abort policy. -/
def ObserveReady {Aux : Type} (field : AccountInfo.Observation)
    (before : World Aux) (args : AccountInfo.Args) : Prop :=
  (AccountInfo.observe field before.1 args.info).1 ≠ .malformed

theorem observe_exists {Aux Unwind Terminal : Type} (field : AccountInfo.Observation)
    (before : World Aux) (args : AccountInfo.Args) (ready : ObserveReady field before args) :
    ∃ outcome, observe (Unwind := Unwind) (Terminal := Terminal) field before args outcome := by
  cases step : AccountInfo.observe field before.1 args.info with
  | mk value after =>
    cases value with
    | malformed => exact False.elim (ready (by simp only [step]))
    | value amount => exact ⟨.returned amount (after, before.2), by simp only [observe, step]⟩
    | borrowFailed =>
      cases strategy : args.profile.aborts with
      | false => exact ⟨.unwound (.inl .borrowFailed) (after, before.2),
          by simp only [observe, step, strategy, Bool.false_eq_true, ↓reduceIte]⟩
      | true => exact ⟨.terminated (.inl .borrowFailed),
          by simp only [observe, step, strategy, ↓reduceIte]⟩

/-- Anchor `is_closed`: a non-system owner short-circuits without a data
borrow. A system owner is closed exactly when the actual length getter is 0. -/
def isClosed {Aux Unwind Terminal : Type} (ownerAt : AccountInfo.OwnerAt Aux) :
    Callback.Run (World Aux) AccountInfo.Args Bool
      (ConstructorUnwind Unwind) (ConstructorTerminal Terminal) :=
  fun before args outcome =>
    if ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId then
      Callback.map (fun length => length == 0) (observe .dataLen) before args outcome
    else outcome = .returned false before

def IsClosedReady {Aux : Type} (ownerAt : AccountInfo.OwnerAt Aux)
    (before : World Aux) (args : AccountInfo.Args) : Prop :=
  ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId → ObserveReady .dataLen
    before args

/-- This local source operation has an actual finite outcome on every admitted
input, including a borrow panic. No callback totality is presumed. -/
theorem isClosed_exists {Aux Unwind Terminal : Type} (ownerAt : AccountInfo.OwnerAt Aux)
    (before : World Aux) (args : AccountInfo.Args) (ready : IsClosedReady ownerAt before args) :
    ∃ outcome, isClosed (Unwind := Unwind) (Terminal := Terminal) ownerAt before args outcome := by
  by_cases system : ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId
  · obtain ⟨produced, called⟩ := observe_exists (Unwind := Unwind) (Terminal := Terminal)
      .dataLen before args (ready system)
    exact ⟨Outcome.map (fun length => length == 0) produced,
      by simp only [isClosed, system, ↓reduceIte]; exact ⟨produced, called, rfl⟩⟩
  · exact ⟨.returned false before, by simp only [isClosed, system, ↓reduceIte]⟩

/-- A serializer receives a mutable byte slice, so it can change bytes but not
the slice length or the type of its lamports cell. Shared views remain unchanged. -/
def mutableDataFootprint : Borrow.Footprint AccountInfo.Content AccountInfo.View :=
  fun mode _ old next =>
    match mode, old, next with
    | .exclusive, .data before, .data after => after.length = before.length
    | _, _, _ => next = old

def MutableFrame {Aux Value Unwind Terminal : Type}
    (before : World Aux) (guard : Borrow.Guard)
    (produced : Outcome (World Aux) Value Unwind Terminal) : Prop :=
  match produced with
  | .returned _ after | .unwound _ after =>
    Borrow.CallbackFrame mutableDataFootprint before.1 after.1 guard
  | .terminated _ => True

def MutableAdmissible {Aux Args Value Unwind Terminal : Type}
    (guard : Borrow.Guard) (run : Callback.Run (World Aux) Args Value Unwind Terminal)
    (before : World Aux) (args : Args) : Prop :=
  ∀ produced, run before args produced → MutableFrame before guard produced

/-- The held-token law of the mutable callback supplies real checked cleanup on
return and unwind. All written bytes and auxiliary effects remain afterward. -/
theorem MutableFrame.release_exists {Aux Value Unwind Terminal : Type}
    {before : World Aux} {guard : Borrow.Guard} {slot : Borrow.Slot AccountInfo.View}
    {produced : Outcome (World Aux) Value Unwind Terminal}
    (live : before.1.resolve guard = some slot) (frame : MutableFrame before guard produced) :
    ∃ outcome, AnchorAccount.releaseOutcome guard produced = some outcome := by
  cases produced with
  | terminated reason => exact ⟨.terminated reason, rfl⟩
  | returned value after =>
    have held : after.1.resolve guard = some slot := frame.held.trans live
    exact ⟨.returned value ((Borrow.release after.1 guard).2, after.2), by
      simp only [AnchorAccount.releaseOutcome, AccountInfo.GuardCallback.releaseOutcome,
        Borrow.release_live held]⟩
  | unwound reason after =>
    have held : after.1.resolve guard = some slot := frame.held.trans live
    exact ⟨.unwound reason ((Borrow.release after.1 guard).2, after.2), by
      simp only [AnchorAccount.releaseOutcome, AccountInfo.GuardCallback.releaseOutcome,
        Borrow.release_live held]⟩

/-- Every actual admitted serializer exit extends through the guard
scope of the wrapper. This theorem retains ordinary errors and partial writes on unwind. -/
theorem MutableAdmissible.retain {Aux Args Value Unwind Terminal : Type}
    {before : World Aux} {args : Args} {guard : Borrow.Guard} {slot : Borrow.Slot AccountInfo.View}
    {run : Callback.Run (World Aux) Args Value Unwind Terminal}
    (live : before.1.resolve guard = some slot)
    (admitted : MutableAdmissible guard run before args)
    {produced : Outcome (World Aux) Value Unwind Terminal} (called : run before args produced) :
    ∃ outcome, AnchorAccount.releaseOutcome guard produced = some outcome ∧
      AnchorEffects.withGuard guard run before args outcome := by
  obtain ⟨outcome, released⟩ := (admitted produced called).release_exists live
  exact ⟨outcome, released, produced, called, released⟩

end Solanalib.Specs.Core.AnchorLifecycle
