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

open AnchorAccount (World)

/-- A guard-local two-field Rc operation must preserve the held data lease at
each reached primitive, including a first return followed by divergence. -/
def RcReady {Aux Terminal : Type}
    (op : Callback.Run (World Aux) (AccountInfoRc.Field × Borrow.Handle) Unit Empty Terminal)
    (before : World Aux) (info : AccountInfo.Value) (guard : Borrow.Guard) : Prop :=
  AccountInfo.GuardCallback.Admissible guard op before (.lamports, info.lamports) ∧
    ∀ middle, op before (.lamports, info.lamports) (.returned () middle) →
      AccountInfo.GuardCallback.Admissible guard op middle (.data, info.data)

theorem dependency_admissible {base : Base} {Args Value : Type}
    {run : Callback.Run (World base.Aux) Args Value Empty base.Terminal}
    {before : World base.Aux} {args : Args} {guard : Borrow.Guard}
    (ready : AccountInfo.GuardCallback.Admissible guard run before args) :
    AccountInfo.GuardCallback.Admissible guard (dependency base run) before args := by
  rintro outcome ⟨lifted, ⟨produced, called, rfl⟩, rfl⟩
  have framed := ready produced called
  cases produced with
  | returned _ _ => exact framed
  | unwound impossible _ => nomatch impossible
  | terminated _ => trivial

/-- Both Rc primitives are framed separately, so the first remains admitted
even when the second has no finite exit. The composed operation retains every
actual exit and preserves the same live data guard. -/
theorem RcReady.clone {base : Base}
    {rc : AccountInfoRc.Ops (World base.Aux) base.Terminal}
    {before : World base.Aux} {info : AccountInfo.Value} {guard : Borrow.Guard}
    (ready : RcReady rc.cloneRc before info guard) :
    AccountInfo.GuardCallback.Admissible guard (cloneInfo base rc) before info := by
  apply dependency_admissible
  apply AccountInfo.GuardCallback.Admissible.bind ready.1
  intro _ after called
  exact (ready.2 after called).map (fun _ => AccountInfo.clone info)

theorem RcReady.drop {base : Base}
    {rc : AccountInfoRc.Ops (World base.Aux) base.Terminal}
    {before : World base.Aux} {info : AccountInfo.Value} {guard : Borrow.Guard}
    (ready : RcReady rc.dropRc before info guard) :
    AccountInfo.GuardCallback.Admissible guard
      (fun state (_ : Unit) => dropInfo base rc info state) before () := by
  apply dependency_admissible
  apply AccountInfo.GuardCallback.Admissible.bind ready.1
  intro _ after called
  exact ready.2 after called

/-- A retained resource drop runs in the state of the pending outcome. A finite
drop preserves the guard there; termination has no invented cleanup state. -/
theorem cleanup_one_frame {Aux Value Unwind Terminal : Type}
    {before : World Aux} {guard : Borrow.Guard}
    {pending final : Outcome (World Aux) Value Unwind Terminal}
    {drop : Owned.DropAction (World Aux) Unwind Terminal}
    {double : Owned.DoubleUnwind (World Aux) Unwind Terminal}
    (frame : AccountInfo.GuardCallback.Frame before guard pending)
    (ready : match pending with
      | .returned _ after | .unwound _ after =>
          AccountInfo.GuardCallback.Admissible guard (fun state (_ : Unit) => drop state) after ()
      | .terminated _ => True)
    (cleaned : Owned.cleanup double [drop] pending final) :
    AccountInfo.GuardCallback.Frame before guard final := by
  cases pending with
  | terminated reason => cases cleaned; trivial
  | returned value after =>
    obtain ⟨dropped, called, rest⟩ := cleaned
    have droppedFrame := ready dropped called
    cases dropped with
    | returned _ _ => cases rest; exact droppedFrame.prepend frame
    | unwound _ _ => cases rest; exact droppedFrame.prepend frame
    | terminated _ => cases rest; trivial
  | unwound original after =>
    obtain ⟨dropped, called, rest⟩ := cleaned
    have droppedFrame := ready dropped called
    cases dropped with
    | returned _ _ => cases rest; exact droppedFrame.prepend frame
    | unwound _ _ => obtain ⟨_, _, rfl⟩ := rest; trivial
    | terminated _ => cases rest; trivial

/-- Only Account and InterfaceAccount clone before decoding. The zero-copy path of Loader belongs to
its separate development. -/
inductive PayloadKind where
  | account
  | interfaceAccount
  deriving DecidableEq, Repr

def PayloadKind.constructor : PayloadKind → AnchorAccount.Constructor
  | .account => .account
  | .interfaceAccount => .interfaceAccount

end Solanalib.Specs.Core.AnchorLifecycle
