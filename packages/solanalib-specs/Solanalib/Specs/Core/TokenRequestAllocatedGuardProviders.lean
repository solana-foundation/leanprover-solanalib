/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedGuardPrimitives
public import Solanalib.Specs.Core.TokenRequestAllocatedGuardScope
public import Solanalib.Specs.Core.OwnedFocus

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedGuard

open AccountInfo.GuardCallback

/-- A dependency focused into auxiliary storage retains every account guard,
even when the dependency itself has effects, unwinds or terminates. -/
theorem Preserves.focus {Extra Inner Args Value Unwind Terminal : Type}
    (part : Owned.Focus (World Extra) Inner)
    (outside : ∀ before inner, (part.set before inner).1 = before.1)
    (run : Callback.Run Inner Args Value Unwind Terminal) : Preserves (part.lift run) := by
  apply Preserves.of_accounts
  rintro before _ _ ⟨produced, _, rfl⟩
  cases produced with
  | returned _ _ => exact outside _ _
  | unwound _ _ => exact outside _ _
  | terminated _ => trivial

/-- The focused vector provider has primitive guard frames regardless of the progress of its
allocator or storage relation. No resource laws are inferred here. -/
theorem VectorFrames.focus {Extra Inner Element Resource Unwind Terminal : Type}
    (ops : Owned.VectorOps Inner Element Resource Unwind Terminal)
    (part : Owned.Focus (World Extra) Inner)
    (outside : ∀ before inner, (part.set before inner).1 = before.1) :
    PlainVectorFrames (ops.focus part) where
  empty := by
    intro before valid guard _ _
    change StateFrame before.1 (part.set before (ops.empty (part.get before)).2).1 guard
    rw [outside]
    exact StateFrame.refl _ _ valid
  capacity := Preserves.focus part outside ops.withCapacity
  fromList := Preserves.focus part outside ops.fromList
  push := Preserves.focus part outside ops.push
  extend := Preserves.focus part outside ops.extend
  drop := Preserves.focus part outside ops.drop

/-- Lifting an Empty-unwind dependency changes only the outcome vocabulary. -/
theorem Preserves.rcLift {Extra Args Value Unwind Terminal : Type}
    {run : Callback.Run (World Extra) Args Value Empty Terminal} (law : Preserves run) :
    Preserves (AccountInfoRc.lift (Unwind := Unwind) run) := by
  intro before args valid guard slot live absent outcome called
  obtain ⟨produced, actual, same⟩ := called
  have frame := law before args valid guard slot live absent produced actual
  cases produced with
  | returned _ _ => cases same; exact frame
  | unwound impossible _ => exact nomatch impossible
  | terminated _ => cases same; trivial

/-- Derived AccountInfo cloning consumes the separate lamports/data Rc laws
at the real sequential call inputs, before any later source observation. -/
theorem rc_clone_preserves {Extra Terminal : Type}
    {ops : AccountInfoRc.Ops (World Extra) Terminal} (law : Preserves ops.cloneRc) :
    Preserves (AccountInfoRc.cloneCall ops) := by
  intro before info valid guard slot live absent
  have first := law before (.lamports, info.lamports) valid guard slot live absent
  apply first.bind
  intro _ after called
  have frame : StateFrame before.1 after.1 guard := first _ called
  exact (law after (.data, info.data) frame.valid guard slot (frame.resolve live) absent).map
    (fun _ => AccountInfo.clone info)

/-- Derived AccountInfo destruction preserves live caller-held guards through
both actual Rc field drops; it neither supplies nor assumes their return. -/
theorem rc_drop_preserves {Extra Terminal : Type}
    {ops : AccountInfoRc.Ops (World Extra) Terminal} (law : Preserves ops.dropRc) :
    Preserves (AccountInfoRc.dropCall ops) := by
  intro before info valid guard slot live absent
  have first := law before (.lamports, info.lamports) valid guard slot live absent
  apply first.bind
  intro _ after called
  have frame : StateFrame before.1 after.1 guard := first _ called
  exact law after (.data, info.data) frame.valid guard slot (frame.resolve live) absent

/-- Embedding the successful value returned by a primitive in Ok keeps its exact frame. -/
theorem perform_preserves {Extra Value Unwind Terminal : Type}
    {call : World Extra → Outcome (World Extra) Value Unwind Terminal → Prop}
    (law : Preserves (fun state (_ : Unit) => call state)) :
    Preserves (fun state (_ : Unit) => AllocatedControl.perform call state) :=
  law.map Except.ok

/-- Inspection changes no state. Its readiness is a separate current-value
obligation; this lemma does not manufacture an absent observation. -/
theorem inspect_preserves {Extra Value Unwind Terminal : Type}
    (observe : World Extra → Option Value) :
    Preserves (fun state (_ : Unit) =>
      AllocatedControl.inspect (Unwind := Unwind) (Terminal := Terminal) observe state) := by
  apply Preserves.of_accounts
  rintro _ _ _ ⟨_, _, rfl⟩
  rfl

/-- Pure result/error exits preserve the borrow store. -/
theorem result_preserves {Extra Value Unwind Terminal : Type} (value : Except Error Value) :
    Preserves (fun state (_ : Unit) =>
      AllocatedControl.result (State := World Extra) (Unwind := Unwind)
        (Terminal := Terminal) value state) := by
  apply Preserves.of_accounts
  intro _ _ _ same
  cases same
  rfl

/-- Result-aware bind consumes the first admission even if a dependent
continuation later lacks an outcome. Ordinary errors do not run that continuation. -/
theorem bind_preserves {Extra Value Next Unwind Terminal : Type}
    {first : AllocatedControl.Run (World Extra) Value Unwind Terminal}
    {next : Value → AllocatedControl.Run (World Extra) Next Unwind Terminal}
    (firstLaw : Preserves (fun state (_ : Unit) => first state))
    (nextLaw : ∀ value, Preserves (fun state (_ : Unit) => next value state)) :
    Preserves (fun state (_ : Unit) => AllocatedControl.bind first next state) := by
  intro before _ valid guard slot live absent outcome execution
  obtain ⟨pending, called, continued⟩ := execution
  have frame := firstLaw before () valid guard slot live absent pending called
  cases pending with
  | returned value after =>
    cases value with
    | ok actual =>
      exact Frame.prepend frame
        (nextLaw actual after () frame.valid guard slot (frame.resolve live) absent outcome
          continued)
    | error _ => cases continued; exact frame
  | unwound _ _ => cases continued; exact frame
  | terminated _ => cases continued; trivial

/-- A scope whose drops own no data guard composes actual body and destructor
frames. The body frame is derived compositionally from its primitive laws. -/
theorem scope_preserves {Extra Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind (World Extra) Unwind Terminal)
    {drops : List (Owned.DropAction (World Extra) Unwind Terminal)}
    {body : AllocatedControl.Run (World Extra) Value Unwind Terminal}
    (bodyLaw : Preserves (fun state (_ : Unit) => body state))
    (dropLaws : ∀ action ∈ drops, Preserves (fun state (_ : Unit) => action state)) :
    Preserves (fun state (_ : Unit) => AllocatedControl.scope double drops body state) := by
  intro before _ valid guard slot live absent outcome execution
  obtain ⟨pending, called, cleaned⟩ := execution
  apply cleanup_frame live double drops
  · intro action member state currentValid currentSlot currentLive
    exact dropLaws action member state () currentValid guard currentSlot currentLive absent
  · exact bodyLaw before () valid guard slot live absent pending called
  · exact cleaned

end Solanalib.Specs.Core.Token.AllocatedGuard
