/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessProviders
public import Solanalib.Specs.Core.TokenRequestAllocatedGuardProviders

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.Witness

open AllocatedGuard AccountInfo.GuardCallback

/-- The vector-only partial providers of the sample frame the account store on
every primitive exit, rather than relying on their unused source branches. -/
theorem emptyOnly_frames {Element : Type}
    (part : Owned.Focus State (Owned.VectorState Unit))
    (outside : ∀ before inner, (part.set before inner).1 = before.1) :
    PlainVectorFrames (emptyOnlyOps (Element := Element) part) := by
  have units := VectorFrames.focus
    (Owned.vectorReference (Element := Unit) (Unwind := Nat) (Terminal := Nat)) part outside
  refine ⟨units.empty, units.capacity, ?_, Preserves.empty, ?_, units.drop⟩
  · intro before values valid guard slot live absent outcome called
    exact units.capacity before 0 valid guard slot live absent outcome called.2
  · apply Preserves.of_accounts
    rintro before ⟨resource, values⟩ outcome ⟨_, _, same⟩
    cases same
    rfl

/-- Both concrete Rc operations retain account bytes and lease identities
while changing their actual auxiliary owner counts and ordered event trace. -/
theorem rc_frames : Preserves rcOps.cloneRc ∧ Preserves rcOps.dropRc := by
  constructor <;> apply Preserves.of_accounts
  all_goals
    rintro before ⟨field, cell⟩ outcome ⟨_, same⟩
    cases same
    rfl

/-- Every clone in a vector extension is checked at its actual sequential
state; this proof makes no complete token-operation assumption. -/
theorem cloneInfos_frames (values : List AccountInfo.Value) : Preserves (cloneInfos values) := by
  induction values with
  | nil =>
    apply Preserves.of_accounts
    intro _ _ _ same
    cases same
    rfl
  | cons value rest induction =>
    exact (rc_clone_preserves rc_frames.1).rcLift.arguments (fun (_ : Unit) => value) |>.bind
      (fun _ => induction)

/-- Current-element destruction follows actual Rc callbacks in source order. -/
theorem dropInfos_frames (values : List AccountInfo.Value) : Preserves (dropInfos values) := by
  induction values with
  | nil =>
    apply Preserves.of_accounts
    intro _ _ _ same
    cases same
    rfl
  | cons value rest induction =>
    exact (rc_drop_preserves rc_frames.2).rcLift.arguments (fun (_ : Unit) => value) |>.bind
      (fun _ => induction)

/-- The ordinary AccountInfo vector provider composes actual Rc effects and
current storage operations without altering a held data guard. -/
theorem infos_frames : PlainVectorFrames infosOps := by
  have storage := VectorFrames.focus
    (Owned.vectorReference (Element := AccountInfo.Value) (Unwind := Nat) (Terminal := Nat))
    infosFocus (fun _ _ => rfl)
  refine ⟨storage.empty, storage.capacity, storage.fromList, storage.push, ?_, ?_⟩
  · intro before input valid guard slot live absent outcome called
    exact ((cloneInfos_frames input.2).bind
      (fun _ => storage.extend.arguments (fun (_ : Unit) => input)))
      before () valid guard slot live absent outcome called
  · intro before resource valid guard slot live absent outcome called
    obtain ⟨values, _, run⟩ := called
    exact ((dropInfos_frames values).bind
      (fun _ => Preserves.arguments storage.drop (fun (_ : Unit) => resource)))
      before () valid guard slot live absent outcome run

/-- A local protocol for the unused collection call of the sample. Retirement
returns directly without a resource, or invokes the supplied vector drop. -/
def sampleGuardProtocol : AllocatedCollect.Protocol Extra Nat Nat Nat where
  internal := fun _ _ _ _ => False
  finish := fun _ _ _ => False
  retire := fun resource _ before outcome => match resource with
    | none => outcome = .returned () before
    | some identity => sampleTypes.guards.drop before identity outcome
  double := sampleTypes.doubleUnwind

end Solanalib.Specs.Core.Token.OnchainAllocated.Witness
