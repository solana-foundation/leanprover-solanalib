/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedSeedsTypes

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedSeeds

universe u v w

/-- Optional pure-value correspondence for ordinary returns of the address
dependency. It neither supplies a return nor suppresses any unwind, terminal
exit, state mutation, syscall admission failure or metering failure. -/
def NormalFindAgreement {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (find : FindPda State Unwind Terminal) (crypto : Address.Crypto) : Prop :=
  ∀ before inputs value after, find before inputs (.returned value after) →
    Address.tryFind ⟨crypto, inputs.seeds, inputs.programId⟩ = some value

/-- The selected address-library model satisfies the optional observation law
under its primitive normal-reply agreement. Its complete finite outcomes stay
in `Address.Syscall.findRun`, independently of that agreement. -/
theorem findRun_normal_agreement {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State Address.Syscall.PdaRequest Address.Syscall.PdaReply Unwind
      Terminal)
    (panic : Callback.Run State Address.SearchPanic Empty Unwind Terminal)
    (crypto : Address.Crypto) (agreement : Address.Syscall.NormalPdaAgreement syscall crypto) :
    NormalFindAgreement (Address.Syscall.findRun syscall panic) crypto := by
  intro before inputs value after execution
  exact Address.Syscall.findRun_returned_projection syscall panic crypto agreement
    before after inputs value execution

/-- A supporting mathematical provider, not the primary selected-syscall
interpretation. It uses pure search and calls the supplied Empty-valued panic
only on mathematical exhaustion. The primary resolver accepts a general
stateful `FindPda`, including `Address.Syscall.findRun`. -/
def pureFind {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (crypto : Address.Crypto) (panic : Callback.Run State Unit Empty Unwind Terminal) :
    FindPda State Unwind Terminal :=
  fun before inputs outcome =>
    match Address.tryFind ⟨crypto, inputs.seeds, inputs.programId⟩ with
    | some value => outcome = .returned value before
    | none => Callback.map (fun impossible : Empty => nomatch impossible) panic before () outcome

/-- The mathematical reference has the exact pure-return observation; this
does not prove it represents every exit of a concrete syscall provider. -/
theorem pureFind_normal_agreement {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (crypto : Address.Crypto) (panic : Callback.Run State Unit Empty Unwind Terminal) :
    NormalFindAgreement (pureFind crypto panic) crypto := by
  intro before inputs value after execution
  unfold pureFind at execution
  cases answer : Address.tryFind ⟨crypto, inputs.seeds, inputs.programId⟩ with
  | some actual =>
    rw [answer] at execution
    cases execution
    rfl
  | none =>
    rw [answer] at execution
    obtain ⟨actual, called, mapped⟩ := execution
    cases actual with
    | returned impossible _ => exact nomatch impossible
    | unwound _ _ => cases mapped
    | terminated _ => cases mapped

end Solanalib.Specs.Core.Token.AllocatedSeeds
