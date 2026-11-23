/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedPdaAdmission
public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessProviders

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.TokenAllocatedPdaAdmission

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.OnchainAllocated

abbrev State := Witness.State

/-- This actual source input keeps duplicate and empty seeds in order. -/
def inputs : Address.Syscall.PdaInputs := ⟨[[], [9], [9]], .ofNat 2⟩

theorem inputs_bounded : inputs.Bounded := by
  constructor
  · decide
  · intro seed member
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide

theorem exact_request : Address.Syscall.pdaRequest inputs =
    ⟨[[], [9], [9]], 3, .ofNat 2, none, 255⟩ := rfl

/-- The finite effect of the syscall is retained even by this malformed reply. -/
def changed (before : State) : State :=
  (before.1, { before.2 with invocations := before.2.invocations + 7 })

def badTypes : Types :=
  { Witness.sampleTypes with
    pdaSyscall := Callback.ofFunction fun before _ =>
      .returned ⟨0, none, 3⟩ (changed before) }

/-- A status-zero reply without an address has a real primitive exit and
fails admission before the raw decoder can lose its continuation. -/
theorem uninitialized_success_rejected :
    badTypes.pdaSyscall Witness.initialState (Address.Syscall.pdaRequest inputs)
      (.returned ⟨0, none, 3⟩ (changed Witness.initialState)) ∧
    ¬ PdaAdmission.Ready badTypes := by
  refine ⟨rfl, ?_⟩
  intro ready
  obtain ⟨address, impossible⟩ := ready Witness.initialState inputs inputs_bounded
    ⟨0, none, 3⟩ (changed Witness.initialState) rfl rfl
  cases impossible

/-- Raw partiality stays visible; the new gate does not manufacture an
address, fallback None result, panic, or finite complete-wrapper outcome. -/
theorem uninitialized_success_has_no_find_exit : ∀ outcome,
    ¬ badTypes.findPda Witness.initialState inputs outcome := by
  rintro outcome ⟨_, tried, ⟨produced, called, decoded⟩, _⟩
  change .returned ⟨0, none, 3⟩ (changed Witness.initialState) = produced at called
  cases called
  obtain ⟨result, ⟨address, impossible, _⟩, _⟩ := decoded
  cases impossible

/-- All four primitive exits belong to one provider. The returned and
unwound states are arbitrary; this gate introduces no unrelated state frame. -/
def effectTypes (returned unwound panicAfter : State) : Types :=
  { Witness.sampleTypes with
    pdaSyscall := fun _ _ outcome =>
      outcome = .returned ⟨0, some (.ofNat 23), 17⟩ returned ∨
      outcome = .returned ⟨13, none, 3⟩ returned ∨
      outcome = .unwound (77 : Nat) unwound ∨ outcome = .terminated (91 : Nat)
    raise := fun before site outcome => before = returned ∧ site = .noViableProgramAddress ∧
      (outcome = .unwound (51 : Nat) panicAfter ∨ outcome = .terminated (52 : Nat)) }

theorem effect_types_ready (returned unwound panicAfter : State) :
    PdaAdmission.Ready (effectTypes returned unwound panicAfter) := by
  intro before request bounded reply after called zero
  rcases called with returned | rejected | unwind | terminal
  · cases returned
    exact ⟨.ofNat 23, rfl⟩
  · cases rejected
    exact False.elim ((by decide : (13 : UInt64) ≠ 0) zero)
  · cases unwind
  · cases terminal

/-- Admission derives the real wrapper success at the arbitrary
returned state of the primitive, with its exact key and bump. -/
theorem effectful_success (before returned unwound panicAfter : State) :
    (effectTypes returned unwound panicAfter).findPda before inputs
      (.returned (.ofNat 23, 17) returned) := by
  obtain ⟨address, initialized, retained⟩ :=
    (effect_types_ready returned unwound panicAfter).success_retain inputs_bounded
      (show (effectTypes returned unwound panicAfter).pdaSyscall before
        (Address.Syscall.pdaRequest inputs)
        (.returned ⟨0, some (.ofNat 23), 17⟩ returned) from Or.inl rfl) rfl
  cases initialized
  exact retained

/-- The uninitialized address and changed bump in a failure reply are not read.
Every actual panic alternative survives from the current state of the syscall. -/
theorem each_panic_exit_continues (before returned unwound panicAfter : State)
    {produced : Outcome State Empty Nat Nat}
    (raised : (effectTypes returned unwound panicAfter).raise returned .noViableProgramAddress
      produced) :
    (effectTypes returned unwound panicAfter).findPda before inputs
      (Outcome.map (fun impossible : Empty => nomatch impossible) produced) :=
  PdaAdmission.nonzero_retain inputs_bounded
    (show (effectTypes returned unwound panicAfter).pdaSyscall before
      (Address.Syscall.pdaRequest inputs) (.returned ⟨13, none, 3⟩ returned) from Or.inr (Or.inl
        rfl))
    (by decide : (13 : UInt64) ≠ 0) raised

/-- Both downstream panic forms have concrete finite exits; the unwind uses
the arbitrary new state of the panic callback and the terminal supplies no state. -/
theorem effectful_panic_alternatives (before returned unwound panicAfter : State) :
    (effectTypes returned unwound panicAfter).findPda before inputs (.unwound (51 : Nat)
      panicAfter) ∧
    (effectTypes returned unwound panicAfter).findPda before inputs (.terminated (52 : Nat)) := by
  constructor
  · exact each_panic_exit_continues before returned unwound panicAfter
      (show (effectTypes returned unwound panicAfter).raise returned .noViableProgramAddress
        (.unwound (51 : Nat) panicAfter) from ⟨rfl, rfl, Or.inl rfl⟩)
  · exact each_panic_exit_continues before returned unwound panicAfter
      (show (effectTypes returned unwound panicAfter).raise returned .noViableProgramAddress
        (.terminated (52 : Nat)) from ⟨rfl, rfl, Or.inr rfl⟩)

/-- Independent syscall unwind and terminal exits are forwarded directly,
with neither initialization nor an invented local panic execution. -/
theorem direct_syscall_alternatives (before returned unwound panicAfter : State) :
    (effectTypes returned unwound panicAfter).findPda before inputs (.unwound (77 : Nat) unwound) ∧
    (effectTypes returned unwound panicAfter).findPda before inputs (.terminated (91 : Nat)) := by
  constructor
  · exact PdaAdmission.unwind_retain inputs_bounded
      (show (effectTypes returned unwound panicAfter).pdaSyscall before
        (Address.Syscall.pdaRequest inputs) (.unwound (77 : Nat) unwound) from Or.inr (Or.inr
          (Or.inl rfl)))
  · exact PdaAdmission.terminal_retain inputs_bounded
      (show (effectTypes returned unwound panicAfter).pdaSyscall before
        (Address.Syscall.pdaRequest inputs) (.terminated (91 : Nat)) from Or.inr (Or.inr (Or.inr
          rfl)))

end SolanalibTest.Specs.Core.TokenAllocatedPdaAdmission
